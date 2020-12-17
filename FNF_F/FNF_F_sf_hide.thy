           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               Februaru 2006               |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory FNF_F_sf_hide
imports FNF_F_sf_induct FNF_F_sf_ext
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*  The following simplification rules are deleted in this theory file *)
(*       P (if Q then x else y) = ((Q --> P x) & (~ Q --> P y))        *)
(* Isabelle 2017: split_if --> if_split *)

declare if_split  [split del]

(*****************************************************************

         1. full sequentialization for Hiding (P -- X)
         2.
         3.

 *****************************************************************)

(*============================================================*
 |                                                            |
 |                     Hiding P -- X                          |
 |                                                            |
 *============================================================*)

definition
  Pfun_Hiding :: "'a set => (('p,'a) proc => ('p,'a) proc)"
  where
  Pfun_Hiding_def :
    "Pfun_Hiding X == (%P1. P1 -- X)"
  
definition
  SP_step_Hiding :: 
   "'a set => ('a set => ('a => ('p,'a) proc) => ('p,'a) proc =>
    ('a => ('p,'a) proc) => ('p,'a) proc)"
  where
  SP_step_Hiding_def :
    "SP_step_Hiding X == (%A1 Pf1 Q1 SPf.
     (if (Q1 = STOP) 
      then if (A1 Int X = {}) 
           then ((? :A1 -> SPf) [+] Q1)
           else (((? :(A1-X) -> SPf) [+] Q1)
                 [>seq
                (! :(A1 Int X) ..seq SPf))
      else (((? :(A1-X) -> SPf) [+] Q1) |~|seq
            (! :(A1 Int X) ..seq SPf))))"

definition
  fsfF_Hiding :: "('p,'a) proc => 'a set => ('p,'a) proc"
                          ("(1_ /--seq _)" [84,85] 84)
  where
  fsfF_Hiding_def :
    "P1 --seq X == 
       (fsfF_induct1 (Pfun_Hiding X) (SP_step_Hiding X) P1)"

(*------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------*)

lemma fsfF_Hiding_in:
    "P1 : fsfF_proc ==> P1 --seq X : fsfF_proc"
apply (simp add: fsfF_Hiding_def)
apply (rule fsfF_induct1_in)
apply (simp_all add: SP_step_Hiding_def)
apply (simp split: if_split)
apply (intro conjI impI)
apply (simp_all add: fsfF_proc.intros)
apply (rule fsfF_Int_choice_in)
apply (simp_all add: fsfF_proc.intros)
apply (simp add: fsfF_Rep_int_choice_com_in)
apply (rule fsfF_Timeout_in)
apply (simp_all add: fsfF_proc.intros)
apply (simp add: fsfF_Rep_int_choice_com_in)
apply (rule fsfF_Int_choice_in)
apply (simp add: fsfF_proc.intros)
apply (simp add: fsfF_Rep_int_choice_com_in)
done

(*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*)

lemma cspF_fsfF_Hiding_eqF: "P1 -- X =F P1 --seq X"
apply (simp add: fsfF_Hiding_def)
apply (rule cspF_rw_right)
apply (rule cspF_fsfF_induct1_eqF[THEN cspF_sym])
apply (simp_all add: Pfun_Hiding_def
                     SP_step_Hiding_def)

apply (case_tac "Q1 = STOP")
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (simp)
apply (rule cspF_unit)

apply (rule cspF_rw_left)
apply (rule cspF_step)
apply (simp)

apply (simp split: if_split)
apply (intro conjI impI)
apply (rule cspF_rw_left)
apply (rule cspF_IF)
apply (rule cspF_rw_right)
apply (rule cspF_unit)
apply (rule cspF_reflex)

apply (rule cspF_rw_left)
apply (rule cspF_IF)
apply (rule cspF_rw_right)
apply (rule cspF_fsfF_Timeout_eqF[THEN cspF_sym])
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (rule cspF_rw_right)
apply (rule cspF_unit)
apply (simp)
apply (simp)

apply (rule cspF_rw_right)
apply (rule cspF_fsfF_Rep_int_choice_com_eqF[THEN cspF_sym])
apply (simp)

(* Q1 ~= STOP *)
apply (simp)

apply (rule cspF_rw_left)
apply (rule cspF_SKIP_or_DIV)
apply (simp)

apply (rule cspF_rw_right)
apply (rule cspF_fsfF_Int_choice_eqF[THEN cspF_sym])
apply (rule cspF_decompo)
apply (rule cspF_reflex)

apply (rule cspF_rw_right)
apply (rule cspF_fsfF_Rep_int_choice_com_eqF[THEN cspF_sym])
apply (rule cspF_reflex)

(* congruence *)
apply (simp split: if_split)
apply (intro conjI impI)
apply (rule cspF_rw_left,
     (simp
     | rule cspF_fsfF_Int_choice_eqF[THEN cspF_sym]
     | rule cspF_fsfF_Rep_int_choice_eqF[THEN cspF_sym]
     | rule cspF_fsfF_Rep_int_choice_com_eqF[THEN cspF_sym]
     | rule cspF_fsfF_Timeout_eqF[THEN cspF_sym]
     | rule cspF_decompo 
     | rule cspF_reflex)+ ,
       rule cspF_rw_right,
     (simp
     | rule cspF_fsfF_Int_choice_eqF[THEN cspF_sym]
     | rule cspF_fsfF_Rep_int_choice_eqF[THEN cspF_sym]
     | rule cspF_fsfF_Rep_int_choice_com_eqF[THEN cspF_sym]
     | rule cspF_fsfF_Timeout_eqF[THEN cspF_sym]
     | rule cspF_decompo 
     | rule cspF_reflex)+)+
done

(****************** to add them again ******************)

declare if_split    [split]
declare disj_not1   [simp]

end
