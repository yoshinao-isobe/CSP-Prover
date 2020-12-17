           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory FNF_F_sf_ren
imports FNF_F_sf_induct
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

         1. full sequentialization for Renaming (P [[r]])
         2.
         3.

 *****************************************************************)

(*============================================================*
 |                                                            |
 |                    Renaming P [[r]]                        |
 |                                                            |
 *============================================================*)

definition
  Pfun_Renaming :: "('a * 'a) set => (('p,'a) proc => ('p,'a) proc)"
  where
  Pfun_Renaming_def :
    "Pfun_Renaming r == (%P1. P1 [[r]])"
 
definition
  SP_step_Renaming :: 
   "('a * 'a) set => ('a set => ('a => ('p,'a) proc) =>
    ('p,'a) proc => ('a => ('p,'a) proc) 
    => ('p,'a) proc)"
  where
  SP_step_Renaming_def :
    "SP_step_Renaming r == (%Y1 Pf1 Q1 SPf.
                  (? y:(r `` Y1) -> 
                  (! :{x : Y1. (x, y) : r} .. SPf) [+] Q1))"

definition
  fsfF_Renaming :: "('p,'a) proc => ('a * 'a) set => ('p,'a) proc" 
                                      ("(1_ /[[_]]seq)" [84,0] 84)
  where
  fsfF_Renaming_def :
    "P1 [[r]]seq == (fsfF_induct1 (Pfun_Renaming r)
                    (SP_step_Renaming r) P1)"

(*************************************************************
                     function fsfF -> fsfF
 *************************************************************)

lemma fsfF_Renaming_in:
    "P1 : fsfF_proc ==> P1 [[r]]seq : fsfF_proc"
apply (simp add: fsfF_Renaming_def)
apply (rule fsfF_induct1_in)
apply (simp_all add: SP_step_Renaming_def)
apply (rule fsfF_proc.intros)
apply (rule ballI)
apply (simp add: Rep_int_choice_ss_def)
apply (rule fsfF_proc.intros)
apply (auto)
done

(*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*)

lemma cspF_fsfF_Renaming_eqF:
    "P1 [[r]] =F P1 [[r]]seq"
apply (simp add: fsfF_Renaming_def)
apply (rule cspF_rw_right)
apply (rule cspF_fsfF_induct1_eqF[THEN cspF_sym])
apply (simp_all add: Pfun_Renaming_def
                     SP_step_Renaming_def)
apply (rule cspF_rw_left)
apply (rule cspF_Ext_dist)
apply (rule cspF_decompo)
apply (rule cspF_step)
apply (simp add: cspF_SKIP_or_DIV_or_STOP_Renaming_Id)

(* congruence *)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_decompo)
apply (auto)
done

(****************** to add them again ******************)

declare if_split    [split]
declare disj_not1   [simp]

end
