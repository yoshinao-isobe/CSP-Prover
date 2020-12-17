           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory FNF_F_sf_seq
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

         1. full sequentialization for Sequential composition (P1 ;; P2)
         2.
         3.

 *****************************************************************)

(*============================================================*
 |                                                            |
 |                    Seq_compo P ;; Q                        |
 |                                                            |
 *============================================================*)

definition
  Pfun_Seq_compo :: "('p,'a) proc => (('p,'a) proc => ('p,'a) proc)"
  where
  Pfun_Seq_compo_def :
    "Pfun_Seq_compo P2 == (%P1. P1 ;; P2)"
  
definition
  SP_step_Seq_compo :: 
   "('p,'a) proc => ('a set => ('a => ('p,'a) proc) => ('p,'a) proc =>
                               ('a => ('p,'a) proc) => ('p,'a) proc)"
  where
  SP_step_Seq_compo_def :
    "SP_step_Seq_compo P2 == (%Y1 Pf1 Q1 SPf.
     (if (Q1 = SKIP)
      then (((? x:Y1 -> SPf x) [+] STOP) [>seq P2)
      else if (Q1 = DIV)
      then (((? x:Y1 -> SPf x) [+] STOP) [>seq SDIV)
      else ((? x:Y1 -> SPf x) [+] STOP)))"

definition
  fsfF_Seq_compo :: "('p,'a) proc => ('p,'a) proc => ('p,'a) proc" 
                               ("(1_ /;;seq _)" [79,78] 78)
  where
  fsfF_Seq_compo_def :
    "fsfF_Seq_compo == (%P1 P2. 
       (fsfF_induct1 (Pfun_Seq_compo P2) 
                     (SP_step_Seq_compo P2) P1))"

(*************************************************************
                  function fsfF fsfF -> fsfF
 *************************************************************)

lemma fsfF_Seq_compo_in:
    "[| P1 : fsfF_proc ; P2 : fsfF_proc |]
     ==> P1 ;;seq P2 : fsfF_proc"
apply (simp add: fsfF_Seq_compo_def)
apply (rule fsfF_induct1_in)
apply (simp_all add: SP_step_Seq_compo_def)
apply (simp split: if_split)
apply (intro conjI impI)
apply (rule fsfF_Timeout_in)
apply (simp_all add: fsfF_proc.intros)
apply (rule fsfF_Timeout_in)
apply (simp_all add: fsfF_proc.intros)
done

(*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*)

lemma cspF_fsfF_Seq_compo_eqF:
    "P1 ;; P2 =F P1 ;;seq P2"
apply (simp add: fsfF_Seq_compo_def)
apply (rule cspF_rw_right)
apply (rule cspF_fsfF_induct1_eqF[THEN cspF_sym])
apply (simp_all add: Pfun_Seq_compo_def SP_step_Seq_compo_def)

apply (erule disjE)
      (* SKIP *)
apply (simp)

apply (rule cspF_rw_left)
apply (rule cspF_SKIP_DIV_Seq_compo_step_resolve)

apply (rule cspF_rw_right)
apply (rule cspF_fsfF_Timeout_eqF[THEN cspF_sym])
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (rule cspF_rw_right)
apply (rule cspF_unit)
apply (rule cspF_reflex)
apply (rule cspF_reflex)
apply (rule cspF_reflex)

apply (erule disjE)
      (* DIV *)
apply (simp)

apply (rule cspF_rw_left)
apply (rule cspF_SKIP_DIV_Seq_compo_step_resolve)

apply (rule cspF_rw_right)
apply (rule cspF_fsfF_Timeout_eqF[THEN cspF_sym])
apply (rule cspF_rw_left)
apply (rule cspF_Ext_choice_SKIP_or_DIV_resolve)
apply (simp)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (rule cspF_rw_right)
apply (rule cspF_unit)
apply (rule cspF_reflex)
apply (rule cspF_reflex)
apply (rule cspF_SDIV_eqF)

      (* STOP *)
apply (simp)

apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_unit)
apply (rule cspF_reflex)
apply (rule cspF_rw_left)
apply (rule cspF_step)

apply (rule cspF_rw_right)
apply (rule cspF_unit)
apply (rule cspF_reflex)

(* congruence *)
apply (rule cspF_rw_left,
     (simp
     | rule cspF_IF_split[THEN cspF_sym]
     | rule cspF_fsfF_Timeout_eqF[THEN cspF_sym]
     | rule cspF_decompo 
     | rule cspF_reflex)+ ,
       rule cspF_rw_right,
     (simp
     | rule cspF_IF_split[THEN cspF_sym]
     | rule cspF_fsfF_Timeout_eqF[THEN cspF_sym]
     | rule cspF_decompo 
     | rule cspF_reflex)+)+
done

(****************** to add them again ******************)

declare if_split    [split]
declare disj_not1   [simp]

end
