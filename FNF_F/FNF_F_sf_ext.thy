           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               January 2006                |
            |                 March 2007  (modified)    |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory FNF_F_sf_ext
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

         1. full sequentialization for Ext_choice
         2. full sequentialization for Timeout
         2. 
         3. 

 *****************************************************************)

(*============================================================*
 |                                                            |
 |                        Ext_choice                          |
 |                                                            |
 *============================================================*)

definition
  Pfun_Ext_choice :: "('p,'a) proc => ('p,'a) proc => ('p,'a) proc"
  where
  Pfun_Ext_choice_def :
    "Pfun_Ext_choice == (%P1 P2. P1 [+] P2)"

definition
  SP_step_Ext_choice :: 
   "('a set => ('a => ('p,'a) proc) => ('p,'a) proc =>
     'a set => ('a => ('p,'a) proc) => ('p,'a) proc => 
    ('a => ('p,'a) proc) => ('a => ('p,'a) proc) => ('a => ('p,'a) proc)
        => ('p,'a) proc)"
  where
  SP_step_Ext_choice_def :
    "SP_step_Ext_choice == (%A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2. 

           (? a:(A1 Un A2)
               -> (if (a : A1 & a : A2)
                   then (Pf1 a) |~|seq (Pf2 a)
                   else if (a : A1)
                        then (Pf1 a) else (Pf2 a)))
           [+] (if (Q1 = STOP) then Q2
                else if (Q2 = STOP) then Q1
                else (if (Q1 = SKIP | Q2 = SKIP) then SKIP else DIV)))"

definition
  fsfF_Ext_choice  :: "('p,'a) proc => ('p,'a) proc => ('p,'a) proc"
                                    ("(1_ /[+]seq _)" [72,73] 72)
  where
  fsfF_Ext_choice_def :
    "P1 [+]seq P2 == 
       (fsfF_induct2 Pfun_Ext_choice SP_step_Ext_choice P1 P2)"

(*------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------*)

lemma fsfF_Ext_choice_in:
    "[| P1 : fsfF_proc ; P2 : fsfF_proc |]
     ==> P1 [+]seq P2 : fsfF_proc"
apply (simp add: fsfF_Ext_choice_def)
apply (rule fsfF_induct2_in)
apply (simp_all)

apply (simp_all add: SP_step_Ext_choice_def)
apply (rule fsfF_proc_ext)
apply (intro ballI)
apply (simp split: if_split)
apply (intro impI conjI)
apply (rule fsfF_Int_choice_in)
apply (simp_all)
apply (simp split: if_split)
apply (auto)
done

(*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*)

lemma cspF_fsfF_Ext_choice_eqF:
    "P1 [+] P2 =F P1 [+]seq P2"
apply (simp add: fsfF_Ext_choice_def)
apply (rule cspF_rw_right)
apply (rule cspF_fsfF_induct2_eqF[THEN cspF_sym])
apply (simp_all add: Pfun_Ext_choice_def)
apply (rule cspF_Dist_nonempty, simp)
apply (rule cspF_Dist_nonempty, simp)
apply (simp add: SP_step_Ext_choice_def)

(* commut and assoc *)
apply (rule cspF_rw_left)
apply (subgoal_tac 
  "? :A1 -> Pf1 [+] Q1 [+] (? :A2 -> Pf2 [+] Q2)
  =F (? :A1 -> Pf1 [+] ? :A2 -> Pf2) [+] (Q1 [+] Q2)")  (* sub1 *)
apply (simp)

 (* sub1 *)
 apply (rule cspF_rw_left)
 apply (rule cspF_assoc)
 apply (rule cspF_rw_left)
 apply (rule cspF_decompo)
 apply (rule cspF_assoc_sym)
 apply (rule cspF_reflex)
 apply (rule cspF_rw_left)
 apply (rule cspF_decompo)
 apply (rule cspF_decompo)
 apply (rule cspF_reflex)
 apply (rule cspF_commut)
 apply (rule cspF_reflex)
 apply (rule cspF_rw_left)
 apply (rule cspF_decompo)
 apply (rule cspF_assoc)
 apply (rule cspF_reflex)
 apply (rule cspF_rw_left)
 apply (rule cspF_assoc_sym)
 apply (rule cspF_reflex)

apply (rule cspF_decompo)

(* expand *)
apply (rule cspF_rw_left)
apply (rule cspF_step)
apply (rule cspF_decompo)
apply (simp)

(* if *)
apply (rule cspF_rw_right)
apply (rule cspF_IF_split[THEN cspF_sym])
apply (rule cspF_decompo)
apply (simp)
apply (simp add: cspF_fsfF_Int_choice_eqF)
apply (rule cspF_rw_right)
apply (rule cspF_IF_split[THEN cspF_sym])
apply (rule cspF_decompo)
apply (simp_all)

(* SKIP [+] DIV *)
apply (simp split: if_split)
apply (intro conjI impI)
apply (simp_all)
apply (rule cspF_rw_left)
apply (rule cspF_SKIP_or_DIV)
apply (simp_all)
apply (rule cspF_rw_left)
apply (rule cspF_SKIP_or_DIV)
apply (simp_all)

(* congruence *)
apply (simp add: SP_step_Ext_choice_def)
done

(*--------------------------------------------------*
 |                                                  |
 |  The equality "cspF_fsfF_Ext_choice_eqF" can be  |
 |  proven by using tactics as follows:             |
 |                                                  |
 *--------------------------------------------------*)

(*
lemma "P1 [+] P2 =F P1 [+]seq P2"
apply (simp add: fsfF_Ext_choice_def)
apply (rule cspF_rw_right)
apply (rule cspF_fsfF_induct2_eqF[THEN cspF_sym])
apply (simp_all add: Pfun_Ext_choice_def)
apply (tactic {* cspF_dist_tac 1 *})
apply (tactic {* cspF_dist_tac 1 *})
apply (simp add: SP_step_Ext_choice_def)
apply (elim disjE)
apply (simp_all)

apply ((tactic {* cspF_hsf_tac 1 *})+,
       (rule cspF_decompo), (rule), (simp),
       (simp split: if_split),
       (intro conjI allI impI),
       (tactic {* cspF_simp_tac 1 *})+,
       (rule cspF_fsfF_Int_choice_eqF),
       (tactic {* cspF_simp_tac 1 *}),
       (tactic {* cspF_simp_tac 1 *}))+

apply (simp add: SP_step_Ext_choice_def)
done
*)

(*============================================================*
 |                                                            |
 |                         Timeout                            |
 |                                                            |
 *============================================================*)

definition
  fsfF_Timeout ::
  "('p,'a) proc => ('p,'a) proc => ('p,'a) proc"  ("(1_ /[>seq _)" [73,74] 73)
  where
  fsfF_Timeout_def :
    "P1 [>seq P2 == (P1 |~|seq SSTOP) [+]seq P2"

(*------------------------------------*
 |                 in                 |
 *------------------------------------*)

lemma fsfF_Timeout_in:
  "[| P1 : fsfF_proc ; P2 : fsfF_proc |] ==> P1 [>seq P2 : fsfF_proc"
apply (simp add: fsfF_Timeout_def)
apply (rule fsfF_Ext_choice_in)
apply (rule fsfF_Int_choice_in)
apply (simp_all)
done

(*------------------------------------*
 |                 eqF                |
 *------------------------------------*)

lemma cspF_fsfF_Timeout_eqF:
  "(P1 [> P2) =F (P1 [>seq P2)"
apply (simp add: fsfF_Timeout_def)
apply (rule cspF_rw_right)
apply (rule cspF_fsfF_Ext_choice_eqF[THEN cspF_sym])
apply (rule cspF_decompo)

apply (rule cspF_rw_right)
apply (rule cspF_fsfF_Int_choice_eqF[THEN cspF_sym])
apply (rule cspF_decompo)
apply (rule cspF_reflex)
apply (rule cspF_SSTOP_eqF)
apply (rule cspF_reflex)
done

(****************** to add them again ******************)

declare if_split    [split]
declare disj_not1   [simp]

end
