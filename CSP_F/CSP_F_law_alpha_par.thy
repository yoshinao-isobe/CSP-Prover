           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                    May 2005               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_law_alpha_par
imports CSP_F_op_alpha_par CSP_F_law_decompo 
        CSP_T.CSP_T_law_alpha_par
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  Union (B ` A) = (UN x:A. B x)                      *)
(*                  Inter (B ` A) = (INT x:A. B x)                     *)

(*
declare Union_image_eq [simp del]
declare Inter_image_eq [simp del]
*)

(* no simp rules in Isabelle 2017 
declare Sup_image_eq [simp del]
declare Inf_image_eq [simp del]
*)

(*****************************************************************

         1. associativity of |[X,Y]|
         2. commutativity of |[X,Y]|
         3. monotonicity of |[X,Y]|
         4. 

 *****************************************************************)

(*********************************************************
                        P |[X,Y]| Q
 *********************************************************)

(************************************
 |         SKIP and SKIP            |
 ************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_SKIP_Alpha_parallel:
  "(SKIP |[{}, {}]| SKIP) =F[M1,M2] SKIP"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_SKIP_Alpha_parallel)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures_Alpha_parallel)
 apply (elim conjE exE)

 apply (simp add: in_failures)
 apply (elim disjE)
 apply (simp_all)
 apply (simp add: Evset_def)
 apply (subgoal_tac "(s = <> | s = <Tick>)")
 apply (erule disjE)
 apply (simp)
 apply (fast)
 apply (simp)
 apply (simp add: sett_subset_Tick)

 apply (subgoal_tac "(s = <> | s = <Tick>)")
 apply (erule disjE)
 apply (simp)
 apply (simp)
 apply (simp add: sett_subset_Tick)

(* <= *)
 apply (rule)
 apply (simp add: in_failures_Alpha_parallel)
 apply (rule_tac x="X" in exI)
 apply (rule_tac x="X" in exI)
 apply (simp)

 apply (simp add: in_failures)
 apply (auto)
done

(************************************
 |          associativity           |
 ************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Alpha_parallel_ass_lm1:
          "Ya Int insert Tick (Ev ` X1) Un
          (Za Int insert Tick (Ev ` X2) Un Z Int insert Tick (Ev ` X3)) =
           Ya Int insert Tick (Ev ` X1) Un
           (Za Int insert Tick (Ev ` X2) Un Z Int insert Tick (Ev ` X3)) Int
           insert Tick (Ev ` (X2 Un X3))"
by (auto)

lemma cspF_Alpha_parallel_assoc:
  "(P1 |[X1, X2]| P2) |[X1 Un X2, X3]| P3 =F[M,M]
   P1 |[X1, X2 Un X3]| (P2 |[X2, X3]| P3)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Alpha_parallel_assoc)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures_Alpha_parallel)
 apply (elim conjE exE)
 apply (simp add: Un_upper1 Un_upper2 rest_tr_of_rest_tr_subset)
 apply (rule_tac x="Ya" in exI, simp)
 apply (rule_tac x="(Za Int insert Tick (Ev ` X2)) Un 
                     (Z Int insert Tick (Ev ` X3))" in exI)
 apply (simp add: Un_assoc)
 apply (simp add: cspF_Alpha_parallel_ass_lm1)

 apply (rule_tac x="Za" in exI, simp)
 apply (rule_tac x="Z" in exI, simp)
 apply (force)

(* <= *)
 apply (rule)
 apply (simp add: in_failures_Alpha_parallel)
 apply (elim conjE exE)
 apply (simp add: Un_upper1 Un_upper2 rest_tr_of_rest_tr_subset)
 apply (rule_tac x="Y Int insert Tick (Ev ` X1) Un
                  (Ya Int insert Tick (Ev ` X2))" in exI)
 apply (rule_tac x="Za" in exI)
 apply (simp add: Un_assoc)
 apply (rule conjI)
 apply (fast)

 apply (rule_tac x="Y" in exI, simp)
 apply (rule_tac x="Ya" in exI, simp)
 apply (force)
done

lemma cspF_Alpha_parallel_assoc_sym:
  "P1 |[X1, X2 Un X3]| (P2 |[X2, X3]| P3) =F[M,M]
   (P1 |[X1, X2]| P2) |[X1 Un X2, X3]| P3"
apply (rule cspF_sym)
by (simp add: cspF_Alpha_parallel_assoc)

(************************************
 |          commutativity           |
 ************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Alpha_parallel_commut:
  "(P1 |[X1, X2]| P2) =F[M,M] (P2 |[X2, X1]| P1)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Alpha_parallel_commut)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures_Alpha_parallel)
 apply (elim conjE exE)
 apply (rule_tac x="Z" in exI)
 apply (rule_tac x="Y" in exI)
 apply (simp add: Un_commute)

(* <= *)
 apply (rule)
 apply (simp add: in_failures_Alpha_parallel)
 apply (elim conjE exE)
 apply (rule_tac x="Z" in exI)
 apply (rule_tac x="Y" in exI)
 apply (simp add: Un_commute)
done

(************************************
 |          monotonicity            |
 ************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Alpha_parallel_mono:
  "[| X1 = X2 ; Y1 = Y2 ;
      P1 <=F[M1,M2] Q1 ; 
      P2 <=F[M1,M2] Q2 |]
           ==> P1 |[X1,Y1]| P2 <=F[M1,M2] Q1 |[X2,Y2]| Q2"
apply (simp add: Alpha_parallel_def)
apply (simp add: cspF_Parallel_mono)
done

lemma cspF_Alpha_parallel_cong:
  "[| X1 = X2 ; Y1 = Y2 ;
      P1 =F[M1,M2] Q1 ; 
      P2 =F[M1,M2] Q2 |]
           ==> P1 |[X1,Y1]| P2 =F[M1,M2] Q1 |[X2,Y2]| Q2"
by (simp add: cspF_eq_ref_iff cspF_Alpha_parallel_mono)

lemmas cspF_decompo_Alpha_parallel = cspF_Alpha_parallel_mono
                                     cspF_Alpha_parallel_cong

(****************** to add them again ******************)
(*
declare Union_image_eq [simp]
declare Inter_image_eq [simp]
*)
(*
declare Sup_image_eq [simp]
declare Inf_image_eq [simp]
*)
end

