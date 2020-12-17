           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                    May 2005               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_law_alpha_par
imports CSP_T_op_alpha_par CSP_T_law_decompo
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  Union (B ` A) = (UN x:A. B x)                      *)
(*                  Inter (B ` A) = (INT x:A. B x)                     *)

(* Isabelle 2013
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

lemma cspT_SKIP_Alpha_parallel:
  "(SKIP |[{}, {}]| SKIP) =T[M1,M2] SKIP"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces in_traces_Alpha_parallel)
 apply (simp add: sett_subset_Tick)

(* <= *)
 apply (rule)
 apply (simp add: in_traces in_traces_Alpha_parallel)
 apply (simp add: sett_subset_Tick)
 apply (insert rest_tr_sett_subseteq_sett[of _ "{}"])
 apply (auto)
done

(************************************
 |          associativity           |
 ************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Alpha_parallel_assoc:
  "(P1 |[X1, X2]| P2) |[X1 Un X2, X3]| P3 =T[M,M]
   P1 |[X1, X2 Un X3]| (P2 |[X2, X3]| P3)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces_Alpha_parallel)
 apply (elim conjE exE)
 apply (simp add: Un_upper1 Un_upper2 rest_tr_of_rest_tr_subset)
 apply (simp add: Un_assoc)

(* <= *)
 apply (rule)
 apply (simp add: in_traces_Alpha_parallel)
 apply (elim conjE exE)
 apply (simp add: Un_upper1 Un_upper2 rest_tr_of_rest_tr_subset)
 apply (simp add: Un_assoc)
done

lemma cspT_Alpha_parallel_assoc_sym:
  "P1 |[X1, X2 Un X3]| (P2 |[X2, X3]| P3) =T[M,M]
   (P1 |[X1, X2]| P2) |[X1 Un X2, X3]| P3"
apply (rule cspT_sym)
by (simp add: cspT_Alpha_parallel_assoc)

(************************************
 |          commutativity           |
 ************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Alpha_parallel_commut:
  "(P1 |[X1, X2]| P2) =T[M,M] (P2 |[X2, X1]| P1)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces_Alpha_parallel)
 apply (fast)

(* <= *)
 apply (rule)
 apply (simp add: in_traces_Alpha_parallel)
 apply (fast)
done

(************************************
 |          monotonicity            |
 ************************************)

(*------------------*
 |      csp law M   |
 *------------------*)

lemma cspT_Alpha_parallel_mono:
  "[| X1 = X2 ; Y1 = Y2 ;
      P1 <=T[M1,M2] Q1 ; 
      P2 <=T[M1,M2] Q2 |]
           ==> P1 |[X1,Y1]| P2 <=T[M1,M2] Q1 |[X2,Y2]| Q2"
apply (simp add: Alpha_parallel_def)
apply (simp add: cspT_Parallel_mono)
done

lemma cspT_Alpha_parallel_cong:
  "[| X1 = X2 ; Y1 = Y2 ;
      P1 =T[M1,M2] Q1 ; 
      P2 =T[M1,M2] Q2 |]
           ==> P1 |[X1,Y1]| P2 =T[M1,M2] Q1 |[X2,Y2]| Q2"
by (simp add: cspT_eq_ref_iff cspT_Alpha_parallel_mono)

lemmas cspT_decompo_Alpha_parallel = cspT_Alpha_parallel_mono
                                     cspT_Alpha_parallel_cong

(****************** to add them again ******************)
(* 2013
declare Union_image_eq [simp]
declare Inter_image_eq [simp]
*)
(* 2017
declare Sup_image_eq [simp]
declare Inf_image_eq [simp]
*)
end

