           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                    May 2005               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_law_rep_par
imports CSP_F_law_alpha_par CSP_F_op_rep_par CSP_T.CSP_T_law_rep_par
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

         1. associativity of [||]:I
         2. commutativity of [||]:I
         3. 
         4. 

 *****************************************************************)

(*****************************************************
   replace an index set with another equal index set
 *****************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Rep_parallel_index_eq_lm1:
   "[| inj_on f I1 ; ALL i:I1. PXf2 (f i) = PXf1 i |] ==>
    Union {(Yf i Int insert Tick (Ev ` snd (PXf1 i))) |i. i : I1} =
    Union {(Yf (inv_on I1 f i) Int insert Tick (Ev ` snd (PXf2 i))) |i. i : f ` I1}"
apply (rule) 

 (* => *)
 apply (rule, simp)
 apply (elim conjE exE)
 apply (rule_tac x="(Yf i) Int insert Tick (Ev ` snd (PXf2 (f i)))" in exI)
 apply (simp)
 apply (rule_tac x="f i" in exI)
 apply (simp add: inv_f_f_on)

 (* <= *)
 apply (rule, simp)
 apply (simp add: image_iff)
 apply (elim conjE exE bexE)
 apply (rule_tac x=
   "(Yf xb) Int insert Tick (Ev ` snd (PXf1 xb))" in exI)
 apply (simp)
 apply (simp add: inv_f_f_on)
 apply (rule_tac x="xb" in exI)
 apply (simp)
done

lemma cspF_Rep_parallel_index_eq_lm2:
   "ALL i:I1. PXf2 (f i) = PXf1 i ==>
    Union {(Yf i Int insert Tick (Ev ` snd (PXf2 i))) |i. i : f ` I1} =
    Union {(Yf (f i) Int insert Tick (Ev ` snd (PXf1 i))) |i. i : I1}"
apply (rule) 

 (* => *)
 apply (rule, simp)
 apply (simp add: image_iff)
 apply (elim conjE exE bexE)
 apply (simp)
 apply (rule_tac x="xa" in exI)
 apply (simp)
 apply (rule_tac x="xb" in exI)
 apply (simp)

 (* <= *)
 apply (rule, simp)
 apply (elim conjE exE)
 apply (rule_tac x="xa" in exI)
 apply (simp)
 apply (rule_tac x="f i" in exI)
 apply (simp)
done

(* main *)

lemma cspF_Rep_parallel_index_eq:
   "[| finite I1 ;
       EX f. I2 = f ` I1 & inj_on f I1 &
             (ALL i:I1. PXf2 (f i) = PXf1 i) |]
     ==> [||]:I1 PXf1 =F[M,M] [||]:I2 PXf2"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_parallel_index_eq)
apply (case_tac "I1 = {}", simp)
apply (rule order_antisym)

 (* <= *)
 apply (rule)
 apply (elim conjE exE)
 apply (simp add: in_failures_Rep_parallel)
 apply (subgoal_tac "Union (snd ` PXf2 ` f ` I1) = Union (snd ` PXf1 ` I1)")
 apply (simp)
 apply (elim conjE exE)
 apply (rule_tac x="(%i. Yf (inv_on I1 f i))" in exI)
 apply (simp add: inv_f_f_on)
 apply (simp add: cspF_Rep_parallel_index_eq_lm1)
 apply (simp add: Union_index_fun)

 (* => *)
 apply (rule)
 apply (elim conjE exE)
 apply (simp add: in_failures_Rep_parallel)
 apply (subgoal_tac "Union (snd ` PXf2 ` f ` I1) = Union (snd ` PXf1 ` I1)")
 apply (simp)
 apply (elim conjE exE)
 apply (rule_tac x="(%i. Yf (f i))" in exI)
 apply (simp)
 apply (simp add: cspF_Rep_parallel_index_eq_lm2)
 apply (simp add: Union_index_fun)
done

(*********************************************************
                [||]:I PXf ==> [||] PXs
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Index_to_Inductive_parallel:
  "[| finite I ; Is isListOf I |] ==>
   [||]:I PXf =F[M,M] [||] (map PXf Is)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Index_to_Inductive_parallel)
apply (case_tac "I = {}", simp)

apply (case_tac "map PXf Is = []")
apply (simp)
apply (rule order_antisym)

 (* <= *)
 apply (rule)
 apply (simp add: in_failures_Rep_parallel)
 apply (simp add: in_failures_Inductive_parallel_nth)
 apply (simp add: isListOf_set_eq)
 apply (elim conjE exE)
  apply (rule_tac x= "map Yf Is" in exI)
  apply (simp)
  apply (rule conjI)
  apply (rule in_failures_Rep_parallel_lm2, simp)
  apply (intro allI impI)
  apply (drule_tac x="Is ! i" in bspec)
  apply (simp add: isListOf_nth_in_index)
  apply (simp)

 (* => *)
 apply (rule)
 apply (simp add: in_failures_Rep_parallel)
 apply (simp add: in_failures_Inductive_parallel_nth)
 apply (simp add: isListOf_set_eq)
 apply (elim conjE exE)
 apply (rule_tac x= "(%i. (Ys!(THE n. (Is!n) = i & n<length Is)))" in exI)
  apply (rule conjI)
  apply (simp add: in_failures_Rep_parallel_lm1)
  apply (rule ballI)

  apply (erule isListOf_index_to_nthE)
  apply (drule_tac x="i" in bspec, simp)
  apply (elim conjE exE, simp)

  apply (drule_tac x="n" in spec, simp)
  apply (rotate_tac 4)
  apply (drule sym)
  apply (simp add: isListOf_THE_nth)
done

(************************************
 |       [||]:I PXf and SKIP        |
 ************************************)

lemma cspF_SKIP_Rep_parallel_right_lm1:
  "I ~= {} ==>
   insert Tick (Union {(Yf i Int insert Tick (Ev ` snd (PXf i))) |i. i : I})
   = Union {(insert Tick (Yf i Int Ev ` snd (PXf i))) |i. i : I}"
by (auto)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_SKIP_Rep_parallel_right:
  "finite I ==>
   (([||]:I PXf) |[Union (snd `  PXf ` I), {}]| SKIP) =F[M,M]
   ([||]:I PXf)"
apply (case_tac "I={}")
apply (simp add: cspF_SKIP_Alpha_parallel)

  apply (simp add: cspF_cspT_semantics)
(* Isabelle 2017 *)
apply (simp add: cspT_SKIP_Rep_parallel_right[simplified])
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures_Alpha_parallel)
 apply (simp add: in_failures_Rep_parallel)
 apply (elim conjE exE)

  apply (case_tac "Tick ~: Z")
  apply (simp)
  apply (rule_tac x="Yf" in exI)
  apply (rule conjI)
  apply (subgoal_tac "Z Int {Tick} = {}")
  apply (simp (no_asm_simp))
  apply (simp)

  apply (intro ballI)
  apply (drule_tac x="i" in bspec, simp)
  apply (subgoal_tac " snd (PXf i) <= Union (snd ` PXf ` I)")
  apply (simp add: rest_tr_of_rest_tr_subset)
  apply (force)

  apply (simp add: in_failures)
  apply (erule disjE)
  apply (simp add: Evset_def)
  apply (force)

  apply (rule_tac x="(%i. insert Tick (Yf i))" in exI)
  apply (simp)
  apply (subgoal_tac "Z Int {Tick} = {Tick}", simp)
  apply (simp add: cspF_SKIP_Rep_parallel_right_lm1)

  apply (intro ballI)
  apply (drule_tac x="i" in bspec, simp)
  apply (subgoal_tac " snd (PXf i) <= Union (snd ` PXf ` I)")
  apply (simp add: rest_tr_of_rest_tr_subset)

  apply (simp add: rest_tr_Tick_sett)
  apply (elim conjE exE)
  apply (simp)
  apply (rule proc_T2_T3)
  apply (simp)
  apply (simp)
  apply (force)
  apply (force)

(* <= *)
 apply (rule)
 apply (simp add: in_failures_Alpha_parallel)
 apply (rule_tac x="X" in exI)
 apply (rule_tac x="{}" in exI)
 apply (simp)

 apply (simp add: in_failures)
 apply (simp add: rest_tr_empty)
 apply (simp add: in_failures_Rep_parallel)
 apply (elim conjE exE)
 apply (rule_tac x="Yf" in exI)
 apply (simp)
 apply (intro ballI)
 apply (drule_tac x="i" in bspec, simp)

 apply (subgoal_tac " snd (PXf i) <= Union (snd ` PXf ` I)")
 apply (simp add: rest_tr_of_rest_tr_subset)
 apply (force)
done

(************************************
 |        SKIP and [||]:I PXf       |
 ************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_SKIP_Rep_parallel_left:
  "finite I ==>
   (SKIP |[{}, Union (snd ` PXf ` I)]| ([||]:I PXf)) =F[M,M]
   ([||]:I PXf)"
apply (subgoal_tac 
    "(SKIP |[{}, Union (snd ` PXf ` I)]| ([||]:I PXf)) =F[M,M]
     (([||]:I PXf) |[Union (snd ` PXf ` I), {}]| SKIP)")
apply (rule cspF_trans)
    apply (simp)
(* Isabelle 2017 *)
apply (simp add: cspF_SKIP_Rep_parallel_right[simplified])
apply (simp add: cspF_Alpha_parallel_commut)
done

(*** left and right ***)

lemmas cspF_SKIP_Rep_parallel = cspF_SKIP_Rep_parallel_left
                                  cspF_SKIP_Rep_parallel_right

(************************************
 |          associativity           |
 ************************************)

lemma cspF_Rep_parallel_ass_lm1:
   "Union {(Yf i Int insert Tick (Ev ` snd (PXf i))) |i. i : I} Int
           insert Tick (Ev ` Union (snd ` PXf ` I))
    = Union {(Yf i Int insert Tick (Ev ` snd (PXf i))) |i. i : I}"
by (auto)

lemma cspF_Rep_parallel_ass_lm2:
   "I1 Int I2 = {} ==>
    Union {(Yf1 i Int insert Tick (Ev ` snd (PXf i))) |i. i : I1} Un
    Union {(Yf2 i Int insert Tick (Ev ` snd (PXf i))) |i. i : I2} =
    Union {(if i : I1 then Yf1 i else Yf2 i) Int insert Tick (Ev ` snd (PXf i)) |i.
           i : I1 | i : I2}"
apply (rule)

 apply (rule)
 apply (simp)
 apply (elim disjE conjE exE)

  apply (rule_tac x="Yf1 i Int insert Tick (Ev ` snd (PXf i))" in exI, simp)
  apply (rule_tac x="i" in exI, simp)
  apply (rule_tac x="Yf2 i Int insert Tick (Ev ` snd (PXf i))" in exI, simp)
  apply (rule_tac x="i" in exI, simp)
  apply (force)

 apply (rule)
 apply (simp)
 apply (elim disjE conjE exE)

  apply (rule disjI1)
  apply (rule_tac x="Yf1 i Int insert Tick (Ev ` snd (PXf i))" in exI, simp)
  apply (rule_tac x="i" in exI, simp)
  apply (rule disjI2)
  apply (case_tac "i ~: I1")
  apply (rule_tac x="Yf2 i Int insert Tick (Ev ` snd (PXf i))" in exI, simp)
  apply (rule_tac x="i" in exI, simp)
  apply (force)
done

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Rep_parallel_assoc:
 "[| I1 Int I2 = {} ; finite I1 ; finite I2 |] ==>
  [||]:(I1 Un I2) PXf =F[M,M]
  [||]:I1 PXf |[Union (snd ` PXf ` I1), Union (snd ` PXf ` I2)]| [||]:I2 PXf"

apply (case_tac "I1 = {}")
apply (case_tac "I2 = {}")
apply (rule cspF_sym)
apply (simp add: cspF_SKIP_Alpha_parallel)
   apply (rule cspF_sym)
(* Isabellle 2017 *)
apply (simp add: cspF_SKIP_Rep_parallel[simplified])

apply (case_tac "I2 = {}")
   apply (rule cspF_sym)
(* Isabelle2017 *)
apply (simp add: cspF_SKIP_Rep_parallel[simplified])

apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_parallel_assoc[simplified])
apply (rule order_antisym)

 (* => *)
 apply (rule)
 apply (simp add: in_failures_Alpha_parallel)
 apply (simp add: in_failures_Rep_parallel)
 apply (elim conjE exE)

 apply (rule_tac x="Union {(Yf i Int insert Tick (Ev ` snd (PXf i))) |i. i : I1}" in exI)
 apply (rule_tac x="Union {(Yf i Int insert Tick (Ev ` snd (PXf i))) |i. i : I2}" in exI)
 apply (simp add: Union_snd_Un)
 apply (rule conjI)
  apply (simp add: cspF_Rep_parallel_ass_lm1[simplified])
  apply (blast)

 apply (rule conjI)

  (* I1 *)
  apply (rule_tac x="Yf" in exI)
  apply (simp add: cspF_Rep_parallel_ass_lm1[simplified])

  apply (intro ballI)
  apply (drule_tac x="i" in bspec, simp)
  apply (subgoal_tac "snd (PXf i) <= Union (snd ` PXf ` I1)")
  apply (simp add: rest_tr_of_rest_tr_subset)
  apply (force)

  (* I2 *)
  apply (rule_tac x="Yf" in exI)
  apply (simp add: cspF_Rep_parallel_ass_lm1[simplified])

  apply (intro ballI)
  apply (drule_tac x="i" in bspec, simp)
  apply (subgoal_tac "snd (PXf i) <= Union (snd ` PXf ` I2)")
  apply (simp add: rest_tr_of_rest_tr_subset)
  apply (force)

 (* <= *)
 apply (rule)
 apply (simp add: in_failures_Alpha_parallel)
 apply (simp add: in_failures_Rep_parallel)
 apply (elim exE conjE)
 apply (simp add: Union_snd_Un)
 apply (rename_tac s X Y Z Yf1 Yf2)

 apply (rule_tac x="(%i. if i:I1 then Yf1 i else Yf2 i)" in exI)
       (* the necessity of the condition "I1 Int I2 = {}" *)
 apply (simp add: cspF_Rep_parallel_ass_lm2)

 apply (intro ballI)
 apply (simp)
 apply (erule disjE)

  apply (drule_tac x="i" in bspec, simp, simp)
  apply (subgoal_tac "snd (PXf i) <= Union (snd ` PXf ` I1)")
  apply (simp add: rest_tr_of_rest_tr_subset)
  apply (force)

  apply (drule_tac x="i" in bspec, simp)
  apply (case_tac "i ~: I1")
  apply (subgoal_tac "snd (PXf i) <= Union (snd ` PXf ` I2)")
  apply (simp add: rest_tr_of_rest_tr_subset)
  apply (force)
  apply (blast)
done

(************************************
 |             induct               |
 ************************************)

(*------------------*
 |     csp law      |
 |   (derivable)    |
 *------------------*)

lemma cspF_Rep_parallel_induct:
 "[| finite I ; i ~: I |] ==>
  [||]:(insert i I) PXf =F[M,M]
  fst (PXf i) |[snd (PXf i), Union (snd ` PXf ` I)]| [||]:I PXf"
apply (insert cspF_Rep_parallel_assoc[of "{i}" I PXf M])
apply (simp add: Rep_parallel_one)
apply (rule cspF_rw_left)
apply (simp)

apply (insert cspF_Alpha_parallel_assoc
  [of "fst (PXf i)" "snd (PXf i)" "{}" "SKIP" "Union (snd ` PXf ` I)" "[||]:I PXf" M])
apply (rule cspF_trans)
apply (simp)

apply (rule cspF_decompo_Alpha_parallel)
apply (simp_all)
(* Isabelle 2017 *)
apply (simp add: cspF_SKIP_Rep_parallel[simplified])
done

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

