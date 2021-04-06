           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                    May 2005               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_law_rep_par
imports CSP_T_law_alpha_par CSP_T_op_rep_par
begin

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

lemma cspT_Rep_parallel_index_eq:
   "[| finite I1 ;
       EX f. I2 = f ` I1 & inj_on f I1 &
             (ALL i:I1. PXf2 (f i) = PXf1 i) |]
    ==> [||]:I1 PXf1 =T[M,M] [||]:I2 PXf2"
apply (simp add: cspT_semantics)

apply (case_tac "I1 = {}")
apply (simp)
apply (rule order_antisym)

 (* <= *)
 apply (rule)
 apply (elim conjE exE)
   apply (simp add: in_traces_par)
(* not necessary for Isabelle 2017
 apply (subgoal_tac "Union (snd ` PXf2 ` f ` I1) = Union (snd ` PXf1 ` I1)")
 apply (simp)
 apply (simp add: Union_index_fun)
*)

 (* => *)
 apply (rule)
 apply (elim conjE exE)
  apply (simp add: in_traces_par)
(* not necessary for Isabelle 2017
 apply (subgoal_tac "Union (snd ` PXf2 ` f ` I1) = Union (snd ` PXf1 ` I1)")
 apply (simp)
 apply (simp add: Union_index_fun)
*)
done

(*********************************************************
                [||]:I PXf ==> [||] PXs
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Index_to_Inductive_parallel:
  "[| finite I ; Is isListOf I |] ==>
   [||]:I PXf =T[M,M] [||] (map PXf Is)"
apply (simp add: cspT_semantics)

apply (case_tac "I = {}")
apply (simp)

apply (case_tac "map PXf Is = []")
apply (simp)
apply (rule order_antisym)

 (* <= *)
 apply (rule)
 apply (simp add: in_traces_Rep_parallel)
 apply (simp add: in_traces_Inductive_parallel_nth)
 apply (simp add: isListOf_set_eq)
 apply (intro allI impI)
 apply (elim conjE exE)
 apply (drule_tac x="Is!i" in bspec)
 apply (simp add: isListOf_nth_in_index)
 apply (simp)

 (* => *)
 apply (rule)
 apply (simp add: in_traces_Rep_parallel)
 apply (simp add: in_traces_Inductive_parallel_nth)
 apply (simp add: isListOf_set_eq)
 apply (intro ballI)
 apply (elim conjE)
 apply (erule isListOf_index_to_nthE)
 apply (drule_tac x="i" in bspec, simp)
 apply (elim exE conjE)
 apply (drule_tac x="n" in spec, simp)
done

(************************************
 |       [||]:I PXf and SKIP        |
 ************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_SKIP_Rep_parallel_right:
  "finite I ==>
   (([||]:I PXf) |[Union (snd `  PXf ` I), {}]| SKIP) =T[M,M]
   ([||]:I PXf)"
apply (case_tac "I={}")
apply (simp add: cspT_SKIP_Alpha_parallel)

apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces_par)

 apply (intro ballI)
 apply (elim conjE)
 apply (drule_tac x="i" in bspec, simp)
 apply (subgoal_tac "snd (PXf i) <= Union (snd ` PXf ` I)")
 apply (simp add: rest_tr_of_rest_tr_subset)
 apply (force)

(* <= *)
 apply (rule)
 apply (simp add: in_traces_par in_traces)
 apply (simp add: rest_tr_empty)

 apply (intro ballI)
 apply (elim conjE)
 apply (drule_tac x="i" in bspec, simp)
 apply (subgoal_tac "snd (PXf i) <= Union (snd ` PXf ` I)")
 apply (simp add: rest_tr_of_rest_tr_subset)
 apply (force)
done

(************************************
 |        SKIP and [||]:I PXf       |
 ************************************)

(*------------------*
 |      csp law     |
 *------------------*)


lemma cspT_SKIP_Rep_parallel_left:
  "finite I ==>
   (SKIP |[{}, Union (snd ` PXf ` I)]| ([||]:I PXf)) =T[M,M]
   ([||]:I PXf)"
  apply (subgoal_tac 
    "(SKIP |[{}, Union (snd ` PXf ` I)]| ([||]:I PXf)) =T[M,M]
     (([||]:I PXf) |[Union (snd ` PXf ` I), {}]| SKIP)")
apply (rule cspT_trans)
(* modified for Isabelle 2017 *)
  apply (simp del: UN_simps SUP_image)
  apply (simp del: UN_simps SUP_image add: cspT_SKIP_Rep_parallel_right)
apply (simp add: cspT_Alpha_parallel_commut)
done

(*** left and right ***)

lemmas cspT_SKIP_Rep_parallel = cspT_SKIP_Rep_parallel_left
                                  cspT_SKIP_Rep_parallel_right

(************************************
 |          associativity           |
 ************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Rep_parallel_assoc:
 "[| I1 Int I2 = {} ; finite I1 ; finite I2 |] ==>
  [||]:(I1 Un I2) PXf =T[M,M]
  [||]:I1 PXf |[Union (snd ` PXf ` I1), Union (snd ` PXf ` I2)]| [||]:I2 PXf"

  apply (case_tac "I1 = {}")
   apply (case_tac "I2 = {}")
    apply (rule cspT_sym)
    apply (simp add: cspT_SKIP_Alpha_parallel)

   apply (rule cspT_sym)
(* for Isabelle 2017 *)
   apply (simp del: UN_simps SUP_image add: cspT_SKIP_Rep_parallel)

  apply (case_tac "I2 = {}")
   apply (rule cspT_sym)
(* for Isabelle 2017 *)
   apply (simp del: UN_simps SUP_image add: cspT_SKIP_Rep_parallel)
  apply (simp add: cspT_semantics)
apply (rule order_antisym)

 (* => *)
 apply (rule)
(* for Isabelle 2017 *)
 apply (simp del: UN_simps SUP_image add: in_traces_par)
 apply (simp add: Union_snd_Un)
 apply (elim conjE)
 apply (rule conjI)

  apply (intro ballI)
  apply (drule_tac x="i" in bspec, simp)
  apply (subgoal_tac "snd (PXf i) <= Union (snd ` PXf ` I1)")
  apply (simp add: rest_tr_of_rest_tr_subset)
  apply (force)

  apply (intro ballI)
  apply (drule_tac x="i" in bspec, simp)
  apply (subgoal_tac "snd (PXf i) <= Union (snd ` PXf ` I2)")
  apply (simp add: rest_tr_of_rest_tr_subset)
  apply (force)

 (* <= *)
 apply (rule)
(* for Isabelle 2017 *)
 apply (simp del: UN_simps SUP_image add: in_traces_par)
 apply (simp add: Union_snd_Un)
 apply (elim conjE)

 apply (intro ballI)
 apply (simp)
 apply (erule disjE)

  apply (drule_tac x="i" in bspec, simp)
  apply (subgoal_tac "snd (PXf i) <= Union (snd ` PXf ` I1)")
  apply (simp add: rest_tr_of_rest_tr_subset)
  apply (force)

  apply (drule_tac x="i" in bspec, simp)
  apply (subgoal_tac "snd (PXf i) <= Union (snd ` PXf ` I2)")
  apply (simp add: rest_tr_of_rest_tr_subset)
  apply (force)
done

(************************************
 |             induct               |
 ************************************)

(*------------------*
 |     csp law      |
 |   (derivable)    |
 *------------------*)

lemma cspT_Rep_parallel_induct:
 "[| finite I ; i ~: I |] ==>
  [||]:(insert i I) PXf =T[M,M]
  fst (PXf i) |[snd (PXf i), Union (snd ` PXf ` I)]| [||]:I PXf"
apply (insert cspT_Rep_parallel_assoc[of "{i}" I PXf M])
apply (simp add: Rep_parallel_one)
apply (rule cspT_trans)
apply (simp)

apply (insert cspT_Alpha_parallel_assoc
  [of "fst (PXf i)" "snd (PXf i)" "{}" "SKIP" "Union (snd ` PXf ` I)" "[||]:I PXf" M])
apply (rule cspT_trans)
apply (simp)

  apply (rule cspT_decompo_Alpha_parallel)
(* for Isabelle 2017 *)
apply (simp_all)
apply (simp add: cspT_SKIP_Rep_parallel[simplified])
done

end

