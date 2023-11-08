           (*-------------------------------------------*
            |                DFP package                |
            |                   June 2005               |
            |               December 2005  (modified)   |
            |                                           |
            |   DFP on CSP-Prover ver.3.0               |
            |              September 2006  (modified)   |
            |                  April 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory DFP_Proof_Rule1
imports DFP_Block
        HOL.Transitive_Closure
begin


(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite (notick | t = []t)                 *)
(*                                                                     *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*****************************************************************

         1. 
         2. 
         3. 
         4. 

 *****************************************************************)

(*--------------------------------------------------*
 |        Theorem 1 [Roscoe_Dathi_1987 P.8]         |
 *--------------------------------------------------*)

theorem Theorem1_Roscoe_Dathi_1987:
  "[| (I,FXf) isFailureOf (I,PXf) ; I ~= {} ; finite I ; 
      triple_disjoint (I,FXf) ; BusyNetwork (I,FXf) ; 
      EX f::('i => 'a failure => ('pi::order)).
      ALL t Yf. (t,Yf) isStateOf (I,FXf) -->
      (ALL i j. (I,FXf) >> i --[(t,Yf), (VocabularyOf (I,FXf))]-->o j
                --> f j (t rest-tr (snd (FXf j)), Yf j)
                  < f i (t rest-tr (snd (FXf i)), Yf i)) |]
   ==> DeadlockFreeNetwork (I,PXf)"
apply (simp add: DeadlockFree_notDeadlockState)
apply (case_tac "ALL t Yf. ~ (t, Yf) isDeadlockStateOf (I, FXf)", simp)

      (* by contradiction *)
apply (simp)
apply (elim conjE exE)
apply (subgoal_tac "(t,Yf) isStateOf (I,FXf)")
apply (simp add: Lemma1_Roscoe_Dathi_1987)
apply (subgoal_tac "EX j:I. ALL i:I. ~(f i (t rest-tr (snd (FXf i)), Yf i) 
                                     < f j (t rest-tr (snd (FXf j)), Yf j))")
apply (elim bexE)
apply (drule_tac x="j" in bspec, simp)
apply (simp add: isBlockedIn_def)
apply (elim conjE exE)
apply (drule_tac x="x" in spec)
apply (simp)

apply (drule_tac x="t" in spec)
apply (drule_tac x="Yf" in spec)
apply (simp)
apply (drule_tac x="j" in spec)
apply (drule_tac x="x" in spec)
apply (simp)
apply (drule_tac x="x" in bspec, simp add: isRequestOf_def)
apply (simp)

apply (simp add: nonempty_finite_set_exists_min_fun)
apply (simp add: isDeadlockStateOf_def)
done

(*--------------------------------------------------*
 |         Lemma 2 [Roscoe_Dathi_1987 P.9]          |
 *--------------------------------------------------*)

lemma Lemma2_Roscoe_Dathi_1987:
  "[| I ~= {} ; finite I ;
      triple_disjoint (I,FXf) ; BusyNetwork (I,FXf) ; 
      EX f::('i => 'a failure => ('pi::order)).
      ALL i:I. ALL j:I. i ~= j -->
      (ALL t Yf.
       (t,Yf) isStateOf ({i,j},FXf) &
       ({i,j},FXf) >> i --[(t,Yf), (VocabularyOf (I,FXf))]-->o j
                 --> f j (t rest-tr (snd (FXf j)), Yf j)
                   < f i (t rest-tr (snd (FXf i)), Yf i)) |]
   ==> EX f::('i => 'a failure => ('pi::order)).
       ALL t Yf. (t,Yf) isStateOf (I,FXf) -->
      (ALL i j. (I,FXf) >> i --[(t,Yf), (VocabularyOf (I,FXf))]-->o j
                --> f j (t rest-tr (snd (FXf j)), Yf j)
                  < f i (t rest-tr (snd (FXf i)), Yf i))"
apply (elim exE)
apply (rule_tac x="f" in exI)
apply (intro allI impI)
apply (drule_tac x="i" in bspec)
apply (simp add: in_index_I)
apply (drule_tac x="j" in bspec)
apply (simp add: in_index_I)
apply (simp add: in_index_I)

apply (drule_tac x="t rest-tr ((snd (FXf i) Un snd (FXf j)))" in spec)
apply (drule_tac x="Yf" in spec)
apply (drule mp)
 apply (rule conjI)
 apply (rule isStateOf_subsetI)
 apply (simp)
 apply (simp add: in_index_I)
 apply (blast)
 apply (rule isUngrantedRequestOfwrt_subsetI)
 apply (simp_all add: in_index_I)
 apply (simp add: in_index_I)
 apply (fast)
 apply (fast)

 apply (subgoal_tac 
    "t rest-tr ((snd (FXf i) Un snd (FXf j))) rest-tr (snd (FXf i))
   = t rest-tr (snd (FXf i))")
 apply (subgoal_tac 
    "t rest-tr ((snd (FXf i) Un snd (FXf j))) rest-tr (snd (FXf j))
   = t rest-tr (snd (FXf j))")
 apply (simp)
 apply (rule rest_tr_of_rest_tr_subset)
 apply (force)
 apply (rule rest_tr_of_rest_tr_subset)
 apply (force)
done

(*--------------------------------------------------*
 |         Rule 1 [Roscoe_Dathi_1987 P.9]           |
 *--------------------------------------------------*)

lemma Rule1_Roscoe_Dathi_1987:
  "[| (I,FXf) isFailureOf (I,PXf) ; I ~= {} ; finite I ;
      triple_disjoint (I,FXf) ; BusyNetwork (I,FXf) ; 
      EX f::('i => 'a failure => ('pi::order)).
      ALL i:I. ALL j:I. i ~= j -->
      (ALL t Yf.
       ({i,j},FXf) >> i --[(t,Yf), (VocabularyOf (I,FXf))]-->o j
                 --> f j (t rest-tr (snd (FXf j)), Yf j)
                   < f i (t rest-tr (snd (FXf i)), Yf i)) |]
   ==> DeadlockFreeNetwork (I,PXf)"
apply (rule Theorem1_Roscoe_Dathi_1987)
apply (simp_all)
apply (rule Lemma2_Roscoe_Dathi_1987)
apply (simp_all)
apply (simp add: isUngrantedRequestOfwrt_def)
apply (simp add: isUngrantedRequestOf_def)
apply (simp add: isRequestOf_def)
done

lemma Rule1_Roscoe_Dathi_1987_I:
  "[| (I,FXf) isFailureOf V ; I ~= {} ; finite I ;
      triple_disjoint (I,FXf) ; BusyNetwork (I,FXf) ; 
      EX f::('i => 'a failure => ('pi::order)).
      ALL i:I. ALL j:I. i ~= j -->
      (ALL t Yf.
       ({i,j},FXf) >> i --[(t,Yf), (VocabularyOf (I,FXf))]-->o j
                 --> f j (t rest-tr (snd (FXf j)), Yf j)
                   < f i (t rest-tr (snd (FXf i)), Yf i)) |]
   ==> DeadlockFreeNetwork V"
apply (insert decompo_V[of V])
apply (rotate_tac -1, erule exE)
apply (rotate_tac -1, erule exE)
apply (subgoal_tac "Ia = I")
apply (simp add: Rule1_Roscoe_Dathi_1987)
apply (simp add: isFailureOf_def)
done

(*** looks test ***)

theorem Rule1_Roscoe_Dathi_1987_simp:
  "[| VF = {(F i, X i) | i:I}Fnet ; V = {(P i, X i) | i:I}net ;
      VF isFailureOf V ; I ~= {} ; finite I ;
      triple_disjoint VF ; BusyNetwork VF ;
      EX f::('i => 'a failure => ('pi::order)).
      ALL i:I. ALL j:I. i ~= j -->
      (ALL t Y.
       {(F i, X i) | i:{i,j}}Fnet >> 
               i --[(t,Y), (VocabularyOf VF)]-->o j
                 --> f j (t rest-tr (X j), Y j)
                   < f i (t rest-tr (X i), Y i)) |]
   ==> DeadlockFreeNetwork V"
apply (simp)
apply (rule Rule1_Roscoe_Dathi_1987_I)
apply (simp_all)
apply (elim conjE exE)
apply (rule_tac x="f" in exI)
apply (auto)
done


(****************** to add it again ******************)

declare disj_not1   [simp]

end
