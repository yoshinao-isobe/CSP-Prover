theory TSF_Theorem1
imports TSF_Lemma1
        TSF_law
        TSF_Lemma2
        TSF_Network
begin


subsection \<open> Theorem 1 \<close>

theorem Theorem1_Jesus_Sampaio_2022:
    "[| isTockNet (I,PXf); I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) ;
        tock_triple_conjoint (I,FXf) ; NonTockBusyNetwork (I,FXf) ;
        ALL i:I. ~ Ev ` snd (FXf i) <= {Tock} ;
        EX f::('i => 'a::tockCSP failure => ('pi::order)) .
          ALL t Yf. (t,Yf) isStateOf (I,FXf) -->
          (ALL i j. (I,FXf) >> i --tock[(t,Yf), (VocabularyOf (I,FXf))]-->o j
                    --> f j (t rest-tr (snd (FXf j)), Yf j)
                      < f i (t rest-tr (snd (FXf i)), Yf i)) |]
     ==> TimeStopFreeNetwork (I,PXf)"
  apply (subst TimeStopFreeNetwork_iff_DeadlockFree_PAR_Nontock, simp, simp)

  apply (simp only: DeadlockFree_def)
  apply (subst unfolded_DeadlockFree_PAR_Hiding_notNonTockDeadlockState)
  apply (simp, simp, simp, simp)
  apply (simp add: isNonTockDeadlockStateOf_def, rule, rule, rule)

  apply (elim exE)
  apply (drule_tac x=a in spec)
  apply (drule_tac x=b in spec)
  apply (simp)

  apply (simp only: all_not_ex)
  apply (rotate_tac -1)
  apply (erule contrapos_np, simp)

  apply (frule Lemma2_Jesus_Sampaio_2022, simp, simp, simp)
  apply (simp add: isNonTockDeadlockStateOf_def)

  (* 1 - order subgoal *)
  apply (subgoal_tac "EX j:I. ALL i:I. ~(f i (a rest-tr (snd (FXf i)), b i) 
                                       < f j (a rest-tr (snd (FXf j)), b j))")
  (* "Instantiates" index j *)
  apply (elim bexE)

  (* "Instantiates" index i *)
  apply (rotate_tac -3)
  apply (drule_tac x=j in bspec, simp)
  apply (simp only: isBlockedInNonTock_def, elim conjE exE)

  apply (simp only: isRequestOf_def, elim conjE, simp)

  apply (rotate_tac -2)
  apply (drule_tac x=ja in bspec, simp)

  apply (rule_tac x=j in exI)
  apply (rule_tac x=ja in exI)
  apply (simp)

  (* 1 - prove order subgoal *)
  apply (simp add: nonempty_finite_set_exists_min_fun)
  done


subsection \<open> Lemma 3 \<close>

lemma Lemma3_Jesus_Sampaio_2022:
    "[| I ~= {} ; finite I ; 
        EX f::('i => 'a::tockCSP failure => ('pi::order)).
        ALL i:I. ALL j:I. i ~= j -->
        (ALL t Yf.
         (t,Yf) isStateOf ({i,j},FXf) &
         ({i,j},FXf) >> i --tock[(t,Yf), (VocabularyOf (I,FXf))]-->o j
                   --> f j (t rest-tr (snd (FXf j)), Yf j)
                     < f i (t rest-tr (snd (FXf i)), Yf i)) |]
     ==> EX f::('i => 'a::tockCSP failure => ('pi::order)).
         ALL t Yf. (t,Yf) isStateOf (I,FXf) -->
        (ALL i j. (I,FXf) >> i --tock[(t,Yf), (VocabularyOf (I,FXf))]-->o j
                  --> f j (t rest-tr (snd (FXf j)), Yf j)
                    < f i (t rest-tr (snd (FXf i)), Yf i))"
  apply (elim exE)
  apply (rule_tac x="f" in exI)
  apply (intro allI impI)
  apply (drule_tac x="i" in bspec)
  apply (simp add: in_index_NonTock_I)
  apply (drule_tac x="j" in bspec)
  apply (simp add: in_index_NonTock_I)
  apply (simp add: in_index_NonTock_I)
  
  apply (drule_tac x="t rest-tr ((snd (FXf i) Un snd (FXf j)))" in spec)
  apply (drule_tac x="Yf" in spec)
  apply (drule mp)
   apply (rule conjI)
   apply (rule isStateOf_subsetI)
   apply (simp)
   apply (simp add: in_index_NonTock_I)
   apply (blast)
   apply (rule isUngrantedNonTockRequestOfwrt_subsetI)
   apply (simp add: in_index_NonTock_I)
   apply (simp add: in_index_NonTock_I)
   apply (fast)
   apply (fast)
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



subsection \<open> Rule 1 \<close>

lemma Rule1_Jesus_Sampaio_2022:
    "[| isTockNet (I,PXf); I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) ;
        tock_triple_conjoint (I,FXf) ; NonTockBusyNetwork (I,FXf) ;
        ALL i:I. \<not> Ev ` snd (FXf i) \<subseteq> {Tock} ; 
        EX f::('i => 'a::tockCSP failure => ('pi::order)) .
        ALL i:I. ALL j:I. i ~= j -->
        (ALL t Yf.
         ({i,j},FXf) >> i --tock[(t,Yf), (VocabularyOf (I,FXf))]-->o j
                   --> f j (t rest-tr (snd (FXf j)), Yf j)
                     < f i (t rest-tr (snd (FXf i)), Yf i)) |]
     ==> TimeStopFreeNetwork (I,PXf)"
  apply (rule Theorem1_Jesus_Sampaio_2022)
  apply (simp_all)
  apply (rule Lemma3_Jesus_Sampaio_2022)
  apply (simp_all)
  apply (simp add: isUngrantedNonTockRequestOfwrt_def)
  apply (simp add: isUngrantedNonTockRequestOf_def)
  apply (simp add: isRequestOf_def)
  done

lemma Rule1_Jesus_Sampaio_2022_I:
    "[| isTockNet V; I ~= {} ; finite I ; (I,FXf) isFailureOf V ;
        tock_triple_conjoint (I,FXf) ; NonTockBusyNetwork (I,FXf) ;
        ALL i:I. \<not> Ev ` snd (FXf i) \<subseteq> {Tock} ;
        EX f::('i => 'a::tockCSP failure => ('pi::order)).
        ALL i:I. ALL j:I. i ~= j -->
        (ALL t Yf.
         ({i,j},FXf) >> i --tock[(t,Yf), (VocabularyOf (I,FXf))]-->o j
                   --> f j (t rest-tr (snd (FXf j)), Yf j)
                     < f i (t rest-tr (snd (FXf i)), Yf i)) |]
     ==> TimeStopFreeNetwork V"
  apply (insert decompo_V[of V])
  apply (rotate_tac -1, erule exE)
  apply (rotate_tac -1, erule exE)
  apply (subgoal_tac "Ia = I")
  apply (simp)
  apply (subst Rule1_Jesus_Sampaio_2022, simp_all)
  apply (simp add: isFailureOf_def)
  done

(*** looks test ***)

theorem Rule1_Jesus_Sampaio_2022_simp:
    "[| VF = {(F i, X i) | i:I}Fnet ; V = {(P i, X i) | i:I}net ;
        VF isFailureOf V ; I ~= {} ; finite I ; isTockNet VF;
        tock_triple_conjoint VF ; NonTockBusyNetwork VF ;
        ALL i:I. ~ Ev ` snd (snd VF i) <= {Tock} ;
        EX f::('i => 'a::tockCSP failure => ('pi::order)).
        ALL i:I. ALL j:I. i ~= j -->
        (ALL t Y.
         {(F i, X i) | i:{i,j}}Fnet >> 
                 i --tock[(t,Y), (VocabularyOf VF)]-->o j
                   --> f j (t rest-tr (X j), Y j)
                     < f i (t rest-tr (X i), Y i)) |]
     ==> TimeStopFreeNetwork V"
  apply (simp)
  apply (rule Rule1_Jesus_Sampaio_2022_I)
  apply (simp_all, simp)
  apply (elim conjE exE)
  apply (rule_tac x="f" in exI)
  apply (auto)
  done


end