theory TSF_Blocked
imports tockCSP_Network
begin



subsection \<open> tock_triple_conjoint \<close>


definition tock_triple_conjoint :: "('i set * ('i => ('b * 'e::tockCSP set))) => bool"
where
    "tock_triple_conjoint VF == 
       (ALL i: fst VF. ALL j: fst VF. ALL k: fst VF. i ~= j & j ~= k & k ~= i
          --> (snd ((snd VF) i) Int snd ((snd VF) j) Int snd ((snd VF) k) = {tock}))"


subsection \<open> Requests \<close>

definition isUngrantedNonTockRequestOf :: "('i,'e) NetworkF => 'i => ('i,'e::tockCSP) net_state => 'i => bool"
      ("(1_ >> /(0_ (1/--tock[_]-->o) /_))" [800, 800,0,800] 900)
where
    "VF >> i --tock[sigma]-->o j ==
        VF >> i --[sigma]--> j &
        ~ (sigma isTimeStopStateOf VF) &
        Ev ` (snd (snd VF i)) Int Ev ` (snd (snd VF j)) - {Tock}
        <= (snd sigma) i Un (snd sigma) j"


definition isUngrantedNonTockRequestOfwrt :: "('i,'e) NetworkF => 'i => ('i,'e) net_state => 'e::tockCSP set => 'i => bool"
      ("(1_ >> /(0_ (1/--tock[(0_,/_)]-->o) /_))" [800, 800,0,0,800] 900)
where
    "VF >> i --tock[sigma,Lambda]-->o j ==
        VF >> i --tock[sigma]-->o j &
        (((Ev ` (snd (snd VF i))) - (snd sigma) i) Un
         ((Ev ` (snd (snd VF j))) - (snd sigma) j)) - {Tock} <= Ev ` Lambda"



subsection \<open> BlockedIn NonTock \<close>


definition  isBlockedInNonTock :: "('i,'e) NetworkF => 'i => ('i,'e::tockCSP) net_state => bool"
      ("(_ >> _ isBlockedInNonTock _)" [800, 800, 800] 900)
where
    "VF >> i isBlockedInNonTock sigma == 
          tock_triple_conjoint VF &
          (EX j. VF >> i --[sigma]--> j) &
          (ALL j. VF >> i --[sigma]--> j
          --> (VF >> i --tock[sigma, (VocabularyOf VF)]-->o j))"





subsection \<open> Lemmas \<close>

subsubsection \<open> tock_triple_conjoint \<close>


lemma tock_triple_conjoint_PXf_FXf :
    "tock_triple_conjoint (I,PXf) \<Longrightarrow> (I,FXf) isFailureOf (I,PXf) \<Longrightarrow>
     tock_triple_conjoint (I,FXf)"
  apply (simp add: tock_triple_conjoint_def)
  by (simp add: isFailureOf_def)



subsubsection \<open> ungranted requests --> in index I \<close>

lemma in_index_NonTock_I1:
  "(I, FXf) >> i --tock[sigma]-->o j ==> i : I & j : I & i ~= j"
apply (simp add: isUngrantedNonTockRequestOf_def)
apply (elim conjE)
by (simp add: in_index_I)

lemma in_index_NonTock_I2:
  "(I, FXf) >> i --tock[sigma,Lambda]-->o j ==> i : I & j : I & i ~= j"
apply (simp add: isUngrantedNonTockRequestOfwrt_def)
apply (elim conjE)
by (simp add: in_index_NonTock_I1)

lemmas in_index_NonTock_I = in_index_NonTock_I1 in_index_NonTock_I2





subsubsection \<open> ungranted requests --> subset \<close>

lemma isUngrantedNonTockRequestOf_subsetI:
  "[| (I, FXf) >> i --tock[(t,Yf)]-->o j; J <= I; i:J ; j:J ; 
      X = Union {snd (FXf i)|i. i:J} |]
   ==> (J, FXf) >> i --tock[(t rest-tr X,Yf)]-->o j"
apply (simp add: isUngrantedNonTockRequestOf_def)
apply (rule)
apply (rule isRequestOf_subsetI, simp_all)
apply (simp add: isTimeStopStateOf_def refusesTock_def, elim conjE)
apply (rule)
apply (simp add: isRequestOf_def, elim conjE)
apply (rule)
apply (drule_tac x=x in spec, fast)
done


lemma isUngrantedNonTockRequestOfwrt_subsetI:
  "[| (I, FXf) >> i --tock[(t,Yf), Lambda1]-->o j; J <= I; i:J ; j:J ; 
      Lambda1 <= Lambda2 ; X = Union {snd (FXf i)|i. i:J} |]
   ==> (J, FXf) >> i --tock[(t rest-tr X,Yf), Lambda2]-->o j"
apply (simp add: isUngrantedNonTockRequestOfwrt_def)
apply (rule conjI)
apply (rule isUngrantedNonTockRequestOf_subsetI)
apply (simp_all)
apply (blast)
done


subsubsection \<open> requests intro \<close>

lemma ex_target_for_NonTockRequest_nonTock_refusals :
    "(t, Yf) isNonTockDeadlockStateOf (I, FXf) ==>
     i : I ==> Yf i ~= Ev ` snd (FXf i) - {Tock} ==>
     EX j. (I, FXf) >> i --[(t, Yf)]--> j"
  apply (simp only: isRequestOf_def)

  apply (frule isStateOf_if_isNonTockDeadlockStateOf)
  apply (frule refusals_are_subsets_if_isStateOf)

  apply (frule Union_refusals_ALP_if_isNonTockDeadlockStateOf)
  apply (simp only: ALP_def)

  (* i is not refusing event a from its synchronisation set *)
  apply (frule ex_non_refused_nonTock_event_if_isNonTockDeadlockStateOf[of t Yf I FXf i])
    apply (simp_all)
    apply (elim bexE)
  apply (subgoal_tac "Ev a : Ev ` {a. EX i:I. a : snd (FXf i)} - {Tock}")
                                                  (* ... sub 1 *)
  apply (rotate_tac 1)
  apply (drule sym)
  apply (simp)
  apply (elim conjE exE)
  apply (simp)

  apply (rule_tac x="ia" in exI)
  apply (case_tac "i = ia", simp)
  apply (simp)
  apply (drule_tac x="ia" in bspec, simp)
  apply (fast)

  (* sub 1 *)
  apply (blast)
  done




lemma ex_NonTockRequest_if_isNonTockDeadlockStateOf_NonTockBusyNetwork :
    "(t, Yf) isNonTockDeadlockStateOf (I, FXf) ==>
     NonTockBusyNetwork (I, FXf) ==> 
     i : I ==> ~ Ev ` snd (FXf i) <= {Tock} ==>
     EX j. (I, FXf) >> i --[(t, Yf)]--> j"
  apply (frule isStateOf_if_isNonTockDeadlockStateOf)

  apply (rule ex_target_for_NonTockRequest_nonTock_refusals, simp_all)

  (* refusing ALL events *)
  apply (frule Union_refusals_ALP_if_isNonTockDeadlockStateOf, simp add: ALP_def)

  (* NonTock busy --> i is time-stop-free *)
  apply (simp only: NonTockBusyNetwork_def)

  (* State of i *)
  apply (drule_tac x="i" in bspec, simp)
  apply (drule_tac x="(t rest-tr (snd (FXf i)), Yf)" in spec)

  apply (simp add: isNonTockDeadlockStateOf_def)
  apply (drule mp, simp add: isStateOf_each_element)

  apply (simp only: refusesAllNonTock_def refusesNonTock_def)
  apply (simp add: ALP_def)
  done



end