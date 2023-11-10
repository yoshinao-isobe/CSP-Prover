           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 2022 / 2023               |
            |                                           |
            |          Lemmas and Theorems from         |
            |    Jesus and Sampaio's SBMF 2022 paper    |
            |                     and                   |
            |    Jesus and Sampaio's SCP 2023 paper     |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

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

definition
  hasTockRequestFor :: "('i,'e) NetworkF => 'i => ('i,'e::tockCSP) net_state => 'i => bool"
     ("(1_ >> /(0_ (1/--[_]tock-->) /_))" [800, 800,100,800] 900)
  where
  hasTockRequestFor_def :
    "VF >> i --[sigma]tock--> j ==
        VF >> i --[sigma]--> j &
        Tock ~: (snd sigma) i"



definition hasUngrantedTockRequestFor ::
     "('i,'e) NetworkF => 'i => ('i,'e::tockCSP) net_state => 'i => bool"
      ("(1_ >> /(0_ (1/--[_]tock-->o) /_))" [800, 800,0,800] 900)
where
    "VF >> i --[sigma]tock-->o j ==
        VF >> i --[sigma]tock--> j &
        Tock : (snd sigma) j"


definition hasUngrantedTockRequestForwrt ::
     "('i,'e) NetworkF => 'i => ('i,'e) net_state => 'e::tockCSP set => 'i => bool"
      ("(1_ >> /(0_ (1/--[(0_,/_)]tock-->o) /_))" [800, 800,0,0,800] 900)
where
    "VF >> i --[sigma,Lambda]tock-->o j ==
        VF >> i --[sigma]tock-->o j &
        (((Ev ` (snd (snd VF i))) - (snd sigma) i) Un
         ((Ev ` (snd (snd VF j))) - (snd sigma) j)) <= Ev ` Lambda"





definition
  hasNonTockRequestFor :: "('i,'e) NetworkF => 'i => ('i,'e::tockCSP) net_state => 'i => bool"
     ("(1_ >> /(0_ (1/--tock[_]-->) /_))" [800, 800,100,800] 900)
  where
  hasNonTockRequestFor_def :
    "VF >> i --tock[sigma]--> j ==
        VF >> i --[sigma]--> j &
        (Ev ` (snd (snd VF i)) - (snd sigma) i) Int Ev ` (snd (snd VF j)) \<noteq> {Tock}"


definition isUngrantedNonTockRequestOf ::
     "('i,'e) NetworkF => 'i => ('i,'e::tockCSP) net_state => 'i => bool"
      ("(1_ >> /(0_ (1/--tock[_]-->o) /_))" [800, 800,0,800] 900)
where
    "VF >> i --tock[sigma]-->o j ==
        VF >> i --tock[sigma]--> j &
        Ev ` (snd (snd VF i)) Int Ev ` (snd (snd VF j)) - {Tock}
        <= (snd sigma) i Un (snd sigma) j"


definition isUngrantedNonTockRequestOfwrt ::
     "('i,'e) NetworkF => 'i => ('i,'e) net_state => 'e::tockCSP set => 'i => bool"
      ("(1_ >> /(0_ (1/--tock[(0_,/_)]-->o) /_))" [800, 800,0,0,800] 900)
where
    "VF >> i --tock[sigma,Lambda]-->o j ==
        VF >> i --tock[sigma]-->o j &
        (((Ev ` (snd (snd VF i))) - (snd sigma) i) Un
         ((Ev ` (snd (snd VF j))) - (snd sigma) j)) <= Ev ` Lambda"
(*
         ((Ev ` (snd (snd VF j))) - (snd sigma) j)) - {Tock} <= Ev ` Lambda"
*)


subsection \<open> BlockedIn NonTock \<close>


definition  isBlockedInNonTock :: "('i,'e) NetworkF => 'i => ('i,'e::tockCSP) net_state => bool"
      ("(_ >> _ isBlockedInNonTock _)" [800, 800, 800] 900)
where
    "VF >> i isBlockedInNonTock sigma == 
          tock_triple_conjoint VF &
          (EX j. VF >> i --tock[sigma]--> j) &
          (ALL j. VF >> i --tock[sigma]--> j
          --> (VF >> i --tock[sigma, (VocabularyOf VF)]-->o j))"



subsection \<open> BlockedIn Tock \<close>


definition  isBlockedInTock :: "('i,'e) NetworkF => 'i => ('i,'e::tockCSP) net_state => bool"
      ("(_ >> _ isBlockedInTock _)" [800, 800, 800] 900)
where
    "VF >> i isBlockedInTock sigma == 
          tock_triple_conjoint VF &
          (EX j. VF >> i --[sigma]tock--> j) &
          (ALL j. VF >> i --[sigma]tock--> j
           --> (EX j. VF >> i --[sigma, (VocabularyOf VF)]tock-->o j))"





subsection \<open> Lemmas \<close>


subsubsection \<open> tock_triple_conjoint \<close>


lemma tock_triple_conjoint_PXf_FXf :
    "tock_triple_conjoint (I,PXf) ==> (I,FXf) isFailureOf (I,PXf) ==>
     tock_triple_conjoint (I,FXf)"
  apply (simp add: tock_triple_conjoint_def)
  by (simp add: isFailureOf_def)


lemma isTPN_if_tock_triple_conjoint :
    "tock_triple_conjoint VF ==>
     ALL i : fst VF. EX j : fst VF. EX k : fst VF.
     i \<noteq> j \<and> j \<noteq> k \<and> k \<noteq> i ==>
     isTPN VF"
  apply (simp add: tock_triple_conjoint_def)
  apply (simp add: isTPN_def)
  apply (rule)
  apply (drule_tac x=i in bspec, simp)
  apply (drule_tac x=i in bspec, simp)
  by (auto)


subsubsection \<open> ungranted requests --> in index I \<close>

lemma in_index_NonTock_I1:
    "(I, FXf) >> i --tock[sigma]-->o j ==> i : I & j : I & i ~= j"
  apply (simp add: isUngrantedNonTockRequestOf_def)
  apply (simp only: hasNonTockRequestFor_def)
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
  apply (simp add: hasNonTockRequestFor_def)
  apply (rule isRequestOf_subsetI, simp_all)
  done

(*lemma isUngrantedNonTockRequestOf_subsetI:
    "[| (I, FXf) >> i --tock[(t,Yf)]-->o j; J <= I; i:J ; j:J ; 
        X = Union {snd (FXf i)|i. i:J} |]
     ==> (J, FXf) >> i --tock[(t rest-tr X,Yf)]-->o j"
  apply (simp add: isUngrantedNonTockRequestOf_def)
  apply (rule)
  apply (rule isRequestOf_subsetI, simp_all)
  apply (simp add: isTimeStopStateOf_def refusesTock_def, elim conjE)
  apply (rule)
  apply (simp add: isRequestOf_def, elim conjE)

  apply (simp add: Tock_notin_refusalSet_subset)
  done*)


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




subsubsection \<open> isBlockedInTock \<close>


lemma EX_if_ALL_isBlockedInTock :
    "I ~= {} ==>
     ALL i : I. (I, FXf) >> i isBlockedInTock (t, Yf) ==>
     EX i : I. (I, FXf) >> i isBlockedInTock (t, Yf)"
  by (insert ex_in_conv[of I], simp)


(*lemma ALL_if_EX_isBlockedInTock :
    "TockBusyNetwork (I, FXf) ==>
     (t, Yf) isStateOf (I, FXf) ==>
     EX i : I. (I, FXf) >> i isBlockedInTock (t, Yf) ==>
     ALL i : I. (I, FXf) >> i isBlockedInTock (t, Yf)"
  apply (rule, erule bexE)
  apply (simp only: isBlockedInTock_def, elim conjE exE)
  apply (rule, simp)
  apply (rule)

  apply (simp only: hasUngrantedTockRequestForwrt_def)
  apply (simp only: hasUngrantedTockRequestFor_def)
  apply (simp add: hasTockRequestFor_def)
  apply (simp add: isRequestOf_def, elim conjE)
  apply (drule mp, fast)
  apply (elim exE conjE)

  apply (simp add: TockBusyNetwork_def)
  apply (simp add: isUrgentStateOf_def)
  apply (simp add: refusesTock_def)
  apply (drule_tac x=ja in bspec, simp)
  apply (frule_tac i=ja in isStateOf_each_element, simp)
  apply (simp add: refusalSet_def)

  apply (intro allI impI)

  apply (drule_tac x=j in spec)
  apply (drule mp, simp)

  apply (rule_tac x=ja in exI)

  apply (elim exE)

  apply (unfold hasUngrantedTockRequestForwrt_def)
  apply (simp only: hasUngrantedTockRequestFor_def)
  apply (simp add: hasTockRequestFor_def)
  apply (simp add: isRequestOf_def)
  apply (elim conjE)

  apply (simp add: TockBusyNetwork_def)
  apply (simp add: isUrgentStateOf_def)
  apply (simp add: refusesTock_def)

  apply (drule_tac x=jb in bspec, simp)

  apply (simp add: refusalSet_def)
  apply (frule_tac i=jb in isStateOf_each_element, simp_all)
  done

lemma ALL_iff_EX_isBlockedInTock :
    "I ~= {} ==>
     TockBusyNetwork (I, FXf) ==>
     (t, Yf) isStateOf (I, FXf) ==>
     (EX i : I. (I, FXf) >> i isBlockedInTock (t, Yf)) =
     (ALL i : I. (I, FXf) >> i isBlockedInTock (t, Yf))"
  apply (rule)
  apply (rule ALL_if_EX_isBlockedInTock, simp_all)
  by (blast)*)


subsubsection \<open> request intro (NonTockDeadlockState and not TimeStopState) \<close>


lemma ex_target_for_Request_nonTock_refusals :
    "(t, Yf) isNonTockDeadlockStateOf (I, FXf) ==>
     i : I ==>
     ~ (t rest-tr snd (FXf i), Yf) refusesAllNonTockEv ({i}, FXf) ==>
     EX j. (I, FXf) >> i --[(t, Yf)]--> j"
  apply (simp only: isRequestOf_def)

  apply (simp add: isNonTockDeadlockStateOf_def)
  apply (simp add: refusesAllNonTockEv_def)
  apply (simp add: refusalSet_def ALP_def)
  apply (simp add: subset_eq)
  apply (elim bexE conjE)
  apply (simp)

  apply (drule_tac x=x in bspec, fast)
  apply (elim exE conjE, simp)

  apply (case_tac "i = ia", simp)
  apply (rule_tac x="ia" in exI)

  apply (frule refusals_are_subsets_if_isStateOf)
  apply (drule_tac x="ia" in bspec, simp)
  apply (simp)
  apply (blast)
  done



lemma ex_Request_if_isNonTockDeadlockStateOf_NonTockBusyNetwork :
    "NonTockBusyNetwork (I, FXf) ==>
     (t, Yf) isNonTockDeadlockStateOf (I, FXf) ==>
     i : I ==>
     EX j. (I, FXf) >> i --[(t, Yf)]--> j"
  (* NonTock busy --> i is time-stop-free *)
  apply (simp only: NonTockBusyNetwork_def)

  (* State of i *)
  apply (drule_tac x="i" in bspec, simp)
  apply (drule_tac x="(t rest-tr (snd (FXf i)), Yf)" in spec)

  apply (rule ex_target_for_Request_nonTock_refusals, simp_all)
  apply (simp only: isNonTockDeadlockStateOf_def)
  apply (simp add: refusesAllNonTockEv_def)

  apply (elim conjE)
  apply (simp add: isStateOf_each_element)
  done




lemma ex_target_for_NonTockRequest :
    "(t, Yf) isNonTockDeadlockStateOf (I, FXf) ==>
     j : I ==>
     ~ (t rest-tr snd (FXf i), Yf) refusesAllNonTockEv ({j}, FXf) ==>
     EX i. (I, FXf) >> j --tock[(t, Yf)]--> i"
  apply (simp add: hasNonTockRequestFor_def)
  apply (simp add: isRequestOf_def)
  apply (rule conjI)

  apply (simp add: isNonTockDeadlockStateOf_def)
  apply (simp add: isNonTockDeadlockStateOf_def)
  apply (simp add: refusesAllNonTockEv_def)
  apply (simp add: refusalSet_def ALP_def)
  apply (simp add: subset_eq)
  apply (elim bexE conjE)
  apply (simp)

  apply (drule_tac x=x in bspec, fast)
  apply (elim exE conjE, simp)

  apply (case_tac "j = i", simp)
  apply (rule_tac x="i" in exI)

  apply (frule refusals_are_subsets_if_isStateOf)
  apply (drule_tac x="i" in bspec, simp)
  apply (simp)
  apply (blast)
  done


lemma ex_NonTockRequest_if_isNonTockDeadlockStateOf_NonTockBusyNetwork :
    "NonTockBusyNetwork (I, FXf) ==>
     (t, Yf) isNonTockDeadlockStateOf (I, FXf) ==>
     j : I ==>
     EX i. (I, FXf) >> j --tock[(t, Yf)]--> i"
  (* NonTock busy --> i is time-stop-free *)
  apply (simp only: NonTockBusyNetwork_def)

  (* State of i *)
  apply (drule_tac x="j" in bspec, simp)
  apply (drule_tac x="(t rest-tr (snd (FXf j)), Yf)" in spec)

  apply (rule ex_target_for_NonTockRequest, simp_all)
  apply (simp only: isNonTockDeadlockStateOf_def)
  apply (simp add: refusesAllNonTockEv_def)

  apply (elim conjE)
  apply (simp add: isStateOf_each_element)
  done


(*
lemma ex_target_for_Request_nonTock_refusals :
    "(t, Yf) isNonTockDeadlockStateOf (I, FXf) ==>
     ~ (t, Yf) isTimeStopStateOf (I, FXf) ==>
     i : I ==>
     Yf i ~= Ev ` snd (FXf i) - {Tock} ==>
     EX j. (I, FXf) >> i --[(t, Yf)]--> j"
  apply (simp only: isRequestOf_def)

  apply (frule isStateOf_if_isNonTockDeadlockStateOf)
  apply (frule refusals_are_subsets_if_isStateOf)

  apply (frule Union_refusals_eq_ALP_diff_Tock_if_isNonTockDeadlockStateOf, simp)

  apply (frule refusals_are_subsetsNonTock_if_not_isTimeStopStateOf, simp)

  (* i is not refusing event a from its synchronisation set *)
  apply (frule ex_non_refused_nonTock_event_if_not_isTimeStopStateOf, simp_all)
  apply (simp_all, elim bexE)

  apply (frule in_ALP_Diff_Tock, simp, simp, simp)

  apply (rotate_tac 1)
  apply (drule sym)
  apply (simp add: image_iff refusalSet_def)
  apply (elim conjE exE)
  apply (simp)
  apply (rule_tac x="ia" in exI)
  apply (case_tac "i = ia", simp)
  apply (simp)
  apply (drule_tac x="ia" in bspec, simp)
  apply (blast)
  done


lemma ex_Request_if_isNonTockDeadlockStateOf_NonTockBusyNetwork1 :
    "NonTockBusyNetwork (I, FXf) ==>
     (t, Yf) isNonTockDeadlockStateOf (I, FXf) ==>
     ~ (t, Yf) isTimeStopStateOf (I, FXf) ==>
     i : I ==>
     ~ Ev ` snd (FXf i) <= {Tock} ==>
     EX j. (I, FXf) >> i --[(t, Yf)]--> j"
  apply (frule isStateOf_if_isNonTockDeadlockStateOf)

  apply (rule ex_target_for_Request_nonTock_refusals, simp_all)

  (* refusing ALL events *)
  apply (frule Union_refusals_eq_ALP_diff_Tock_if_isNonTockDeadlockStateOf)
    apply (simp)

  (* NonTock busy --> i is time-stop-free *)
  apply (simp only: NonTockBusyNetwork_def)

  (* State of i *)
  apply (drule_tac x="i" in bspec, simp)
  apply (drule_tac x="(t rest-tr (snd (FXf i)), Yf)" in spec)

  apply (simp only: isNonTockDeadlockStateOf_def)
  apply (simp add: refusesAllNonTock_def)
  apply (simp add: isStateOf_each_element)
  apply (simp add: ALP_def refusalSet_def)
  apply (blast)
  done


lemma ex_Request_if_isNonTockDeadlockStateOf_NonTockBusyNetwork2 :
    "NonTockBusyNetwork (I, FXf) ==>
     (t, Yf) isNonTockDeadlockStateOf (I, FXf) ==>
     ~ (t, Yf) isTimeStopStateOf (I, FXf) ==>
     i : I ==>
     ~ Yf i <= {Tock} ==>
     EX j. (I, FXf) >> i --[(t, Yf)]--> j"
  apply (rule ex_Request_if_isNonTockDeadlockStateOf_NonTockBusyNetwork1, simp_all)
  apply (frule isStateOf_if_isNonTockDeadlockStateOf)
  apply (simp add: not_alpha_subset_Tock_if_not_refusals_subset_Tock)

  (*(* State of i *)
  apply (frule not_isTimeStopStateOf_each_element, fast, simp)
  apply (drule_tac x="i" in bspec, simp)
  apply (drule_tac x="(t rest-tr (snd (FXf i)), Yf)" in spec)

  apply (frule refusals_neq_ALP_diff_Tock_if_not_isNonTockDeadlockStateOf, simp_all)*)
  done
*)



subsubsection \<open> Tock Request \<close>


lemma hasTockRequest_sym :
    "isTPN (I, FXf) ==>
     i : I ==> j : I ==>
     Tock ~: Yf i ==>
     Tock ~: Yf j ==>
     ((I, FXf) >> i --[(t, Yf)]tock--> j) = ((I, FXf) >> j --[(t, Yf)]tock--> i)"
  apply (simp add: hasTockRequestFor_def)
  apply (simp add: isRequestOf_def)
  apply (simp add: isTPN_def, blast)
  done


subsubsection \<open> Tock Request intro (TimeStopState) \<close>


lemma ex_target_for_TockRequest_Tock_refusal :
    "isTPN (I, FXf) ==>
     (t, Yf) isUrgentStateOf (I, FXf) ==>
     i : I ==> Tock ~: Yf i ==>
     EX j. (I, FXf) >> i --[(t, Yf)]tock--> j"
  apply (simp only: hasTockRequestFor_def)

  apply (simp add: isRequestOf_def)

  apply (frule isStateOf_if_isUrgentStateOf)
  apply (frule refusals_are_subsets_if_isStateOf)

  apply (simp add: isUrgentStateOf_def)
  apply (simp add: refusesTock_def refusalSet_def)
  apply (elim exE conjE, simp)

  apply (case_tac "i = ia", simp)
  apply (rule_tac x="ia" in exI, simp)
  apply (drule_tac x="ia" in bspec, simp)
  apply (simp add: isTPN_def)
  apply (fast)
  done


lemma ex_TockRequest_if_isUrgentStateOf_TockBusyNetwork :
    "(t, Yf) isUrgentStateOf (I, FXf) ==>
     isTPN (I, FXf) ==>
     TockBusyNetwork (I, FXf) ==>
     i : I ==>
     EX j. (I, FXf) >> i --[(t, Yf)]tock--> j"
  apply (frule isStateOf_if_isUrgentStateOf)

  apply (rule ex_target_for_TockRequest_Tock_refusal, simp_all)

  (* Tock busy --> i is time-stop-free *)
  apply (simp only: TockBusyNetwork_def)

  (* State of i *)
  apply (drule_tac x="i" in bspec, simp)
  apply (drule_tac x="(t rest-tr (snd (FXf i)), Yf)" in spec)
  apply (simp)

  apply (simp add: isUrgentStateOf_def)
  apply (simp add: isStateOf_each_element)
  apply (simp add: refusesTock_def)
  apply (simp add: refusalSet_def)
  done




lemma all_target_for_TockRequest_Tock_refusal :
    "isTPN (I, FXf) ==>
     (t, Yf) isUrgentStateOf (I, FXf) ==>
     i : I ==> Tock ~: Yf i ==>
     ALL j:I. j ~= i --> (I, FXf) >> i --[(t, Yf)]tock--> j"
  apply (simp only: hasTockRequestFor_def)
  apply (simp add: isRequestOf_def)

  apply (frule isStateOf_if_isUrgentStateOf)
  apply (frule refusals_are_subsets_if_isStateOf)

  apply (simp add: isTPN_def)
  apply (fast)
  done


lemma all_TockRequest_if_isTimeStopStateOf_TockBusyNetwork :
    "(t, Yf) isUrgentStateOf (I, FXf) ==>
     isTPN (I, FXf) ==>
     TockBusyNetwork (I, FXf) ==>
     i : I ==>
     ALL j:I. j ~= i --> (I, FXf) >> i --[(t, Yf)]tock--> j"
  apply (frule isStateOf_if_isUrgentStateOf)

  apply (rule all_target_for_TockRequest_Tock_refusal, simp_all)

  (* Tock busy --> i is time-stop-free *)
  apply (simp only: TockBusyNetwork_def)

  (* State of i *)
  apply (drule_tac x="i" in bspec, simp)
  apply (drule_tac x="(t rest-tr (snd (FXf i)), Yf)" in spec)
  apply (simp)

  apply (simp only: isUrgentStateOf_def)
  apply (simp add: isStateOf_each_element)
  apply (simp add: refusesTock_def refusalSet_def)
  done



subsubsection \<open> Vocabulary \<close>




lemma in_VocabularyOf_I :
     "ALL i:I. (I, FXf) >> i isBlockedInNonTock (t, Yf) ==>
      ev ~= tock ==>
      e = Ev ev ==>
      i : I ==>
      ev : snd (FXf i) ==>
      Ev ev ~: Yf i ==> ev : VocabularyOf (I,FXf) - {tock}"
  apply (simp only: isBlockedInNonTock_def)
  apply (simp add: VocabularyOf_def)
  apply (drule_tac x="i" in bspec, simp)
  apply (elim exE conjE)
  apply (drule_tac x="j" in spec)
  apply (simp add: isUngrantedNonTockRequestOfwrt_def, elim conjE)
  apply (blast)
  done

lemma in_VocabularyOf_D :
    "ev : VocabularyOf (I, FXf) ==>
     EX x. (EX i:I. EX j:I. i ~= j & x = snd (FXf i) Int snd (FXf j)) & ev : x"
  by (simp add: VocabularyOf_def)


lemma Tock_in_Ev_VocabularyOf :
    "isTPN (I, FXf) \<Longrightarrow>
     i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow>
     Tock \<in> Ev ` VocabularyOf (I, FXf)"
  apply (simp add: isTPN_def VocabularyOf_def)
  apply (blast)
done

(*lemma tock_in_VocabularyOf :
     "isTPN (I, FXf) ==>
      i : I ==> (I, FXf) >> i --[(t, Yf)]--> j ==>
      tock : VocabularyOf (I, FXf)"
  apply (simp add: VocabularyOf_def)
  apply (simp add: isTPN_def isRequestOf_def)
  apply (frule_tac x=i in bspec, simp)
  by (rule_tac x="snd (FXf i) \<inter> snd (FXf j)" in exI, fast)*)


lemma NonTock_in_Ev_VocabularyOf :
    "(t, Yf) isStateOf (I, FXf) \<Longrightarrow>
     i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow>
     \<forall>x\<in>NonTockEvALP (I, FXf). x \<in> refusalSet (I, FXf)<Yf> \<Longrightarrow>
     \<forall>i\<in>I. \<forall>x\<in>Yf i. x \<in> Ev ` snd (FXf i) \<Longrightarrow>
     x \<in> Ev ` snd (FXf i) \<and> x \<notin> Yf i \<Longrightarrow>
     x \<noteq> Tock \<Longrightarrow>
     x \<in> Ev ` VocabularyOf (I, FXf) "
  apply (simp add: VocabularyOf_def)

  apply (subgoal_tac "x : (refusalSet(I,FXf)<Yf>) - {Tock}")
  apply (simp add: ALP_def)

  apply (simp add: refusalSet_def)
  apply (elim conjE bexE exE)

   apply (simp add: image_iff)
   apply (elim disjE conjE bexE)

    apply (case_tac "i = ia", simp)
    apply (drule_tac x="ia" in bspec, simp)
    apply (simp add: isStateOf_def)
    apply (rule_tac x="snd (FXf i) Int snd (FXf ia)" in exI)
    apply (rule conjI)
     apply (rule_tac x="i" in bexI)
     apply (rule_tac x="ia" in bexI)
     apply (simp)
     apply (simp)
     apply (simp)
     apply (blast)

  apply (simp)
  apply (frule_tac x="x" in bspec, simp)
  apply (simp add: ALP_def)
  apply (blast)

  apply (simp)
  done


end