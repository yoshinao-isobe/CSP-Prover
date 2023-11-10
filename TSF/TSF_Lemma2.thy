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

theory TSF_Lemma2
imports TSF_Blocked
begin


text \<open> NonTockDeadlockState \<longleftrightarrow> \<forall> BlockedInNonTock \<close>

text \<open> For Lemma 2 in Jesus and Sampaio's SBMF 2022 paper
       see Lemma2_Jesus_Sampaio_2022 at the end of this file.
       For Lemma 2 in Jesus and Sampaio's SCP 2023 paper
       see Lemma2_Jesus_Sampaio_2023 at the end of this file. \<close>


(*** only if ***)

lemma BlockedInNonTock_if :
    "[| isTPN (I, FXf) ;
        tock_triple_conjoint (I,FXf) ;
        NonTockBusyNetwork (I,FXf) ;
        (t,Yf) isNonTockDeadlockStateOf (I,FXf) |]
     ==> ALL i:I. (I,FXf) >> i isBlockedInNonTock (t,Yf)"
  (* ALL i *)
  apply (intro ballI)

  (* Refusals are subsets *)
  apply (frule isStateOf_if_isNonTockDeadlockStateOf)
  apply (frule refusals_are_subsets_if_isStateOf, simp)

  apply (simp only: isBlockedInNonTock_def)
  (* tock_triple_conjoint AND ... *)
  apply (rule conjI, simp)
  (* EX request AND
     ALL request IMPLIES ungratedNonTockRequest *)
  apply (rule conjI)

  (* EX request FROM i TO j *)
  apply (rule ex_NonTockRequest_if_isNonTockDeadlockStateOf_NonTockBusyNetwork, simp_all)

  (* ALL j *)
  apply (intro allI impI)

  (* ALL NonTock Requests FROM i TO j ARE Ungrated
     AND communication FROM i and j ARE in the Vocabulary *)
  apply (unfold isUngrantedNonTockRequestOfwrt_def)

  apply (intro conjI)

  (* 1 *)
  (* ALL NonTock Requests FROM i TO j ARE Ungrated *)
  apply (simp add: isUngrantedNonTockRequestOf_def)

    apply (rule)
    (* x is a refusal *)
    apply (simp add: hasNonTockRequestFor_def)
    apply (simp add: isRequestOf_def, elim conjE)

    (* "Creates" the third index ia *)
    apply (subgoal_tac "x : refusalSet(I,FXf)<Yf>")
    apply (simp add: refusalSet_def)
    apply (elim conjE exE, simp)

    apply (case_tac "ia = i", simp)
    apply (case_tac "ia = j", simp)
    (* ia ~= i & ia ~= j ==> contradict with tock_triple_conjoint *)
    apply (simp add: tock_triple_conjoint_def)
    apply (blast)
    
    apply (rule_tac i=i and j=j in in_refusals_if_isNonTockDeadlockStateOf[of t Yf I FXf])
      apply (simp, simp, simp, simp, simp)

  (* 2 *)
  (* ALL communication FROM i and j ARE in the Vocabulary *)
  apply (rule)

  apply (simp add: isNonTockDeadlockStateOf_def)
    apply (simp add: refusesAllNonTockEv_def)

  apply (simp add: subset_eq)
  apply (simp add: hasNonTockRequestFor_def)
  apply (simp add: isRequestOf_def)
  apply (elim conjE)

  apply (case_tac "x = Tock", simp)
    apply (simp add: Tock_in_Ev_VocabularyOf)
    apply (elim disjE)
      apply (simp add: NonTock_in_Ev_VocabularyOf)
      apply (simp add: NonTock_in_Ev_VocabularyOf)
done

lemmas Lemma2_Jesus_Sampaio_2022_only_if = BlockedInNonTock_if


(*** if ***)


lemma NonTockDeadlockState_if :
    "[| tock_triple_conjoint (I,FXf) ; NonTockBusyNetwork (I,FXf) ;
        (t, Yf) isStateOf (I, FXf) ;
        ALL i:I. (I,FXf) >> i isBlockedInNonTock (t,Yf) |]
     ==> (t,Yf) isNonTockDeadlockStateOf (I,FXf)"

  apply (simp add: isNonTockDeadlockStateOf_def)
  apply (simp add: refusesAllNonTockEv_def)

  (* ALP - {Tock} <= netRefusals *)
  apply (rule)
  apply (simp, elim conjE)

  (* an event x (~= Tock) from the net ALP is being refused *)
  apply (case_tac "EX i:I. x : Yf i")
  apply (elim bexE, simp add: in_refusalSet)

  (* ~ EX i:I. x : Yf i *)
  apply (simp add: image_iff, elim bexE)
  apply (simp only: ALP_def)
  apply (drule CollectD)
  apply (elim bexE)
  apply (rename_tac e ev i)

  apply (simp add: refusalSet_def)

  apply (frule_tac ev="ev" in in_VocabularyOf_I, simp_all, fast)
  apply (drule in_VocabularyOf_D)
  apply (elim conjE exE bexE)

  apply (drule_tac x="i" in bspec, simp)
  apply (simp only: isBlockedInNonTock_def)
  apply (simp add: isUngrantedNonTockRequestOfwrt_def)
  apply (simp add: isUngrantedNonTockRequestOf_def)
  apply (simp add: hasNonTockRequestFor_def)
  apply (simp add: isRequestOf_def)
  apply (elim conjE exE)

    (* j refuses x *)
    apply (case_tac "ia = i")
    apply (simp)
    apply (rule_tac x="Yf j" in exI)
    apply (rule conjI, fast)
    apply (drule_tac x="j" in spec)
    apply (drule mp, simp)
    apply (fast)
    apply (fast)

    apply (case_tac "j = i")
    apply (simp)
    apply (rule_tac x="Yf ia" in exI)
    apply (rule conjI, fast)
    apply (drule_tac x="ia" in spec)
    apply (drule mp, simp)
    apply (fast)
    apply (fast)

    (* ia ~= i; j ~= i; ia ~= j, but xa : snd (PXf i), ... *)
    apply (simp add: tock_triple_conjoint_def)
    apply (drule_tac x="i" in bspec, simp)
    apply (rotate_tac -1)
    apply (drule_tac x="ia" in bspec, simp)
    apply (rotate_tac -1)
    apply (drule_tac x="j" in bspec, simp)
    apply (fast)
  done

lemmas Lemma2_Jesus_Sampaio_2022_if = NonTockDeadlockState_if


lemma NonTockBlockedNetwork_iff :
    "[| isTPN (I, FXf) ;
        tock_triple_conjoint (I,FXf) ; NonTockBusyNetwork (I,FXf) ;
        (t,Yf) isStateOf (I,FXf) |]
     ==> (t,Yf) isNonTockDeadlockStateOf (I,FXf)
         = (ALL i:I. (I,FXf) >> i isBlockedInNonTock (t,Yf))"
  apply (rule)
  apply (simp add: BlockedInNonTock_if)
  apply (simp add: NonTockDeadlockState_if)
  done


lemmas Lemma2_Jesus_Sampaio_2022 = NonTockBlockedNetwork_iff

lemmas Lemma2_Jesus_Sampaio_2023 = Lemma2_Jesus_Sampaio_2022

end