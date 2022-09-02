theory TSF_Lemma2
imports TSF_Blocked
begin


subsection \<open> Lemma 2 \<close>


(*** only if ***)

lemma Lemma2_Jesus_Sampaio_2022_only_if:
    "[| tock_triple_conjoint (I,FXf) ; NonTockBusyNetwork (I,FXf) ;
        (t,Yf) isNonTockDeadlockStateOf (I,FXf) ;
        ALL i:I. ~ Ev ` snd (FXf i) <= {Tock} |]
     ==> ALL i:I. (I,FXf) >> i isBlockedInNonTock (t,Yf)"
  (* ALL i *)
  apply (intro ballI)

  (* Refusals are subsets *)
  apply (frule isStateOf_if_isNonTockDeadlockStateOf)
  apply (frule refusals_are_subsets_if_isStateOf, simp)
  apply (frule refusals_are_subsetsNonTock_if_isNonTockDeadlockStateOf)

  apply (simp only: isBlockedInNonTock_def)
    (* tock_triple_conjoint AND ... *)
    apply (rule conjI, simp)
    (* EX request AND
       ALL request IMPLIES ungratedNonTockRequest *)
    apply (rule conjI)

    (* EX nonTockRequest FROM i TO j *)
    apply (rule ex_NonTockRequest_if_isNonTockDeadlockStateOf_NonTockBusyNetwork, simp_all)

    (* ALL j *)
    apply (intro allI impI)

    (* ALL request FROM i TO j ARE Ungrated NonTock Requests *)
    apply (unfold isUngrantedNonTockRequestOfwrt_def)

    apply (rule conjI)

    (* 1-2 *)
    apply (simp add: isUngrantedNonTockRequestOf_def)
    apply (frule not_isTimeStopStateOf_if_isNonTockDeadlockStateOf, simp)

    (* Request FROM i TO j *)
    apply (simp add: isRequestOf_def)

    (* alpha i INT alpha j SUBSET Un refusals *)
    apply (rule)
    (* x is a refusal *)

    (* "Creates" the third index ia *)
    apply (subgoal_tac "x : (netRefusals I Yf)")

     apply (simp)
     apply (elim conjE bexE exE)
     apply (case_tac "ia = i", simp)
     apply (case_tac "ia = j", simp)
     (* ia ~= i & ia ~= j ==> contradict with tock_triple_conjoint *)
     apply (simp add: tock_triple_conjoint_def)
     apply (blast)

     apply (rule_tac i=i and j=j in in_refusals_if_isNonTockDeadlockStateOf[of t Yf I FXf])
       apply (simp, simp, simp, simp, simp)

     (* 2-2 *)
     apply (rule)
     apply (simp only: VocabularyOf_def)
     apply (subgoal_tac "x : netRefusals I Yf")

     apply (simp)
     apply (elim conjE bexE exE)
     apply (simp add: image_iff)
     apply (elim disjE conjE bexE)

      apply (case_tac "i = ia", simp)
      apply (drule_tac x="ia" in bspec, simp)
      apply (simp add: isStateOf_def)
        apply (rule_tac x="(snd (FXf i) Int snd (FXf ia))" in exI, blast)

      apply (case_tac "j = ia", simp)
      apply (drule_tac x="ia" in bspec, simp)
      apply (simp only: isRequestOf_def, elim conjE)
      apply (simp add: isStateOf_def)
        apply (rule_tac x="snd (FXf j) Int snd (FXf ia)" in exI, blast)

      apply (simp only: isRequestOf_def)
      apply (simp add: isNonTockDeadlockStateOf_def)
      apply (simp add: refusesAllNonTock_def refusesNonTock_def)
      apply (simp add: subset_singleton_iff)
      apply (simp add: Diff_eq Int_def ALP_def)
      apply (elim conjE)
      apply (simp only: Union_eq set_eq_iff)
      apply (drule_tac x="x" in spec, simp)
      apply (erule disjE, fast, fast)
  done



(*** if ***)



(* ALL synchronisation sets are Tock \<union> X where X \<noteq> {} *)
lemma Lemma2_Jesus_Sampaio_2022_if:
    "[| tock_triple_conjoint (I,FXf) ; NonTockBusyNetwork (I,FXf) ;
        (t, Yf) isStateOf (I, FXf) ; 
        ALL i:I. (I,FXf) >> i isBlockedInNonTock (t,Yf) ;
        ALL i:I. ~ Ev ` snd (FXf i) <= {Tock} |]
     ==> (t,Yf) isNonTockDeadlockStateOf (I,FXf)"

  apply (simp add: isNonTockDeadlockStateOf_def)
  apply (simp add: refusesAllNonTock_def)

  apply (rule)

  (* <= *) (* netRefusals <= ALP - {Tock} *)
  (*apply (insert ex_in_conv[of I], simp, elim exE)
  apply (rename_tac i)*)
  apply (rule)
  apply (rule)
    apply (simp add: isStateOf_def ALP_def, elim conjE, fast)
    apply (simp)
    apply (elim exE conjE)
    apply (simp)
    apply (drule_tac x="i" in bspec, simp)
    apply (drule_tac x="i" in bspec, simp only:)
    apply (simp only: isBlockedInNonTock_def, elim conjE exE)
    apply (drule_tac x=j in spec, simp)
    apply (simp add: isUngrantedNonTockRequestOfwrt_def)
    apply (simp add: isUngrantedNonTockRequestOf_def)
    apply (simp add: isTimeStopStateOf_def refusesTock_def)
    apply (simp add: isStateOf_def ALP_def, elim conjE, blast)

  (* => *) (* ALP - {Tock} <= netRefusals *)
  apply (rule)
  apply (simp)
  (* an event x (~= Tock) from the net ALP is being refused *)
  apply (simp only: isBlockedInNonTock_def)
    apply (simp only: image_iff ALP_def)
    apply (elim conjE exE bexE)
    apply (drule CollectD)
    apply (elim bexE)
    apply (rename_tac e ev i)
  
    apply (case_tac "Ev ev : Yf i")
    apply (rule_tac x="Yf i" in exI)
    apply (simp, fast)

    (* Ev ev ~: Yf i *)
    apply (subgoal_tac "ev : VocabularyOf (I,FXf) - {tock}")

    apply (simp add: VocabularyOf_def)
    apply (elim conjE exE bexE)
    apply (simp)
    
    apply (case_tac "ia = i")
    apply (simp)
    apply (drule_tac x="i" in bspec, simp)
    apply (elim conjE exE)

    apply (drule_tac x="j" in spec)
    apply (drule mp)
    apply (simp add: isRequestOf_def)
    apply (blast)

    apply (simp add: isUngrantedNonTockRequestOfwrt_def)
    apply (simp add: isUngrantedNonTockRequestOf_def)
    apply (rule_tac x="Yf j" in exI)
    apply (fast)

   apply (case_tac "j = i")
    apply (simp)
    apply (drule_tac x="i" in bspec, simp)
    apply (elim conjE exE)
     apply (drule_tac x="ia" in spec)
     apply (drule mp)
     apply (simp add: isRequestOf_def)
     apply (blast)

     apply (simp add: isUngrantedNonTockRequestOfwrt_def)
     apply (simp add: isUngrantedNonTockRequestOf_def)
     apply (rule_tac x="Yf ia" in exI)
     apply (fast)

    (* ia ~= i; j ~= i; ia ~= j, but xa : snd (PXf i), ... *)
    apply (simp add: tock_triple_conjoint_def)
    apply (drule_tac x="i" in bspec, simp)
    apply (rotate_tac -1)
    apply (drule_tac x="ia" in bspec, simp)
    apply (rotate_tac -1)
    apply (drule_tac x="j" in bspec, simp)
    apply (fast)

    apply (simp add: VocabularyOf_def)
    apply (drule_tac x="i" in bspec, simp)
    apply (elim exE conjE)
    apply (drule_tac x="x" in spec)
    apply (simp add: isUngrantedNonTockRequestOfwrt_def, elim conjE)
    apply (blast)
done


lemma Lemma2_Jesus_Sampaio_2022:
    "[| tock_triple_conjoint (I,FXf) ; NonTockBusyNetwork (I,FXf) ;
        (t,Yf) isStateOf (I,FXf) ; 
        ALL i:I. ~ Ev ` snd (FXf i) <= {Tock} |]
     ==> (t,Yf) isNonTockDeadlockStateOf (I,FXf)
         = (ALL i:I. (I,FXf) >> i isBlockedInNonTock (t,Yf))"
  apply (rule)
  apply (simp add: Lemma2_Jesus_Sampaio_2022_only_if)
  apply (simp add: Lemma2_Jesus_Sampaio_2022_if)
  done

end