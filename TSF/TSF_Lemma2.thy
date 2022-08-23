theory TSF_Lemma2
imports TSF_Blocked
begin


subsection \<open> Lemma 2 \<close>


(*** only if ***)
lemma Lemma2_Jesus_Sampaio_2022_only_if:
    "[| tock_triple_conjoint (I,FXf) ; BusyNetwork (I,FXf) ;
        (t,Yf) isNonTockDeadlockStateOf (I,FXf) |]
     ==> ALL i:I. (I,FXf) >> i isBlockedInNonTock (t,Yf)"
  (* ALL i *)
  apply (intro ballI)

  (* Refusals are subsets *)
  apply (frule refusals_are_subsets_if_isNonTockDeadlockStateOf)

  apply (simp only: isBlockedInNonTock_def)
    (* tock_triple_conjoint AND ... *)
    apply (rule conjI, simp)
    (* EX nonTockRequest AND
       ALL nontockRequest IMPLIES ungratedNonTockRequest *)
    apply (rule conjI)

  (* EX nonTockRequest FROM i TO j *)
    apply (frule isDeadlockStateOf_if_isNonTockDeadlockStateOf)
    apply (rule ex_Request_if_isDeadlockStateOf_BusyNetwork, simp_all)

  (* ALL j *)
    apply (intro allI impI)

    (* ALL nontockRequest FROM i TO j IMPLIES ungratedNonTockRequest FROM i TO j *)
    apply (unfold isUngrantedNonTockRequestOfwrt_def)

    apply (rule conjI)
      apply (simp add: isUngrantedNonTockRequestOf_def)
      apply (frule not_isTimeStopStateOf_if_isNonTockDeadlockStateOf, simp)

      (* Request FROM i TO j *)
      apply (simp add: isRequestOf_def)

      (* alpha i INT alpha j SUBSET Un refusals *)
      apply (rule)
      (* x is a refusal *)
      (* "Creates" the third index ia *)
      apply (subgoal_tac "x : Union {Yf i |i. i : I}")

       apply (simp)
       apply (elim conjE bexE exE)
       apply (case_tac "ia = i", simp)
       apply (case_tac "ia = j", simp)
       (* ia ~= i & ia ~= j ==> contradict with tock_triple_conjoint *)
       apply (drule_tac x="ia" in bspec, simp)
       apply (simp add: isDeadlockStateOf_def isStateOf_def)
       apply (simp add: tock_triple_conjoint_def)
       apply (drule_tac x="i" in bspec, simp)
       apply (drule_tac x="j" in bspec, simp)
       apply (drule_tac x="ia" in bspec, simp)
        apply (drule mp)
        apply (simp)
       apply (rotate_tac 5)
       apply (erule contrapos_pp)
       apply (blast)

       apply (rule_tac i=i and j=j in in_refusals_if_isNonTockDeadlockStateOf[of t Yf I FXf])
         apply (simp, simp, simp, simp, simp)

     (* 2-2 *)
      apply (rule)
      apply (simp only: VocabularyOf_def)
      apply (subgoal_tac "x : Union {Yf i |i. i : I}")

       apply (simp)
       apply (elim conjE bexE exE)
       apply (simp add: image_iff)
       apply (elim disjE conjE bexE)

        apply (case_tac "i = ia", simp)
        apply (drule_tac x="ia" in bspec, simp)
        apply (simp add: isStateOf_def)
        apply (rule)
        apply (rule_tac x="(snd (FXf i) Int snd (FXf ia))" in exI)
        apply (rule conjI)
         apply (rule_tac x="i" in bexI)
         apply (rule_tac x="ia" in bexI)
         apply (simp)
         apply (simp)
         apply (simp)
         apply (blast)

        apply (rule tock_notin_refusals_if_isNonTockDeadlockStateOf2, simp, simp, simp)

        apply (case_tac "j = ia", simp)
        apply (drule_tac x="ia" in bspec, simp)
        apply (simp only: isRequestOf_def, elim conjE)
        apply (simp add: isStateOf_def)
        apply (rule)
        apply (rule_tac x="snd (FXf j) Int snd (FXf ia)" in exI)
        apply (rule conjI)
         apply (rule_tac x="j" in bexI)
         apply (rule_tac x="ia" in bexI)
         apply (simp)
         apply (simp)
         apply (simp add: isRequestOf_def)
         apply (blast)

        apply (rule tock_notin_refusals_if_isNonTockDeadlockStateOf2, simp, simp, simp)

  apply (simp only: Un_iff isNonTockDeadlockStateOf_def)
  apply (simp only: isDeadlockStateOf_def)
  apply (simp add: isDeadlockStateOf_def)
  apply (simp add: ALP_def)

  apply (simp add: image_iff)
  apply (elim disjE conjE bexE)

   apply (rule_tac x="xa" in exI)
   apply (simp)
   apply (fast)

   apply (rule_tac x="xa" in exI)
   apply (simp)
   apply (rule_tac x="j" in bexI)
   apply (simp)
   apply (simp add: isRequestOf_def)
  done



(*** if ***)

lemma Lemma2_Jesus_Sampaio_2022_if:
    "[| tock_triple_conjoint (I,FXf) ; BusyNetwork (I,FXf) ;
        (t,Yf) isStateOf (I,FXf) ;
        ALL i:I. (I,FXf) >> i isBlockedInNonTock (t,Yf) |]
     ==> (t,Yf) isNonTockDeadlockStateOf (I,FXf)"
  apply (simp add: isNonTockDeadlockStateOf_def)
  apply (rule)
  apply (simp add: isDeadlockStateOf_def)
  apply (simp add: ALP_def)
  apply (rule)
  
   (* <= *)
   apply (rule)
   apply (simp)
   apply (elim exE conjE)
   apply (simp)
   apply (drule_tac x="i" in bspec, simp)
   apply (simp add: isStateOf_def)
   apply (elim conjE)
   apply (drule_tac x="i" in bspec, simp)
   apply (simp add: ALP_def)
   apply (force)

   (* => *)
   apply (rule)
   apply (simp)
   apply (simp only: isBlockedInNonTock_def)
   apply (simp add: image_iff)
   apply (elim conjE exE bexE)
   apply (simp)
   
   apply (case_tac "Ev xa : Yf i")
    apply (rule_tac x="Yf i" in exI)
    apply (fast)
  
   (* Ev xa ~: Yf i *)
    apply (subgoal_tac "xa : VocabularyOf (I,FXf) - {tock}")
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
      apply (simp only: isTimeStopStateOf_def de_Morgan_conj)
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
       apply (simp only: isTimeStopStateOf_def de_Morgan_conj)
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


    (* xa : VocabularyOf VF - {tock} *)
     apply (simp, rule)

     apply (drule_tac x="i" in bspec, simp)
     apply (elim exE conjE)
     apply (drule_tac x="xb" in spec)
     apply (simp add: isUngrantedNonTockRequestOfwrt_def)
     apply (simp add: isUngrantedNonTockRequestOf_def)
     apply (fast)

     apply (drule_tac x="i" in bspec, simp)
     apply (elim exE conjE)
     apply (drule_tac x="xb" in spec, simp)
     apply (simp add: isUngrantedNonTockRequestOfwrt_def)
     apply (simp add: isUngrantedNonTockRequestOf_def)
     apply (elim conjE)
     apply (frule Tock_notin_refusals_if_not_isTimeStopStateOf, simp)

       apply (simp add: VocabularyOf_def)
       apply (simp only: isRequestOf_def, elim conjE)
       apply (drule_tac x="Yf xb" in spec)
       apply (erule disjE, simp, simp)
       apply (simp add: subset_iff)
       apply (fast)

    (* ~ isTimeStopStateOf *)
       apply (simp only: isBlockedInNonTock_def)
       apply (simp add: isUngrantedNonTockRequestOfwrt_def)
       apply (simp add: isUngrantedNonTockRequestOf_def)
       apply (simp only: isTimeStopStateOf_def de_Morgan_conj)
       apply (rule disjI2, simp)
       apply (fast)
  done


lemma Lemma2_Jesus_Sampaio_2022:
    "[| tock_triple_conjoint (I,FXf) ; BusyNetwork (I,FXf) ; 
        (t,Yf) isStateOf (I,FXf) |]
     ==> (t,Yf) isNonTockDeadlockStateOf (I,FXf)
         = (ALL i:I. (I,FXf) >> i isBlockedInNonTock (t,Yf))"
  apply (rule)
  apply (simp add: Lemma2_Jesus_Sampaio_2022_only_if)
  apply (simp add: Lemma2_Jesus_Sampaio_2022_if)
  done

end