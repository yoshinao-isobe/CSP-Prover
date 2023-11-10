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

theory TSF_Theorem1
imports TSF_law
        TSF_Lemma2
        TSF_Network
begin


subsection \<open> TimeStopFreeNetwork \<close>

text \<open> For Theorem 1 in Jesus and Sampaio's SBMF 2022 paper
       or Theorem 3 in Jesus and Sampaio's SCP 2023 paper
       see Theorem1_Jesus_Sampaio_2022 below.
       For Theorem 1 in Jesus and Sampaio's SCP 2023 paper
       see \<^theory>\<open>DFP.DFP_Hiding\<close>. \<close>


theorem Theorem1_Jesus_Sampaio_2022:
    "[| isTPN (I,PXf) ; I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) ;
        tock_triple_conjoint (I,FXf) ;
        NonTockBusyNetwork (I,FXf) ;
        EX f::('i => 'a::tockCSP failure => ('pi::order)) .
          ALL t Yf. (t,Yf) isStateOf (I,FXf) -->
          (ALL i j. (I,FXf) >> i --tock[(t,Yf), (VocabularyOf (I,FXf))]-->o j
                    --> f j (t rest-tr (snd (FXf j)), Yf j)
                      < f i (t rest-tr (snd (FXf i)), Yf i)) |]
     ==> TimeStopFreeNetwork (I,PXf)"
  apply (subst TimeStopFreeNetwork_iff_notTimeStopState, simp_all)

  (* order function f *)
  apply (elim exE)

  (* by contradiction *)
  apply (case_tac "ALL t Yf. ~ (t, Yf) isTimeStopStateOf (I, FXf)", simp)
  apply (simp)
  apply (elim conjE exE)

  apply (frule isFailureOf_same_TPN)
  apply (frule isStateOf_if_isTimeStopStateOf)

  apply (simp only: isTimeStopStateOf_iff_isNonTockDeadlockStateOf_and_isUrgentStateOf)
  apply (elim conjE)

  (* ALL components are BlockedInNonTock *)
  apply (subst (asm) Lemma2_Jesus_Sampaio_2022, simp_all)

  (* Some component i isBlockedInTock *)
  (*apply (subst (asm) Lemma2b_Jesus_Sampaio_2022, simp_all)
  apply (elim bexE)*)

  (* ASSUME EX MINIMAL j: ALL k:I. f j \<le> f k *)
  apply (subgoal_tac "EX j:I. ALL k:I. ~(f k (t rest-tr (snd (FXf k)), Yf k) 
                                       < f j (t rest-tr (snd (FXf j)), Yf j))")
  apply (elim bexE)

  (* CONSIDER j isBlockedInNonTock *)
  apply (drule_tac x="j" in bspec, simp)

  (* EX k for the non-tock request from j *)
  apply (simp add: isBlockedInNonTock_def)
  apply (elim conjE exE)
  apply (rename_tac k)
  
  (* order f assumption in the state (t,Yf) *)
  apply (drule_tac x="t" in spec)
  apply (drule_tac x="Yf" in spec, simp)

  (* the non-tock request from j to k is ungranted *)
  apply (drule_tac x="k" in spec, simp)

  (* The order f assumption says non-tock requests from j to k implies f k < f j *)
  apply (drule_tac x="j" in spec)
  apply (drule_tac x="k" in spec, simp)

  (* order violation: f j < f k \<and> f k < f j *)
  apply (drule_tac x="k" in bspec)
  apply (simp add: isUngrantedNonTockRequestOfwrt_def)
  apply (simp add: isUngrantedNonTockRequestOf_def)
  apply (simp add: hasNonTockRequestFor_def)
  apply (simp add: isRequestOf_def)
  apply (simp)
  
  (* subgoal proof *)
  apply (simp add: nonempty_finite_set_exists_min_fun)
  done



end