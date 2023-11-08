           (*-------------------------------------------*
            |                     DF A                  |
            |                                           |
            |                 2022 / 2023               |
            |                                           |
            |        CSP-Prover on Isabelle2021         |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_law_DFnonTick
imports DFP_DFnonTick
begin


section \<open> deadlock-free \<close>

fun DF_induct_Hypotheses :: "'e DFalphaPN \<Rightarrow> (DFtickName, 'e) proc"
where
    "DF_induct_Hypotheses (DF' A) = $DFtick"

lemma Lemma_DFPN_To_DFtick :
    "DF_induct_Hypotheses p <=F (DFalphafun p) << DF_induct_Hypotheses"
  apply (induct_tac p, simp, cspF_unwind, rule cspF_Int_choice_left1, cspF_auto)
  apply (case_tac "xa = {}", cspF_auto)
  apply (rule cspF_decompo_ref, simp, simp)
done

lemma dfp_DF': "($DFtick::(DFtickName, 'e) proc) <=F (($DF' A)::('e DFalphaPN, 'e) proc)"
  apply (rule_tac Pf="DFalphafun" and f="DF_induct_Hypotheses" in cspF_fp_induct_ref_right)
  apply (simp, case_tac FPmode, simp_all)
  apply (rule Lemma_DFPN_To_DFtick)
done


lemma DF'_isDeadlockFree: "($DF' A:: ('e DFalphaPN, 'e) proc) isDeadlockFree"
by (simp only: DeadlockFree_DFtick_ref, rule dfp_DF')


lemma DF'_DeadlockFree:
    "($DF' A:: ('e DFalphaPN, 'e) proc) <=F P ==> P isDeadlockFree"
  apply (insert DF'_isDeadlockFree)
  apply (simp add: DeadlockFree_def)
  apply (simp add: cspF_refF_semantics)
  apply (auto)
done



end