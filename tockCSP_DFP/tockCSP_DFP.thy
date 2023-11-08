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

theory tockCSP_DFP
imports tockCSP_DFP_law
begin



subsection \<open> dfp_TOCKS \<close>


lemma dfpnt_TOCKS :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    $DF' <=F (($TOCKS)::(TOCKSPN,'event::tockCSP) proc)"
  apply (rule_tac Pf="DFfun" and f="\<lambda>p. $TOCKS" in cspF_fp_induct_ref_left)
  apply (simp, case_tac FPmode, simp_all)

  apply (induct_tac p, simp)
  apply (cspF_unwind_right)
  apply (cspF_step_right)
  by (rule cspF_decompo_ref, simp_all)


lemma dfp_TOCKS :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    $DFtick <=F (($TOCKS)::(TOCKSPN,'event::tockCSP) proc)"
  by (rule cspF_trans, rule dfp_DF', rule dfpnt_TOCKS)


lemma TOCKS_isDeadlockFree :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    (($TOCKS)::(TOCKSPN,'event::tockCSP) proc) isDeadlockFree"
  by (rule DFtick_DeadlockFree, rule dfp_TOCKS, simp)




subsection \<open> dfp_TOCKSTick \<close>


lemma dfp_TOCKSTick :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    $DFtick <=F (($TOCKSTick)::(TOCKSTickPN,'event::tockCSP) proc)"
  apply (rule_tac Pf="DFtickfun" and f="\<lambda>p. $TOCKSTick" in cspF_fp_induct_ref_left)
  apply (simp, case_tac FPmode, simp_all)

  apply (induct_tac p, simp)
  apply (cspF_unwind_right)
  apply (rule cspF_decompo)
  apply (cspF_step_right)
  by (rule cspF_decompo_ref, simp_all)


lemma TOCKSTick_isDeadlockFree :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    (($TOCKSTick)::(TOCKSTickPN,'event::tockCSP) proc) isDeadlockFree"
  by (rule DFtick_DeadlockFree, rule dfp_TOCKSTick, simp)


end