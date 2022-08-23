theory tockCSP_DFP
imports tockCSP_F_Main
        tockCSP_Infra_DFP
begin



subsection \<open> dfp_TOCKS \<close>


lemma dfpnt_TOCKS :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    $DFnonTick <=F (($TOCKS)::(TOCKSPN,'event::tockCSP) proc)"
  apply (rule_tac Pf="DFnonTickfun" and f="\<lambda>p. $TOCKS" in cspF_fp_induct_ref_left)
  apply (simp, case_tac FPmode, simp_all)

  apply (induct_tac p, simp)
  apply (cspF_unwind_right)
  apply (cspF_step)
  by (rule cspF_decompo_ref, simp_all)


lemma dfp_TOCKS :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    $DFtick <=F (($TOCKS)::(TOCKSPN,'event::tockCSP) proc)"
  by (rule cspF_trans, rule dfp_DFnonTick, rule dfpnt_TOCKS)


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
  apply (cspF_step)
  by (rule cspF_decompo_ref, simp_all)


lemma TOCKSTick_isDeadlockFree :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    (($TOCKSTick)::(TOCKSTickPN,'event::tockCSP) proc) isDeadlockFree"
  by (rule DFtick_DeadlockFree, rule dfp_TOCKSTick, simp)


end