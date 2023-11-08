           (*-------------------------------------------*
            |                    RUN S                  |
            |                                           |
            |                 2022 / 2023               |
            |                                           |
            |        CSP-Prover on Isabelle2021         |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_RUN
imports CSP_F.CSP_F_law_RUN
        DFP_law_DFtick
        DFP_law_DF
begin



subsection \<open> ~ DF <=F RUN {} \<close>


lemma not_dfpnt_Run_emptyset :
    "FPmode \<noteq> CPOmode \<Longrightarrow> ~ $DF' <=F (($Run {})::('a RunName,'a) proc)"
  apply (erule contrapos_nn)
  apply (erule cspF_rw_rightE)
  apply (rule cspF_Run_STOP)
by (simp add: not_dfpnt_STOP)


lemma not_dfpnt_RUN_emptyset :
    "FPmode \<noteq> CPOmode \<Longrightarrow> ~ $DF' <=F RUN {}"
by (simp add: RUN_def, rule not_dfpnt_Run_emptyset)


subsection \<open> ~ DFtick <=F RUN {} \<close>

lemma not_dfp_Run_emptyset :
    "FPmode \<noteq> CPOmode \<Longrightarrow> ~ $DFtick <=F (($Run {})::('a RunName,'a) proc)"
  apply (erule contrapos_nn)
  apply (erule cspF_rw_rightE)
  apply (rule cspF_Run_STOP)
by (simp add: not_dfp_STOP)


lemma not_dfp_RUN_emptyset :
    "FPmode \<noteq> CPOmode \<Longrightarrow> ~ $DFtick <=F RUN {}"
by (simp add: RUN_def, rule not_dfp_Run_emptyset)



subsection \<open> DF <=F RUN S \<close>


fun DF_Run :: "'e set \<Rightarrow> DFPN \<Rightarrow> ('e RunName, 'e) proc"
where
  "DF_Run S DFonTick = (if (S = {}) then STOP else $Run S)"

lemma dfpnt_Run :
    "FPmode \<noteq> CPOmode \<Longrightarrow> S \<noteq> {} \<Longrightarrow> $DF' <=F (($Run (S::'a set))::('a RunName,'a) proc)"
  apply (rule_tac Pf=DFfun and f="DF_Run S" in cspF_fp_induct_ref_left)
  apply (simp_all)
  apply (induct_tac p, simp_all)     
  apply (cspF_step)
  apply (cspF_unwind_right)
  apply (rule cspF_decompo_ref, simp_all)
done


lemma dfpnt_RUN :
    "FPmode \<noteq> CPOmode \<Longrightarrow> S \<noteq> {} \<Longrightarrow> $DF' <=F RUN S"
by (simp add: RUN_def, rule dfpnt_Run)



subsection \<open> DFtick <=F RUN S \<close>


lemma dfp_Run :
    "FPmode \<noteq> CPOmode \<Longrightarrow> S \<noteq> {} \<Longrightarrow> $DFtick <=F (($Run (S::'a set))::('a RunName,'a) proc)"
  apply (rule cspF_trans)
  apply (rule dfp_DF')
  apply (rule dfpnt_Run, simp_all)
done


lemma dfp_RUN :
    "FPmode \<noteq> CPOmode \<Longrightarrow> S \<noteq> {} \<Longrightarrow> $DFtick <=F RUN S"
by (simp add: RUN_def, rule dfp_Run)




subsection \<open> dfpnt Run iff \<close>


lemma dfpnt_Run_iff :
    "FPmode \<noteq> CPOmode \<Longrightarrow> ($DF' <=F (($Run (S::'a set))::('a RunName,'a) proc)) = (S \<noteq> {})"
  apply (case_tac "S = {}", simp_all)
  apply (simp add: not_dfpnt_Run_emptyset)
by (simp add: dfpnt_Run)


lemma dfpnt_RUN_iff :
    "FPmode \<noteq> CPOmode \<Longrightarrow> ($DF' <=F RUN S) = (S \<noteq> {})"
by (simp add: RUN_def, rule dfpnt_Run_iff)



subsection \<open> dfp Run iff \<close>


lemma dfp_Run_iff :
    "FPmode \<noteq> CPOmode \<Longrightarrow> ($DFtick <=F (($Run (S::'a set))::('a RunName,'a) proc)) = (S \<noteq> {})"
  apply (case_tac "S = {}", simp_all)
  apply (simp add: not_dfp_Run_emptyset)
by (simp add: dfp_Run)


lemma dfp_RUN_iff :
    "FPmode \<noteq> CPOmode \<Longrightarrow> ($DFtick <=F RUN S) = (S \<noteq> {})"
by (simp add: RUN_def, rule dfp_Run_iff)



end