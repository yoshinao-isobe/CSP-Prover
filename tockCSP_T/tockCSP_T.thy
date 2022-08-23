theory tockCSP_T
imports tockCSP_Infra_CSP_T
        tockCSP_Main
begin


subsection \<open> TOCKS semantics \<close>


subsubsection \<open> traces included in TOCKS \<close>


lemmas TOCKS_domT = Act_prefix_domT


lemma cspT_TOCKS :
    "(($TOCKS)::(TOCKSPN, 'event::tockCSP) proc) =T (((TOCKSfun TOCKS))::(TOCKSPN, 'event) proc)"
  by (simp, cspT_unwind)


lemma traces_TOCKS :
    "traces ($TOCKS) MT = traces (tock -> $TOCKS) MT"
  apply (insert cspT_TOCKS)
  by (simp add: cspT_eqT_semantics)



subsubsection \<open> Roscoe TOCKS = Schneider RUN {tock} \<close>

lemma cspT_TOCKS_eq_RUN :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    RUN : RUNs ==> $TOCKS =T RUN {tock}"
  apply (rule cspT_fp_induct_eq_left[of _ "\<lambda>p. RUN {tock}"])
  apply (simp_all)
  apply (simp)
  apply (case_tac p, simp)

  apply (simp add: cspT_semantics traces_iff)
  apply (simp add: traces_run_RUNs)
  apply (simp add: traces_run_def)
  apply (insert set_run_domT[of "{tock}"])
  apply (subst Abs_domT_inject)
    apply (rule Act_prefix_domT)
    apply (simp)
  apply (rule)
  apply (rule)
    apply (simp add: set_run.intros)
    apply (elim disjE, simp)
      apply (rule set_run.intros)
    apply (elim exE, simp)
    apply (rule set_run_app, rule)
    apply (rule set_run_one, simp)
    apply (simp add: memT_def Abs_domT_inverse)
  apply (rule)
    apply (simp)
    apply (erule set_run.cases, simp_all)
    apply (simp add: memT_def Abs_domT_inverse)
  done




subsection \<open> TOCKSTick semantics \<close>


subsubsection \<open> traces included in TOCKSTick \<close>


lemmas TOCKSTick_domT = Act_prefix_domT SKIP_domT


lemma cspT_TOCKSTick :
    "(($TOCKSTick)::(TOCKSTickPN, 'event::tockCSP) proc) =T
     (((TOCKSTickfun TOCKSTick))::(TOCKSTickPN, 'event) proc)"
  by (simp, cspT_unwind)


lemma traces_TOCKSTick :
    "traces ($TOCKSTick) MT = traces (tock -> $TOCKSTick |~| SKIP) MT"
  apply (insert cspT_TOCKSTick)
  by (simp add: cspT_eqT_semantics)


lemma in_traces_TOCKSTick :
    "(t :t traces ($TOCKSTick) MT) =
     (t = <> \<or> (\<exists>s. t = <Tock> ^^^ s \<and> s :t MT TOCKSTick) \<or> t = <> \<or> t = <Tick>)"
  apply (simp add: traces_TOCKSTick)
  by (simp add: in_traces)



lemma traces_included_in_FIX_TOCKSTick:
    "sett t \<subseteq> {Tick, Tock} \<Longrightarrow>
     t :t traces ((FIX TOCKSTickfun) (TOCKSTick)) (MT)"
  apply (induct t rule: induct_trace)
  
    (* <> *)
    apply (simp)
  
    (* <Tick> *)
    apply (simp add: FIX_def)
    apply (simp add: in_traces)
    apply (rule_tac x="Suc 0" in exI)
    apply (simp add: FIXn_def)
    apply (simp add: Subst_procfun_prod_def)
    apply (simp add: in_traces)
  
    (* <Eva>^^^s *)
    apply (simp add: FIX_def)
    apply (simp add: in_traces)

    apply (erule disjE)
  
    apply (rule_tac x="Suc 0" in exI)
    apply (simp add: FIXn_def)
    apply (simp add: Subst_procfun_prod_def)
    apply (simp add: in_traces)
  
    apply (erule exE)
    apply (rule_tac x="Suc n" in exI)
    apply (simp add: FIXn_def)
    apply (simp add: Subst_procfun_prod_def)
    apply (simp add: in_traces)
  done



lemma traces_included_in_TOCKSTick:
    "sett t \<subseteq> {Tick, Tock} \<Longrightarrow>
     t :t traces ($TOCKSTick::(TOCKSTickPN,'e::tockCSP) proc) (MT)"
  apply (subst FIX_traces[of TOCKSTickfun])
  apply (case_tac FPmode, simp_all)
  by (simp add: traces_included_in_FIX_TOCKSTick)


end