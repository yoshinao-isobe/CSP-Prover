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

theory tockCSP_T
imports tockCSP_Infra_CSP_T
        tockCSP.tockCSP_Main
begin


subsection \<open> TOCKS semantics \<close>


lemmas TOCKS_domT = Act_prefix_domT



subsubsection \<open> Roscoe TOCKS = Schneider RUN {tock} \<close>


lemma cspT_TOCKS_eq_RUN :
    "FPmode = MIXmode \<Longrightarrow> $TOCKS =T RUN {tock}"
  apply (simp add: RUN_def)
  apply (rule cspT_fp_induct_eq_left[of "TOCKSfun" "\<lambda>p. $Run {tock}"])
  apply (simp_all)
  apply (rule cspT_reflex)
  apply (case_tac p, simp)
  apply (clarsimp)
  apply (cspT_unwind_right)
  done

lemma cspT_TOCKS_eq_RUNs :
    "FPmode \<noteq> CPOmode \<Longrightarrow> R : RUNs \<Longrightarrow> $TOCKS =T R {tock}"
  apply (rule cspT_fp_induct_eq_left[of _ "\<lambda>p. R {tock}"])
  apply (simp_all)
  apply (simp)
  apply (case_tac p, simp)
  
  apply (simp add: cspT_semantics traces_iff)
  apply (simp add: traces_run_RUNs)
  apply (simp add: traces_run_def)
  apply (insert set_run_domT[of "{tock}"])
  apply (subst Abs_domT_inject)
    apply (rule TOCKS_domT)
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



subsubsection \<open> TOCKS =T \<close>


lemma cspT_TOCKS :
    "(($TOCKS)::(TOCKSPN, 'event::tockCSP) proc) =T (((TOCKSfun TOCKS))::(TOCKSPN, 'event) proc)"
by (simp, cspT_unwind)



subsubsection \<open> traces included in TOCKS \<close>


lemma traces_TOCKS :
    "traces ($TOCKS) MT = traces (tock -> $TOCKS) MT"
  apply (insert cspT_TOCKS)
by (simp add: cspT_eqT_semantics)


lemma in_traces_TOCKS :
    "(t :t traces ($TOCKS) MT) =
     (t = <> \<or> (\<exists>s. t = <Tock> ^^^ s \<and> s :t MT TOCKS))"
  apply (simp add: traces_TOCKS)
by (simp add: in_traces)



lemma traces_included_in_FIX_TOCKS:
    "sett t \<subseteq> {Tock} \<Longrightarrow>
     t :t traces ((FIX TOCKSfun) (TOCKS)) MT"
  apply (induct t rule: induct_trace)
  
    (* <> *)
    apply (simp)
  
    (* <Tick> *)
    apply (simp)
 
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



lemma traces_included_in_TOCKS:
    "sett t \<subseteq> {Tock} \<Longrightarrow>
     t :t traces ($TOCKS::(TOCKSPN,'e::tockCSP) proc) MT"
  apply (subst FIX_traces[of TOCKSfun])
  apply (case_tac FPmode, simp_all)
by (simp add: traces_included_in_FIX_TOCKS)




subsubsection \<open> traces TOCKS iff sett \<close>


lemma in_traces_TOCKS_E:
    "t :t traces ($TOCKS::(TOCKSPN,'e::tockCSP) proc) MT \<Longrightarrow>
     sett t \<subseteq> {Tock}"
  apply (induct t rule: induct_trace)
  apply (simp_all)
  apply (simp add: traces_TOCKS)
  apply (subst (asm) traces_iff)
  apply (simp add: CollectT_open_memT TOCKS_domT)
  apply (case_tac "a \<noteq> tock", simp add: traces_TOCKS)
  apply (simp add: in_traces)
  apply (subst (asm) traces_TOCKS)
  apply (subst (asm) traces_iff)
  apply (simp)
  apply (simp add: CollectT_open_memT TOCKS_domT)
done


lemma in_traces_TOCKS_iff_sett :
    "t :t traces ($TOCKS::(TOCKSPN,'e::tockCSP) proc) MT \<longleftrightarrow> sett t \<subseteq> {Tock}"
  apply (rule iffI)
  apply (simp add: in_traces_TOCKS_E)
  apply (simp add: traces_included_in_TOCKS)
done



subsubsection \<open> TOCKS hidding \<close>


lemma cspT_TOCKS_hiding_Nontock_idem [simp]:
    "FPmode \<noteq> CPOmode \<Longrightarrow>
     $TOCKS -- Nontock =T $TOCKS"
  apply (rule cspT_fp_induct_right[of _ _ "\<lambda>p. $TOCKS -- Nontock"])
  apply (simp_all, simp)
  apply (induct_tac p)
  apply (cspT_unwind)
by (cspT_auto)+


lemma cspT_TOCKS_hiding_tock_DIV [simp]:
    "(($TOCKS)::(TOCKSPN, 'event::tockCSP) proc) -- {tock} =T DIV"
  apply (simp add: cspT_semantics)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (simp add: Abs_domT_inject Hiding_domT empT_def)
  apply (subst in_traces_TOCKS_iff_sett)
  apply (insert hiding_all_sett[of "{tock}"])
by (simp)




subsection \<open> TOCKSTick semantics \<close>


lemmas TOCKSTick_domT = Act_prefix_domT SKIP_domT


subsubsection \<open> traces included in TOCKSTick \<close>


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




subsubsection \<open> traces TOCKSTick iff sett \<close>


lemma in_traces_TOCKSTick_E:
    "t :t traces ($TOCKSTick::(TOCKSTickPN,'e::tockCSP) proc) MT \<Longrightarrow>
     sett t \<subseteq> {Tick, Tock}"
  apply (induct t rule: induct_trace)
  apply (simp_all)
  apply (case_tac "a \<noteq> tock", simp add: traces_TOCKSTick)
  apply (simp add: in_traces)
  apply (simp add: traces_TOCKSTick)
  apply (subst (asm) traces_iff)
  apply (subst (asm) traces_iff)
  apply (subst (asm) traces_iff)
  apply (simp)
  apply (simp add: CollectT_open_memT Act_prefix_domT)
  apply (simp add: traces_TOCKSTick)
done


lemma in_traces_TOCKSTick_iff_sett :
    "t :t traces ($TOCKSTick::(TOCKSTickPN,'e::tockCSP) proc) MT \<longleftrightarrow> sett t \<subseteq> {Tick, Tock}"
  apply (rule iffI)
  apply (simp add: in_traces_TOCKSTick_E)
  apply (simp add: traces_included_in_TOCKSTick)
done




subsubsection \<open> TOCKSTick Parallel preterm \<close>


lemma Nontock_par_tr_nilt_iff_lm :
    "sett s \<subseteq> {Tick,Tock} \<longrightarrow>  e \<noteq> tock \<longrightarrow>
    s |[- {e, tock}]|tr <> = s |[Nontock]|tr <>"
  apply (induct_tac s rule: induct_trace)
  apply (intro impI, simp)
    apply (rule, rule, simp, rule, simp)
  apply (intro impI, simp)
    apply (rule, rule, simp, rule, simp)

  apply (intro impI, simp)
    apply (rule, rule)
    apply (erule par_tr_elims, simp_all)
    apply (rule par_tr_intros, simp, simp)
    apply (rule par_tr_intros, simp, simp)
    apply (rule)
    apply (erule par_tr_elims, simp_all)
    apply (rule par_tr_intros, simp, simp)
    apply (rule par_tr_intros, simp, simp)
done

lemma Nontock_par_tr_nilt_iff :
    "sett s \<subseteq> {Tick,Tock} \<Longrightarrow> e \<noteq> tock \<Longrightarrow>
    s |[- {e, tock}]|tr <> = s |[Nontock]|tr <>"
by (simp add: Nontock_par_tr_nilt_iff_lm)



lemma Nontock_par_tr_Tickt_iff_lm :
    "sett s \<subseteq> {Tick,Tock} \<longrightarrow>
    s |[- {e, tock}]|tr <Tick> = s |[Nontock]|tr <Tick>"
  apply (induct_tac s rule: induct_trace)
  apply (intro impI, simp)
    apply (rule, rule, simp, rule, simp)
  apply (intro impI, simp)
    apply (rule, rule, simp, rule, simp)

  apply (intro impI, simp)
    apply (rule, rule)
    apply (erule par_tr_elims, simp_all)
    apply (rule par_tr_intros, simp, simp)
    apply (rule)
    apply (erule par_tr_elims, simp_all)
    apply (rule par_tr_intros, simp, simp)
done

lemma Nontock_par_tr_Tickt_iff :
    "sett s \<subseteq> {Tick,Tock} \<Longrightarrow>
    s |[- {e, tock}]|tr <Tick> = s |[Nontock]|tr <Tick>"
by (simp add: Nontock_par_tr_Tickt_iff_lm)


lemma trace_par_tr_Nontock :
    " u \<in> s |[Nontock]|tr t \<Longrightarrow> e \<noteq> tock \<Longrightarrow>
       s :t traces ($TOCKSTick::(TOCKSTickPN,'e::tockCSP) proc) MT \<Longrightarrow>
       t = <> \<or> t = <Tick> \<Longrightarrow> u \<in> s |[- {e, tock}]|tr t"
  apply (frule in_traces_TOCKSTick_E)
  apply (induct u rule: induct_trace)
  apply (erule par_tr_elims, simp_all)
  apply (elim exE conjE disjE)
    apply (simp)
    apply (simp add: Nontock_par_tr_nilt_iff[of s e])
    apply (simp add: Nontock_par_tr_Tickt_iff[of s e])
done

lemma trace_par_tr_Compl_sig_tock :
    " u \<in> s |[- {e, tock}]|tr t \<Longrightarrow> e \<noteq> tock \<Longrightarrow>
       s :t traces ($TOCKSTick::(TOCKSTickPN,'e::tockCSP) proc) MT \<Longrightarrow>
       t = <> \<or> t = <Tick> \<Longrightarrow> u \<in> s |[Nontock]|tr t"
  apply (frule in_traces_TOCKSTick_E)
  apply (induct u rule: induct_trace)
  apply (erule par_tr_elims, simp_all)
  apply (elim exE conjE disjE)
    apply (simp)
    apply (simp add: Nontock_par_tr_nilt_iff[of s e])
    apply (simp add: Nontock_par_tr_Tickt_iff[of s e])
done

lemma traces_TOCKSTick_Parallel_preterm_iff :
    "(e::'e::tockCSP) \<noteq> tock \<Longrightarrow>
     traces ($TOCKSTick |[- {e, tock}]| SKIP) MT =
     traces ($TOCKSTick |[Nontock]| SKIP) MT"
  apply (subst traces_iff)
    apply (subst traces_iff)
    apply (rule sym)
    apply (subst traces_iff)
    apply (subst traces_iff)
    apply (rule CollectT_eq, rule)
      apply (elim exE conjE disjE)
      apply (rule_tac x=s in exI)
      apply (rule_tac x=t in exI, simp)
      apply (simp add: trace_par_tr_Nontock)

      apply (elim exE conjE disjE)
      apply (rule_tac x=s in exI)
      apply (rule_tac x=t in exI, simp)
      apply (simp add: trace_par_tr_Compl_sig_tock)
done


lemma cspT_TOCKSTick_Parallel_preterm :
    "(e::'e::tockCSP) \<noteq> tock \<Longrightarrow>
     $TOCKSTick |[- {e, tock}]| SKIP =T $TOCKSTick |[Nontock]| SKIP"
  apply (simp add: cspT_semantics)
by (rule traces_TOCKSTick_Parallel_preterm_iff)

end