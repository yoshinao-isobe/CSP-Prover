           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 2022 / 2023               |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_noTick
imports CSP_F
begin


section \<open> Non-Terminating \<close>

lemma noTick_if_Evset_notin_failures_t:
    "\<forall>s::'e trace. (s, Evset) ~:f failures P MF \<Longrightarrow>
     t :t traces P (fstF \<circ> MF) \<Longrightarrow> noTick(t::'e trace)"
  apply (drule_tac x="butlastt t ^^^ <Tick>" in spec)
    apply (erule contrapos_np)
    apply (frule Tick_decompo)
    apply (insert proc_domF[of P MF])
    apply (frule_tac s="butlastt t" in domF_T3[of "traces P (fstF \<circ> MF)" "failures P MF" _ UNIV])
    apply (simp)
    apply (rule noTick_butlast, simp)
    apply (rule memF_F2, simp, simp)
done

lemma noTick_if_Evset_notin_failures_f:
    "\<forall>s::'e trace. (s, Evset) ~:f failures P MF \<Longrightarrow>
     (t,X) :f failures P MF \<Longrightarrow> noTick(t::'e trace)"
  apply (drule_tac x="butlastt t ^^^ <Tick>" in spec)
    apply (erule contrapos_np)
    apply (frule Tick_decompo)
    apply (insert proc_domF[of P MF])
    apply (frule_tac s="butlastt t" in domF_T3[of "traces P (fstF \<circ> MF)" "failures P MF" _ UNIV])
    apply (simp)
    apply (rule proc_T2, simp)
    apply (rule noTick_butlast, simp)
    apply (rule_tac X=UNIV in memF_F2, simp, simp)
done

lemmas noTick_if_Evset_notin_failures = noTick_if_Evset_notin_failures_t
                                        noTick_if_Evset_notin_failures_f



lemma decompo_one_appt_noTick:
  "[| noTick (<Ev a> ^^^ t) |] ==> noTick t"
by (simp add: noTick_def)

lemma sett_one_appt_subset :
  "[| sett (<Ev a> ^^^ s) \<subseteq> Ev ` A |] ==> sett (s) \<subseteq> Ev ` A"
by (simp)

lemma sett_subset_Evset_iff_noTick:
 "(sett s <= Evset) = noTick s"
by (simp add: noTick_def Evset_def, force)

lemmas noTick_iff_sett_subset_Evset = sett_subset_Evset_iff_noTick[THEN sym]



end