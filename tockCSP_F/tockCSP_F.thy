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

theory tockCSP_F
imports tockCSP_Infra_CSP_F
        tockCSP_T.tockCSP_T_Main
begin


subsection \<open> TOCKS semantics \<close>


lemmas TOCKS_setF = Act_prefix_setF


subsubsection \<open> Roscoe TOCKS =F Schneider RUN {tock} \<close>


lemma cspF_TOCKS_eq_Run :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    (($TOCKS)::(TOCKSPN,'e::tockCSP) proc) =F (($Run {tock})::('e RunName,'e::tockCSP) proc)"
  apply (rule cspF_fp_induct_left[of _ "\<lambda>p. $Run {tock}"], simp_all)
  apply (simp)
  apply (rule cspF_reflex)
  apply (induct_tac p, simp)
by (cspF_unwind_right)

lemma cspF_TOCKS_eq_RUN :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    (($TOCKS)::(TOCKSPN,'e::tockCSP) proc) =F RUN {tock}"
by (simp add: RUN_def cspF_TOCKS_eq_Run)



subsection \<open> TOCKS =F \<close>


lemma cspF_TOCKS :
    "(($TOCKS)::(TOCKSPN, 'event::tockCSP) proc) =F (((TOCKSfun TOCKS))::(TOCKSPN, 'event) proc)"
by (simp, cspF_unwind)



subsection \<open> TOCKS failures \<close>


lemma failures_TOCKS :
    "failures (($TOCKS) :: (TOCKSPN, 'event::tockCSP) proc) MF =
     {f. (\<exists>X. f = (<>, X) \<and> Tock \<notin> X) \<or>
        (\<exists>s X. f = (<Tock> ^^^ s, X) \<and>
               (s, X) :f sndF (MF TOCKS))}f"
  apply (insert cspF_TOCKS)
  apply (simp add: cspF_eqF_semantics, elim conjE)
by (simp add: failures_iff)


lemma failures_TOCKS_step :
    "failures ($TOCKS) MF =
     {f. (\<exists>X. f = (<>, X) \<and> Tock \<notin> X) \<or>
        (\<exists>s X. f = (<Tock> ^^^ s, X) \<and> (s, X) :f failures ($TOCKS) MF)}f"
  apply (insert cspF_TOCKS)
  apply (simp add: cspF_eqF_semantics, elim conjE)
by (simp add: failures_iff)


(*lemmas in_failures_TOCKS = in_failures_Act_prefix*)
lemma in_failures_TOCKS :
    "((s,X) :f failures (($TOCKS) :: (TOCKSPN, 'event::tockCSP) proc) MF) =
     (s = <> \<and> Tock \<notin> X \<or> (\<exists>sa. s = <Tock> ^^^ sa \<and> (sa, X) :f sndF (MF TOCKS)))"
  apply (simp add: failures_TOCKS)
by (simp add: CollectF_open_memF TOCKS_setF)


lemma failures_TOCKS_to_TOCKSfun : 
    "failures (($TOCKS)::(TOCKSPN, 'event::tockCSP) proc) MF = 
     failures ((TOCKSfun TOCKS)::(TOCKSPN, 'event) proc) MF"
  apply (simp)
  apply (simp add: failures_TOCKS)
  apply (simp add: failures_iff)
done




subsubsection \<open> cases MAXIMAL refusals in_failures_TOCKS \<close>

lemma Tickt_notin_failures_TOCKS :
    "(<Tick>::('e::tockCSP) trace,X) ~:f failures ($TOCKS) MF"
  apply (simp add: failures_TOCKS)
by (simp add: CollectF_open_memF TOCKS_setF)

lemma Tock_notin_failures_TOCKS :
    "(t, X) :f failures ($TOCKS) MF \<Longrightarrow> Tock \<notin> X"
  apply (induct t rule: induct_trace)
  apply (simp add: in_failures_TOCKS)
  apply (simp add: in_failures_TOCKS)
  apply (subst (asm) failures_TOCKS_step)
by (simp add: CollectF_open_memF TOCKS_setF)


lemma NonTockEv_in_failures_TOCKS :
    "sett s \<subseteq> {Tock} \<Longrightarrow> (s,NonTockEv) :f failures ($TOCKS) MF"
  apply (induct s rule: induct_trace)
  apply (simp add: in_failures_TOCKS)
  apply (simp)
  apply (subst failures_TOCKS_step)
by (simp add: CollectF_open_memF TOCKS_setF)


lemma nilt_NonTockEv_in_failures_TOCKS :
    "(<>,NonTockEv) :f failures ($TOCKS) MF"
by (simp add: NonTockEv_in_failures_TOCKS)

lemma Tockt_NonTockEv_in_failures_TOCKS :
    "sett s = {Tock} \<Longrightarrow> (<Tock> ^^^ s,NonTockEv) :f failures ($TOCKS) MF"
by (simp add: NonTockEv_in_failures_TOCKS)

lemmas cases_in_failures_TOCKS = nilt_NonTockEv_in_failures_TOCKS
                                 Tockt_NonTockEv_in_failures_TOCKS
                                 NonTockEv_in_failures_TOCKS



subsubsection \<open> failures included in TOCKS \<close>


(*     (s = <> \<and> Tock \<notin> X \<or> (\<exists>sa. s = <Tock> ^^^ sa \<and> (sa, X) :f sndF (MF TOCKS)))*)

lemma failures_included_in_FIX_TOCKS_lm :
    "(sett t \<subseteq> {Tock} \<and> Tock \<notin> X) \<longrightarrow>
     (t,X) :f failures ((FIX TOCKSfun) (TOCKS)) MF"
  apply (induct t rule: induct_trace)
  
   (* <> *)
  apply (rule)
  apply (simp add: FIX_def in_failures)
  apply (rule_tac x="Suc 0" in exI)
  apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)

   (* <Tick> *)
  apply (simp)
  
   (* <Ev a> ^^^ s *)
  apply (rule)
  apply (simp add: FIX_def in_failures)
  apply (elim exE conjE)
  apply (rule_tac x="Suc n" in exI)
  apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)
done

lemma failures_included_in_FIX_TOCKS :
    "[| sett t \<subseteq> {Tock} ; Tock \<notin> X |] ==>
     (t,X) :f failures ((FIX TOCKSfun) (TOCKS)) MF"
by (simp add: failures_included_in_FIX_TOCKS_lm)

lemma failures_included_in_TOCKS :
    "[| sett t \<subseteq> {Tock} ; Tock \<notin> X |] ==>
     (t,X) :f failures ($TOCKS::(TOCKSPN,'e::tockCSP) proc) MF"
  apply (subst FIX_failures[of TOCKSfun])
  apply (case_tac FPmode, simp_all)
by (simp add: failures_included_in_FIX_TOCKS)




subsubsection \<open> failures TOCKS iff \<close>


lemma in_failures_TOCKS_E:
    "(t,X) :f failures ($TOCKS::(TOCKSPN,'e::tockCSP) proc) MF \<Longrightarrow>
     sett t \<subseteq> {Tock} \<and> Tock \<notin> X"
  apply (frule_tac proc_T2)
  apply (simp add: fstF_MF_MT)
  apply (simp add: in_traces_TOCKS_E)
  apply (simp add: Tock_notin_failures_TOCKS)
done


lemma in_failures_TOCKS_iff_sett :
    "(t,X) :f failures ($TOCKS::(TOCKSPN,'e::tockCSP) proc) MF \<longleftrightarrow> sett (t) \<subseteq> {Tock} \<and> Tock \<notin> X"
  apply (rule iffI)
  apply (simp add: in_failures_TOCKS_E)
  apply (simp add: failures_included_in_TOCKS)
done



subsubsection \<open> TOCKS hidding \<close>


lemma cspF_TOCKS_hiding_Nontock_idem [simp]:
    "FPmode \<noteq> CPOmode \<Longrightarrow>
     $TOCKS -- Nontock =F $TOCKS"
  apply (rule cspF_fp_induct_right[of _ _ "\<lambda>p. $TOCKS -- Nontock"])
  apply (simp_all, simp)
  apply (induct_tac p)
  apply (cspF_unwind)
by (cspF_auto)+


lemma cspF_TOCKS_hiding_tock_DIV [simp]:
    "(($TOCKS)::(TOCKSPN, 'event::tockCSP) proc) -- {tock} =F DIV"
  apply (simp add: cspF_cspT_semantics)
  apply (rule)
    apply (simp add: fstF_MF_MT)
    apply (rule cspT_trans)
    apply (rule cspT_TOCKS_hiding_tock_DIV, simp)

    apply (subst failures_iff)
    apply (subst failures_iff)
    apply (simp add: Abs_domF_inject Hiding_setF empF_def)
    apply (subst in_failures_TOCKS_iff_sett)
    apply (insert hiding_all_sett[of "{tock}"])
by (simp)



subsection \<open> TOCKSTick semantics \<close>


lemmas TOCKSTick_setF = Act_prefix_setF SKIP_setF


lemma cspF_TOCKSTick :
    "(($TOCKSTick)::(TOCKSTickPN, 'event::tockCSP) proc) =F
     (((TOCKSTickfun TOCKSTick))::(TOCKSTickPN, 'event) proc)"
by (simp, cspF_unwind)


lemma failures_TOCKSTick :
    "failures ($TOCKSTick) MF =
     {f. (\<exists>X. f = (<>, X) \<and> Tock \<notin> X) \<or>
        (\<exists>s X. f = (<Tock> ^^^ s, X) \<and>
               (s, X) :f sndF (MF TOCKSTick))}f UnF
     {f. (\<exists>X. f = (<>, X) \<and> X \<subseteq> Evset) \<or> (\<exists>X. f = (<Tick>, X))}f"
  apply (insert cspF_TOCKSTick)
  apply (simp add: cspF_eqF_semantics, elim conjE)
by (simp add: failures_iff)


lemma failures_TOCKSTick_step :
    "failures ($TOCKSTick) MF =
     {f. (\<exists>X. f = (<>, X) \<and> Tock \<notin> X) \<or>
        (\<exists>s X. f = (<Tock> ^^^ s, X) \<and> (s, X) :f failures ($TOCKSTick) MF)}f UnF
     {f. (\<exists>X. f = (<>, X) \<and> X \<subseteq> Evset) \<or> (\<exists>X. f = (<Tick>, X))}f"
  apply (insert cspF_TOCKSTick)
  apply (simp add: cspF_eqF_semantics, elim conjE)
by (simp add: failures_iff)


(*lemmas in_failures_TOCKSTick = in_failures_Act_prefix in_failures_Int_choice in_failures_SKIP*)
lemma in_failures_TOCKSTick :
    "((s,X) :f failures ($TOCKSTick) MF) =
     ((s = <> \<and> Tock \<notin> X \<or>
     (\<exists>sa. s = <Tock> ^^^ sa \<and> (sa, X) :f sndF (MF TOCKSTick)) \<or>
     s = <> \<and> X \<subseteq> Evset \<or> s = <Tick>))"
  apply (simp add: failures_TOCKSTick)
by (simp add: CollectF_open_memF TOCKSTick_setF)


(*lemma in_refusals_TOCKSTick :
    "((s,X) :f failures ($TOCKSTick) MF) =
     ((s = <> \<and> X = NonTickTockEv \<or>
     (\<exists>sa. s = <Tock> ^^^ sa \<and> (sa, X) :f failures ($TOCKSTick) MF) \<or>
     s = <Tick>))"
  apply (simp add: failures_TOCKSTick)
  apply (simp add: CollectF_open_memF SKIP_setF Act_prefix_setF)
  apply (rule)
  apply (elim disjE, simp)
  apply (simp add: CollectF_open_memF TOCKSTick_setF)
apply (aut)*)


lemma failures_TOCKSTick_to_TOCKSTickfun : 
    "failures (($TOCKSTick)::(TOCKSTickPN, 'event::tockCSP) proc) MF = 
     failures ((TOCKSTickfun TOCKSTick)::(TOCKSTickPN, 'event) proc) MF"
  apply (simp)
  apply (simp add: failures_TOCKSTick)
  apply (simp add: failures_iff)
done



subsubsection \<open> cases MAXIMAL refusals in_failures_SKIP - TODO: move to CSP_F.CSP_F_failures \<close>

lemma nilt_Evset_in_failures_SKIP :
    "(<>,Evset) :f failures (SKIP) MF"
by (simp add: in_failures)

lemma Tickt_EvsetTick_in_failures_SKIP :
    "(<Tick>,EvsetTick) :f failures (SKIP) MF"
by (simp add: in_failures)

lemmas cases_in_failures_SKIP = nilt_Evset_in_failures_SKIP
                                Tickt_EvsetTick_in_failures_SKIP



subsubsection \<open> cases NOT in_failures_TOCKSTick \<close>


lemma nilt_EvsetTick_notin_failures_TOCKSTick :
    "(<>::('e::tockCSP) trace,EvsetTick) ~:f failures ($TOCKSTick) MF"
by (simp add: in_failures_TOCKSTick)



subsubsection \<open> cases MAXIMAL refusals in_failures_TOCKSTick \<close>


lemma nilt_Evset_in_failures_TOCKSTick :
    "(<>::('e::tockCSP) trace,Evset) :f failures ($TOCKSTick) MF"
by (simp add: in_failures_TOCKSTick)

lemma Tickt_EvsetTick_in_failures_TOCKSTick :
    "(<Tick>::('e::tockCSP) trace,EvsetTick) :f failures ($TOCKSTick) MF"
  apply (simp add: failures_TOCKSTick)
by (simp add: CollectF_open_memF TOCKSTick_setF)

lemma appt_Tickt_EvsetTick_in_failures_TOCKSTick :
    "sett s \<subseteq> {Tock} \<Longrightarrow>
     (s ^^^ <Tick>::('e::tockCSP) trace,EvsetTick) :f failures ($TOCKSTick) MF"
  apply (subst failures_TOCKSTick_step)
  apply (simp add: CollectF_open_memF TOCKSTick_setF)
  apply (simp add: subset_singleton_iff)
  apply (erule disjE)
    apply (rule disjI2, simp add: sett_empty_iff)
    apply (rule disjI1)
    apply (induct s rule: induct_trace)
      apply (simp_all)
      apply (simp add: subset_singleton_iff)
      apply (elim disjE, simp add: sett_empty_iff)
        apply (simp add: Tickt_EvsetTick_in_failures_TOCKSTick)
      apply (simp)
      apply (elim exE conjE)
      apply (rule_tac x="<Tock> ^^^ sa" in exI)
      apply (frule noTick_if_sett_Tock)
      apply (simp add: appt_assoc)
      apply (subst failures_TOCKSTick_step)
      apply (simp add: CollectF_open_memF TOCKSTick_setF)
done

lemma Tockt_EvsetTick_in_failures_TOCKSTick :
    "(s,EvsetTick) :f failures ($TOCKSTick) MF \<Longrightarrow>
     (<Tock> ^^^ s,EvsetTick) :f failures ($TOCKSTick) MF"
  apply (subst failures_TOCKSTick_step)
by (simp add: CollectF_open_memF TOCKSTick_setF)


lemma NonTickTockEv_in_failures_TOCKSTick_only_if :
    "sett s \<subseteq> {Tock,Tick} \<Longrightarrow> (s,NonTickTockEv) :f failures ($TOCKSTick) MF"
  apply (induct s rule: induct_trace)
  apply (simp add: in_failures_TOCKSTick)
  apply (simp add: in_failures_TOCKSTick)
  apply (subst failures_TOCKSTick_step)
by (simp add: CollectF_open_memF TOCKSTick_setF)

lemma NonTickTockEv_in_failures_TOCKSTick_if :
    "(s,NonTickTockEv) :f failures ($TOCKSTick) MF \<Longrightarrow> sett s \<subseteq> {Tock,Tick}"
  apply (induct s rule: induct_trace)
  apply (simp add: in_failures_TOCKSTick)
  apply (simp add: in_failures_TOCKSTick)
  apply (subst (asm) failures_TOCKSTick_step)
by (simp add: CollectF_open_memF TOCKSTick_setF)

lemma NonTickTockEv_in_failures_TOCKSTick_iff :
    "((s,NonTickTockEv) :f failures ($TOCKSTick) MF) = (sett s \<subseteq> {Tock,Tick})"
  apply (rule iffI)
  apply (simp add: NonTickTockEv_in_failures_TOCKSTick_if)
  apply (simp add: NonTickTockEv_in_failures_TOCKSTick_only_if)
done


lemma nilt_NonTickTockEv_in_failures_TOCKSTick :
    "(<>,NonTickTockEv) :f failures ($TOCKSTick) MF"
by (simp add: NonTickTockEv_in_failures_TOCKSTick_iff)

lemma Tickt_NonTickTockEv_in_failures_TOCKSTick :
    "(<Tick>::('e::tockCSP) trace,NonTickTockEv) :f failures ($TOCKSTick) MF"
by (simp add: NonTickTockEv_in_failures_TOCKSTick_iff)





(*
lemma not_noTick_EvsetTick_in_failures_TOCKSTick_only_if :
    "sett s \<subseteq> {Tock,Tick} \<Longrightarrow>
    \<not> noTick (s::('e::tockCSP) trace) \<Longrightarrow> (s,EvsetTick) :f failures ($TOCKSTick) MF"
  apply (induct s rule: induct_trace)
  apply (simp add: in_failures_TOCKSTick)
  apply (simp add: in_failures_TOCKSTick)

  apply (subst failures_TOCKSTick_step)
  apply (simp add: CollectF_open_memF TOCKSTick_setF)
done

lemma not_noTick_EvsetTick_in_failures_TOCKSTick_if :
    "(s, EvsetTick) :f failures ($TOCKSTick) MF \<Longrightarrow> \<not> noTick (s::('e::tockCSP) trace)"
  apply (induct s rule: induct_trace)
  apply (simp add: in_failures_TOCKSTick)
  apply (simp add: in_failures_TOCKSTick)
  apply (subst (asm) failures_TOCKSTick_step)
  apply (simp add: CollectF_open_memF TOCKSTick_setF)
done

lemma not_noTick_EvsetTick_in_failures_TOCKSTick_iff :
    "sett s \<subseteq> {Tock,Tick} \<Longrightarrow>
    (\<not> noTick (s::('e::tockCSP) trace)) = ((s,EvsetTick) :f failures ($TOCKSTick) MF)"
  apply (rule iffI)
  apply (simp add: not_noTick_EvsetTick_in_failures_TOCKSTick_only_if)
  apply (simp add: not_noTick_EvsetTick_in_failures_TOCKSTick_if)
done



lemma aTock_NonTickTockEv_in_failures_TOCKSTick_only_if :
    "sett s \<subseteq> {Tock} \<Longrightarrow>
     (s,NonTickTockEv) :f failures ($TOCKSTick) MF"
  apply (induct s rule: induct_trace)
  apply (simp add: in_failures_TOCKSTick)
  apply (simp add: in_failures_TOCKSTick)
  apply (subst failures_TOCKSTick_step)
by (simp add: CollectF_open_memF TOCKSTick_setF)

lemma aTock_NonTickTockEv_in_failures_TOCKSTick_if :
    "noTick (s::('e::tockCSP) trace) \<Longrightarrow>
     (s,NonTickTockEv) :f failures ($TOCKSTick) MF \<Longrightarrow> sett s \<subseteq> {Tock}"
  apply (induct s rule: induct_trace)
  apply (simp add: in_failures_TOCKSTick)
  apply (simp add: in_failures_TOCKSTick)
  apply (subst (asm) failures_TOCKSTick_step)
by (simp add: CollectF_open_memF TOCKSTick_setF)

lemma aTock_NonTickTockEv_in_failures_TOCKSTick_iff :
    "noTick (s::('e::tockCSP) trace) \<Longrightarrow>
     sett s \<subseteq> {Tock} = ((s,NonTickTockEv) :f failures ($TOCKSTick) MF)"
  apply (rule iffI)
  apply (simp add: aTock_NonTickTockEv_in_failures_TOCKSTick_only_if)
  apply (simp add: aTock_NonTickTockEv_in_failures_TOCKSTick_if)
done


lemma noTick_NonTickTockEv_in_failures_TOCKSTick_iff :
    "sett s \<subseteq> {Tock} \<Longrightarrow>
     noTick (s::('e::tockCSP) trace) = ((s,NonTickTockEv) :f failures ($TOCKSTick) MF)"
  apply (rule iffI)
  apply (simp add: aTock_NonTickTockEv_in_failures_TOCKSTick_only_if)
  apply (simp add: noTick_if_sett_Tock)
done
*)



lemma NonTockEv_in_failures_TOCKSTick :
    "sett s \<subseteq> {Tock} \<Longrightarrow> (s,NonTockEv) :f failures ($TOCKSTick) MF"
  apply (induct s rule: induct_trace)
  apply (simp add: in_failures_TOCKSTick)
  apply (simp)
  apply (subst failures_TOCKSTick_step)
by (simp add: CollectF_open_memF TOCKSTick_setF)

lemma nilt_NonTockEv_in_failures_TOCKSTick :
    "(<>,NonTockEv) :f failures ($TOCKSTick) MF"
by (simp add: NonTockEv_in_failures_TOCKSTick)

lemma Tockt_NonTockEv_in_failures_TOCKSTick :
    "sett s = {Tock} \<Longrightarrow> (<Tock> ^^^ s,NonTockEv) :f failures ($TOCKSTick) MF"
by (simp add: NonTockEv_in_failures_TOCKSTick)


lemmas cases_in_failures_TOCKSTick = nilt_NonTockEv_in_failures_TOCKSTick
                                     Tockt_NonTockEv_in_failures_TOCKSTick
                                     NonTockEv_in_failures_TOCKSTick


lemma EvsetTick_refusals_TOCKSTick :
    "~ noTick s \<Longrightarrow> sett s \<subseteq> {Tock,Tick} \<Longrightarrow>
    (s::('e::tockCSP) trace,EvsetTick) :f failures ($TOCKSTick) MF"
  apply (induct s rule: induct_trace)
  apply (simp)
  apply (simp add: Tickt_EvsetTick_in_failures_TOCKSTick)
  apply (subst failures_TOCKSTick_step)
  apply (simp add: CollectF_open_memF TOCKSTick_setF)
done

lemma NonTockEv_refusals_TOCKSTick :
    "noTick s \<Longrightarrow> sett s \<subseteq> {Tock,Tick} \<Longrightarrow>
    (s::('e::tockCSP) trace,NonTockEv) :f failures ($TOCKSTick) MF"
  apply (induct s rule: induct_trace)
  apply (simp add: nilt_NonTockEv_in_failures_TOCKSTick)
  apply (insert Tickt_EvsetTick_in_failures_TOCKSTick)
  apply (frule_tac Y=NonTockEv in memF_F2, simp, simp)
  apply (subst failures_TOCKSTick_step)
  apply (simp add: CollectF_open_memF TOCKSTick_setF)
done



subsubsection \<open> failures included in TOCKSTick \<close>


lemma failures_included_in_FIX_TOCKSTick_lm :
    "( (sett t \<subseteq> {Tock} \<and> (Tock \<in> X \<longrightarrow> X \<subseteq> Evset)) \<or>
       (EX s. sett s \<subseteq> {Tock} & t = s ^^^ <Tick>) ) \<longrightarrow>
     (t,X) :f failures ((FIX TOCKSTickfun) (TOCKSTick)) MF"
  apply (induct t rule: induct_trace)
  
   (* <> *)
  apply (rule)
  apply (erule disjE)
  apply (simp add: FIX_def in_failures)
  apply (rule_tac x="Suc 0" in exI)
  apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)
  apply (simp add: FIX_def in_failures)
  apply (rule_tac x="Suc 0" in exI)
  apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)
  apply (rule, elim exE conjE, frule noTick_if_sett_Tock, simp)

   (* <Tick> *)
  apply (rule)
  apply (simp add: FIX_def in_failures)
  apply (rule_tac x="Suc 0" in exI)
  apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)
  
   (* <Ev a> ^^^ s *)
  apply (rule)
  apply (simp add: FIX_def in_failures)
  apply (elim disjE)
    apply (simp, elim conjE, simp, elim exE)
      apply (rule_tac x="Suc n" in exI)
      apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)
    apply (elim exE conjE, simp)
      apply (frule noTick_if_sett_Tock)
      apply (drule subset_singletonD, simp add: sett_empty_iff)
      apply (erule disjE, simp)
      apply (simp add: appt_decompo)
      apply (elim disjE exE)
        apply (rotate_tac 1)
        apply (erule impE, rule_tac x="u" in exI, simp)
      apply (elim exE)
        apply (rule_tac x="Suc n" in exI)
        apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)
        apply (rule_tac x="u ^^^ <Tick>" in exI, simp)
        apply (simp add: appt_assoc)
      apply (elim conjE)
      apply (case_tac "u = <Ev a>", simp, simp)
        apply (rule_tac x="Suc 1" in exI)
        apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)
done

lemma failures_included_in_FIX_TOCKSTick :
    "[| (sett t \<subseteq> {Tock} \<and> (Tock \<in> X \<longrightarrow> X \<subseteq> Evset)) \<or> (EX s. sett s \<subseteq> {Tock} & t = s ^^^ <Tick>) |] ==>
     (t,X) :f failures ((FIX TOCKSTickfun) (TOCKSTick)) MF"
by (simp add: failures_included_in_FIX_TOCKSTick_lm)

lemma failures_included_in_TOCKSTick :
    "[| (sett t \<subseteq> {Tock} \<and> (Tock \<in> X \<longrightarrow> X \<subseteq> Evset)) \<or> (EX s. sett s \<subseteq> {Tock} & t = s ^^^ <Tick>) |] ==>
     (t,X) :f failures ($TOCKSTick::(TOCKSTickPN,'e::tockCSP) proc) MF"
  apply (subst FIX_failures[of TOCKSTickfun])
  apply (case_tac FPmode, simp_all)
by (simp add: failures_included_in_FIX_TOCKSTick)




subsubsection \<open> failures TOCKSTick iff \<close>

(*
     (sett t \<subseteq> {Tock} \<and> (Tock \<in> X \<longrightarrow> X \<subseteq> Evset)) \<or> (EX s. sett s \<subseteq> {Tock} & t = s ^^^ <Tick>)
*)

lemma in_failures_TOCKSTick_E:
    "(t,X) :f failures ($TOCKSTick::(TOCKSTickPN,'e::tockCSP) proc) MF \<Longrightarrow>
     (sett t \<subseteq> {Tock} \<and> (Tock \<in> X \<longrightarrow> X \<subseteq> Evset)) \<or> (EX s. sett s \<subseteq> {Tock} & t = s ^^^ <Tick>)"
  apply (induct t rule: induct_trace)

  apply (simp add: in_failures_TOCKSTick)

  apply (simp add: in_failures_TOCKSTick)
  apply (rule_tac x="<>" in exI, simp)

  apply (case_tac "a \<noteq> tock")
  apply (simp add: in_failures_TOCKSTick)

  apply (subst (asm) failures_TOCKSTick_step)
  apply (simp add: CollectF_open_memF TOCKSTick_setF)
  apply (elim disjE exE)
  apply (rule disjI1, simp)
  apply (rule disjI2)
    apply (rule_tac x="<Tock> ^^^ sa" in exI, simp)
    apply (insert noTick_Ev[of tock])
    apply (case_tac "noTick sa")
    apply (simp add: appt_assoc)
    apply (simp only: noTick_def subset_iff)
    apply (drule_tac x="Tick" in spec, simp)
done


lemma in_failures_TOCKSTick_iff_sett :
    "(t,X) :f failures ($TOCKSTick::(TOCKSTickPN,'e::tockCSP) proc) MF \<longleftrightarrow>
     (sett t \<subseteq> {Tock} \<and> (Tock \<in> X \<longrightarrow> X \<subseteq> Evset)) \<or> (EX s. sett s \<subseteq> {Tock} & t = s ^^^ <Tick>)"
  apply (rule iffI)
  apply (simp add: in_failures_TOCKSTick_E)
  apply (simp add: failures_included_in_TOCKSTick)
done




subsubsection \<open> \<close>


lemma nonexists_in_failures_FIXn_TOCKSTick :
    "noTick s \<Longrightarrow>
     ~ (\<exists>n. (s, EvsetTick)
           :f failures ((FIX[n] TOCKSTickfun) TOCKSTick) MF)"
  apply (induct s rule: induct_trace)
  apply (simp_all)
  apply (rule, induct_tac n)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)
  apply (rule, induct_tac n)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)
done


lemma nonexists_in_failures_FIX_TOCKSTick :
    "noTick s \<Longrightarrow>
     ~ ((s, EvsetTick)
           :f failures ((FIX TOCKSTickfun) TOCKSTick) MF)"
  apply (simp only: FIX_def in_failures Bex_def)
  apply (frule nonexists_in_failures_FIXn_TOCKSTick, simp)
done


lemma nonexists_in_failures_TOCKSTick :
    "noTick s \<Longrightarrow>
     ~ ((s, EvsetTick)
           :f failures ($TOCKSTick::(TOCKSTickPN,'e::tockCSP) proc) MF)"
  apply (subst FIX_failures[of TOCKSTickfun])
  apply (case_tac FPmode, simp_all)
by (rule nonexists_in_failures_FIX_TOCKSTick)






lemma nontock_notin_if_in_failures_TOCKSTick :
    "(e::'e::tockCSP) \<noteq> tock \<Longrightarrow>
     (s,X) :f failures ($TOCKSTick) MF \<Longrightarrow>
     Ev e \<notin> sett s"
  apply (induct s rule: induct_trace)
  apply (simp)
  apply (simp)
  apply (subst (asm) failures_TOCKSTick_step)
  apply (simp add: CollectF_open_memF TOCKSTick_setF)
done



subsubsection \<open> TOCKSTick ref only if \<close>


lemma TOCKSTick_ref_P_Hiding_only_if :
    "$TOCKSTick <=F P -- Nontock \<Longrightarrow>
    \<forall>s X. (\<exists>sa. s =tocks(sa) \<and>
                (sa, NonTickTockEv \<union> X) :f failures P MF) \<longrightarrow>
          s = <> \<and> Tock \<notin> X \<or>
          (\<exists>sa. s = <Tock> ^^^ sa \<and> (sa, X) :f sndF (MF TOCKSTick)) \<or>
          s = <> \<and> X \<subseteq> Evset \<or> s = <Tick>"
  apply (simp add: cspF_refF_semantics subsetF_iff, elim conjE)
by (simp add: in_failures_Hiding hide_tr_sym in_failures_TOCKSTick)









subsection \<open> TOCKSTick to TOCKS \<close>

lemma TOCKSTick_to_TOCKS :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    $TOCKSTick <=F (($TOCKS)::(TOCKSPN,'event::tockCSP) proc)"
  apply (rule_tac Pf="TOCKSTickfun" and f="\<lambda>p. $TOCKS" in cspF_fp_induct_ref_left)
  apply (simp, case_tac FPmode, simp_all)
                                                                      
  apply (induct_tac p, simp)
  apply (cspF_unwind_right)
  apply (rule cspF_Int_choice_left1)
by (cspF_step)


lemma failures_TOCKS_to_failures_TOCKSTick :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
     noTick (t::'e::tockCSP trace) \<Longrightarrow>
     (t,X) :f failures ($TOCKS) MF \<Longrightarrow>
     (t,X) :f failures ($TOCKSTick) MF"
  apply (insert TOCKSTick_to_TOCKS)
  apply (simp add: cspF_semantics)
  apply (erule conjE, erule subsetFE)
by (fast)


lemma failures_TOCKSTick_to_failures_TOCKS :
    "noTick (t::'e::tockCSP trace) \<Longrightarrow> Tock \<notin> X \<Longrightarrow>
     (t,X) :f failures ($TOCKSTick) MF \<Longrightarrow>
     (t,X) :f failures ($TOCKS) MF"
  apply (induct t rule: induct_trace)
  apply (simp add: failures_TOCKSTick_to_TOCKSTickfun)
  apply (subst (asm) in_failures)
  apply (elim disjE)
  apply (subst (asm) in_failures)
  apply (elim disjE exE conjE, simp)
  apply (simp add: in_failures_TOCKS)
  apply (simp add: in_failures_TOCKS)
  apply (simp add: in_failures_TOCKS)
  apply (simp add: in_failures_TOCKS)
  apply (simp)
  apply (subst (asm) failures_TOCKSTick_step)
  apply (simp add: CollectF_open_memF TOCKSTick_setF)
  apply (subst failures_TOCKS_step)
  apply (simp add: CollectF_open_memF TOCKS_setF)
done





subsection \<open> TOCKSTick Parallel preterm \<close>


lemma Ev_notin_nilt :
    "Ev e \<notin> sett <>"
by (simp)

lemma Ev_notin_Tickt :
    "Ev e \<notin> sett <Tick>"
by (simp)




lemma Diff_NontockEv_iff : "(Y - NonTockEv = Z - NonTockEv) = ((Tock \<in> Y) = (Tock \<in> Z))"
by (auto)

lemma Diff_non_e_non_tock_iff :
    "(Y - insert Tick (Ev ` (- {e, tock})) = Z - insert Tick (Ev ` (- {e, tock}))) =
    ( ((Tock \<in> Y) = (Tock \<in> Z)) \<and> ((Ev e \<in> Y) = (Ev e \<in> Z)) )"
  apply (simp add: image_def Bex_def)
  apply (rule)
  apply (fast)
  
  apply (rule)
  apply (rule, simp)
  apply (case_tac x, simp)
  apply (case_tac "x1 = e", simp, force, force)
  apply (rule, simp)
  apply (case_tac x, simp)
  apply (case_tac "x1 = e", simp, force, force)
done

lemma Tock_notin_Ev_Compl_e_tock [simp]: " Tock \<notin> Ev ` (- {e, tock})"
by (auto)


lemma failures_TOCKSTick_Parallel_preterm_iff :
    "failures ($TOCKSTick |[- {(e::'e::tockCSP), tock}]| SKIP) MF =
     failures ($TOCKSTick |[Nontock]| SKIP) MF"
  apply (case_tac "e = tock", simp)

  apply (subst failures_iff, subst failures_iff)
  apply (rule sym, rule trans, subst failures_iff, subst failures_iff, simp, rule sym)
  apply (simp add: Abs_setF_inject Parallel_setF)
  apply (simp add: CollectF_open_memF SKIP_setF)

  apply (simp add: Diff_NontockEv_iff Diff_non_e_non_tock_iff)

  apply (simp add: conj_left_commute conj_disj_distribL ex_disj_distrib)
  apply (simp add: par_tr_nil)
  apply (simp add: par_tr_Tick)
  apply (rule Collect_cong)
  apply (rule disj_cong)

  apply (rule)
    apply (elim exE conjE, simp)
    apply (simp add: in_failures_TOCKSTick_iff_sett)
    apply (simp add: subset_singleton_iff sett_empty_iff)
    apply (rule_tac x=Y in exI, simp)
    apply (rule_tac x=Z in exI, simp)
    apply (elim disjE conjE exE, simp, simp, simp)
    apply (case_tac "noTick s", simp, simp add: noTick_def)

    apply (elim exE conjE, simp)
    apply (simp add: in_failures_TOCKSTick_iff_sett)
    apply (simp add: subset_singleton_iff sett_empty_iff)
    apply (case_tac "(Ev e) \<in> Y")
      apply (rule_tac x="Y" in exI, simp)
      apply (rule_tac x="insert (Ev e) Z" in exI, simp)
      apply (rule, fast)
      apply (elim disjE conjE exE, simp_all add: Evset_def)
      apply (case_tac "noTick s", simp, simp add: noTick_def)

    apply (case_tac "(Ev e) \<in> Z")
      apply (rule_tac x="insert (Ev e) Y" in exI, simp)
      apply (rule_tac x="Z" in exI, simp)
      apply (rule, fast)
      apply (elim disjE conjE exE, simp_all add: Evset_def)
      apply (case_tac "noTick s", simp, simp add: noTick_def)

    apply (rule_tac x=Y in exI, simp)
    apply (rule_tac x=Z in exI, simp)
    apply (elim disjE conjE exE, simp, simp, simp)
    apply (case_tac "noTick s", simp, simp add: noTick_def)


  apply (rule)

    apply (elim exE conjE, simp)
    apply (simp add: in_failures_TOCKSTick_iff_sett)
    apply (simp add: subset_singleton_iff sett_empty_iff)
    apply (rule_tac x=Y in exI, simp)
    apply (rule_tac x=Z in exI, simp)
    apply (elim disjE conjE exE, simp, simp, simp)
    apply (case_tac "noTick s", simp, simp add: noTick_def)

    apply (elim exE conjE, simp)
    apply (simp add: in_failures_TOCKSTick_iff_sett)
    apply (simp add: subset_singleton_iff sett_empty_iff)
    apply (case_tac "(Ev e) \<in> Y")
      apply (rule_tac x="Y" in exI, simp)
      apply (rule_tac x="insert (Ev e) Z" in exI, simp)
      apply (rule, fast)
      apply (elim disjE conjE exE, simp_all add: Evset_def)
      apply (case_tac "noTick s", simp, simp add: noTick_def)

    apply (case_tac "(Ev e) \<in> Z")
      apply (rule_tac x="insert (Ev e) Y" in exI, simp)
      apply (rule_tac x="Z" in exI, simp)
      apply (rule, fast)
      apply (elim disjE conjE exE, simp_all add: Evset_def)
      apply (case_tac "noTick s", simp, simp add: noTick_def)

    apply (rule_tac x=Y in exI, simp)
    apply (rule_tac x=Z in exI, simp)
    apply (elim disjE conjE exE, simp, simp, simp)
    apply (case_tac "noTick s", simp, simp add: noTick_def)
done


lemma cspF_TOCKSTick_Parallel_preterm :
    "(e::'e::tockCSP) \<noteq> tock \<Longrightarrow>
     $TOCKSTick |[- {e, tock}]| SKIP =F $TOCKSTick |[Nontock]| SKIP"
  apply (simp add: cspF_cspT_semantics, rule)
  apply (simp add: fstF_MF_MT)
  apply (simp add: cspT_TOCKSTick_Parallel_preterm)
  apply (simp add: failures_TOCKSTick_Parallel_preterm_iff)
done




(*
lemma Diff_TickTock_iff : "(Y - {Tick,Tock} = Z - {Tick,Tock}) = (\<forall>x. x \<noteq> Tock \<and> x \<noteq> Tick \<longrightarrow> (x \<in> Y) = (x \<in> Z))"
by (auto)


lemma Diff_Tick_iff : "(Y - {Tick} = Z - {Tick}) = (\<forall>x. x \<noteq> Tick \<longrightarrow> (x \<in> Y) = (x \<in> Z))"
by (auto)


lemma failures_TOCKSTick_Parallel_preterm_iff :
    "failures ($TOCKSTick |[{tock}]| SKIP) MF =
     failures (SKIP) MF"
  apply (subst failures_iff)
  apply (subst failures_iff)
  apply (subst Abs_setF_inject)

  (* Parallel_setF*)
  apply (simp add: Parallel_setF)
    apply (simp add: setF_def HC_F2_def)
    apply (intro allI impI)
    apply (elim conjE exE, simp)
    apply (rename_tac u Y Z Y1 Y2 s t)
    apply (rule_tac x="Z Int (Y1 - (Y2 - {Tick,Tock})) Un
                       Z Int (Y2 - {Tick,Tock})" in exI)
    apply (rule_tac x="Z Int (Y2 - (Y2 - {Tick,Tock})) Un
                       Z Int (Y2 - {Tick,Tock})" in exI)
    apply (rule conjI, force)
    apply (rule conjI, force)
    
    apply (rule_tac x="s" in exI)
    apply (rule_tac x="t" in exI)
    apply (simp)
    apply (rule conjI)
    apply (rule memF_F2, simp, force)+
  apply (simp add: SKIP_setF)
  apply (subst failures_iff)
  apply (simp add: CollectF_open_memF SKIP_setF)

  apply (simp add: Diff_TickTock_iff)

  apply (simp add: conj_left_commute conj_disj_distribL ex_disj_distrib)
  apply (simp add: par_tr_nil)                 
  apply (simp add: par_tr_Tick)
  apply (rule Collect_cong)
  apply (rule disj_cong)

  apply (rule)
    apply (elim exE conjE, simp)
    apply (simp add: in_failures_TOCKSTick_iff_sett)
    apply (simp add: subset_singleton_iff sett_empty_iff)
    apply (elim disjE conjE exE, simp_all add: Evset_def)
    apply (case_tac "Tock \<in> Y", simp, simp)


lemma cspF_TOCKSTick_Parallel_preterm :
    "$TOCKSTick |[ {tock} ]| SKIP =F SKIP"
  apply (simp add: cspF_cspT_semantics, rule)
  apply (simp add: fstF_MF_MT)

*)

end