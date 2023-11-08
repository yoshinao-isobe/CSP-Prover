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

theory TSF_TOCKSTick
imports TSF_law_TimeStop
begin



subsection \<open> semantical approach --> syntactical approach \<close>


lemma refTOCKSTick_if_isTimeStopFree:
    "(P) isTimeStopFree ==>
    ($TOCKSTick :: (TOCKSTickPN, 'event::tockCSP) proc) <=F P -- Nontock"
  apply (simp add: cspF_refF_semantics, rule conjI)
    (* traces *)
    apply (simp add: subdomT_iff)
    apply (intro allI impI)
    apply (simp add: in_traces, elim exE conjE)
    apply (simp (no_asm) add: fstF_MF_iff_traces)
    apply (rule traces_included_in_TOCKSTick)
    apply (simp add: subset_eq)
    (* failures *)
    apply (simp add: subsetF_iff)
    apply (intro allI impI)
    apply (simp add: in_failures hide_tr_sym, elim exE conjE)
    apply (simp add: sndF_MF_iff_failures)

    (*apply (rule_tac X="NonTickTockEv \<union> X" in memF_F2, simp_all)*)
    apply (rule failures_included_in_TOCKSTick)

    (* P isTimeStopFree ==> ... *)
    apply (simp add: TimeStopFree_def)
    apply (simp add: DeadlockFree_def in_failures_Hiding hide_tr_sym)

    apply (frule hide_tr_non_x_sett)
    apply (simp add: subset_doubleton_iff)
    apply (simp add: sett_empty_iff sett_Tick_iff)
    apply (elim disjE, simp_all)

    (* <> *)
    apply (rule)
    apply (case_tac "Tick ~: X", simp add: Evset_def, force, simp)
    apply (drule_tac x="s" in spec, simp)
    apply (drule_tac x="sa" in spec, simp)
    apply (erule contrapos_np, simp, elim conjE)
    apply (drule not_subset_Evset)
    apply (simp only: NonTickTockEv_Un_eq_NonTockEv_Un_if)
    apply (simp only: NonTockEv_Un_eq_EvsetTick_if)

    (* <Tick> *)
    apply (rule_tac x="<>" in exI, simp)

    (* < [Tock]* > *)
    apply (rule)
    apply (rule disjI1)
    apply (drule_tac x="s" in spec, simp)
    apply (drule_tac x="sa" in spec, simp)
    apply (erule contrapos_np)
    apply (drule not_subset_Evset)
    apply (simp only: NonTickTockEv_Un_eq_NonTockEv_Un_if)
    apply (simp only: NonTockEv_Un_eq_EvsetTick_if)

    (* < [Tock]*, Tick > *)
    apply (simp add: sett_doubleton)
  done


subsection \<open> syntactical approach --> semantical approach \<close>


lemma isTimeStopFree_if_refTOCKSTick:
    "($TOCKSTick :: (TOCKSTickPN, 'event) proc) <=F P -- (Nontock) ==>
    (P::('pn,'event::tockCSP) proc) isTimeStopFree"
  apply (simp add: TimeStopFree_def)
  apply (simp add: DeadlockFree_def in_failures_Hiding hide_tr_sym)
  apply (intro allI)
  (* s : traces (P -- Nontock) *)
  apply (induct_tac s rule: induct_trace)
  (* Now we must Prove P cannot refine TOCKSTick and refuse UNIV (i.e., refuses Tock) *)
  (* <> : traces (P -- Nontock) *)
  apply (clarsimp)
    (* s : traces P \<and> s --tr Nontock = <> *)
    (* Thus, s can be any trace excluding Tock and Tick events. *)
    apply (drule TOCKSTick_ref_P_Hiding_only_if)
    apply (drule_tac x="<>" in spec)
    apply (drule_tac x=EvsetTick in spec)
    apply (simp)
    (*apply (erule_tac x="<>" in allE, simp)
    apply (rule_tac x=NonTickTockEv in exI)
    apply (simp add: insert_Tock_NonTickTockEv insert_Tick_Evset)*)

  (* <Tick> : traces (P -- Nontock) *)
  apply (clarsimp)
    (* s : traces P \<and> s --tr Nontock = <Tick> *)
    (* OBS: we are only checking timestops. We are not in failures-divergence model
            to check whether P is well-timed, Thus, P can produce infinitely many
            non-Tock events before Tick. *)
  (* <Ev a> ^^^ s : traces (P -- Nontock) *)
  apply (clarsimp)
    (* sa : traces P \<and> sa --tr Nontock = <Ev a> ^^^ s *)
    apply (drule TOCKSTick_ref_P_Hiding_only_if)

    apply (drule_tac x="s" in spec)
    apply (drule_tac x="<Ev a> ^^^ sa" in spec)
    apply (drule_tac x=EvsetTick in spec)
    apply (simp)
    apply (erule impE, rule_tac x=s in exI, simp)
    apply (elim conjE)
    apply (simp add: sndF_MF_iff_failures)
    apply (simp only: Tick_notin_iff_noTick)
    apply (drule nonexists_in_failures_TOCKSTick, simp)
  done



subsection \<open> syntactical approach <--> semantical approach \<close>

theorem TimeStopFree_TOCKSTick_ref_iff:
    "(P::('pn,'event) proc) isTimeStopFree =
     (($TOCKSTick:: (TOCKSTickPN, 'event::tockCSP) proc) <=F P -- Nontock)"
  apply (rule iffI)
    apply (simp add: refTOCKSTick_if_isTimeStopFree)
    apply (simp add: isTimeStopFree_if_refTOCKSTick)
  done



subsection \<open> TSF for basic processes \<close>

corollary tsf_TOCKSTick :
    "($TOCKSTick:: (TOCKSTickPN, 'event::tockCSP) proc) <=F $TOCKSTick -- Nontock"
  apply (subst TimeStopFree_TOCKSTick_ref_iff[THEN sym])
  by (simp add: TOCKSTick_isTimeStopFree)

corollary tsf_TOCKS :
    "($TOCKSTick:: (TOCKSTickPN, 'event::tockCSP) proc) <=F $TOCKS -- Nontock"
  apply (subst TimeStopFree_TOCKSTick_ref_iff[THEN sym])
  by (simp add: TOCKS_isTimeStopFree)

corollary tsf_SKIP :
    "($TOCKSTick:: (TOCKSTickPN, 'event::tockCSP) proc) <=F SKIP -- Nontock"
  apply (subst TimeStopFree_TOCKSTick_ref_iff[THEN sym])
  by (simp add: SKIP_isTimeStopFree)

corollary tsf_DIV :
    "($TOCKSTick:: (TOCKSTickPN, 'event::tockCSP) proc) <=F DIV -- Nontock"
  apply (subst TimeStopFree_TOCKSTick_ref_iff[THEN sym])
  by (simp add: DIV_isTimeStopFree)

corollary not_tsf_STOP :
    "~ (($TOCKSTick:: (TOCKSTickPN, 'event::tockCSP) proc) <=F STOP -- Nontock)"
  apply (subst TimeStopFree_TOCKSTick_ref_iff[THEN sym])
  by (simp add: not_STOP_isTimeStopFree)


lemmas tsf = not_tsf_STOP
             tsf_TOCKSTick
             tsf_TOCKS
             tsf_SKIP
             tsf_DIV

end