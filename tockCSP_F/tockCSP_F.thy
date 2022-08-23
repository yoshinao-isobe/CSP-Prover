theory tockCSP_F
imports tockCSP_Infra_CSP_F
        tockCSP_T_Main
begin



subsection \<open> TOCKS semantics \<close>


lemmas TOCKS_setF = Act_prefix_setF


lemma cspF_TOCKS :
    "(($TOCKS)::(TOCKSPN, 'event::tockCSP) proc) =F (((TOCKSfun TOCKS))::(TOCKSPN, 'event) proc)"
  by (simp, cspF_unwind)


lemma failures_TOCKS :
    "failures (($TOCKS) :: (TOCKSPN, 'event::tockCSP) proc) MF =
     {f. (\<exists>X. f = (<>, X) \<and> Tock \<notin> X) \<or>
        (\<exists>s X. f = (<Tock> ^^^ s, X) \<and>
               (s, X) :f sndF (MF TOCKS))}f"
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



subsubsection \<open> Roscoe TOCKS = Schneider RUN {tock} \<close>

(* TODO cspF_TOCKS_eq_RUN *)
lemma cspF_TOCKS_eq_RUN :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    RUN : RUNs ==> $TOCKS =F RUN {tock}"
  oops (* missing failures definition for RUNs *)



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


(*lemmas in_failures_TOCKSTick = in_failures_Act_prefix in_failures_Int_choice in_failures_SKIP*)
lemma in_failures_TOCKSTick :
    "((s,X) :f failures ($TOCKSTick) MF) =
     ((s = <> \<and> Tock \<notin> X \<or>
     (\<exists>sa. s = <Tock> ^^^ sa \<and> (sa, X) :f sndF (MF TOCKSTick)) \<or>
     s = <> \<and> X \<subseteq> Evset \<or> s = <Tick>))"
  apply (simp add: failures_TOCKSTick)
  by (simp add: CollectF_open_memF TOCKSTick_setF)


lemma failures_TOCKSTick_to_TOCKSTickfun : 
    "failures (($TOCKSTick)::(TOCKSTickPN, 'event::tockCSP) proc) MF = 
     failures ((TOCKSTickfun TOCKSTick)::(TOCKSTickPN, 'event) proc) MF"
  apply (simp)
  apply (simp add: failures_TOCKSTick)
  apply (simp add: failures_iff)
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



(*t = <> \<longrightarrow> ~ X \<subseteq> Evset \<Longrightarrow>*)
(* Tock \<notin> X \<or> ~ X \<subseteq> Evset \<Longrightarrow>*)
lemma failures_TOCKSTick_to_failures_TOCKS :
    "noTick t \<Longrightarrow>
     (t,X) :f failures ($TOCKSTick) MF \<Longrightarrow>
     (t,X) :f failures (($TOCKS)::(TOCKSPN,'event::tockCSP) proc) MF"
  apply (simp add: in_failures_TOCKSTick in_failures_TOCKS)
  apply (case_tac "t = <Tick>", simp, simp)
  apply (elim disjE)
    apply (simp_all)
    apply (rule disjI2)
    apply (elim exE conjE, rule_tac x=sa in exI, simp)
    apply (simp add: MF_def)

  oops (*TODO finish failures_TOCKSTick_to_failures_TOCKS*)



end