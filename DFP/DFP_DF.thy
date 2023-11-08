           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021               |
            |                  2022 / 2023 (modified)   |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_DF
imports DFP_Deadlock
        DFP_noTick
begin



section \<open> The Non-Terminating Deadlock-free DF Process \<close>

subsection \<open> Roscoe's DF process \<close>

datatype DFPN = DF'

primrec DFfun :: "(DFPN, 'event) pnfun"
where
  "DFfun (DF') = (! x ->  $(DF')) "

overloading Set_DFfun == 
  "PNfun :: (DFPN, 'event) pnfun"
begin
  definition "PNfun :: (DFPN, 'event) pnfun == DFfun"
end
  
declare Set_DFfun_def [simp]



lemma guardedfun_DFfun [simp]: "guardedfun DFfun"
  apply (simp add: guardedfun_def)
by (rule allI, induct_tac p, simp)



definition DF :: "(DFPN, 'event) proc"
where
    "DF == $DF'"






subsection \<open> traces DF \<close>

lemma DFfun_eqT_DF' : 
  "((DFfun (DF'))::(DFPN, 'e) proc) =T $DF'"
by (cspT_unwind)

lemmas DF'_eqT_DFfun = DFfun_eqT_DF'[THEN cspT_sym]


lemma traces_DF'_eq_DFfun :
    "traces (($DF')::(DFPN, 'e) proc) MT = traces ((DFfun (DF'))::(DFPN, 'e) proc) MT"
  apply (insert DF'_eqT_DFfun)
by (simp add: cspT_semantics)


lemma traces_DF_eq_DFfun :
    "traces (DF::(DFPN, 'e) proc) MT = traces ((DFfun (DF'))::(DFPN, 'e) proc) MT"
by (simp add: DF_def traces_DF'_eq_DFfun)



subsection \<open> in traces DF fixed point (FIX) \<close>

lemma in_traces_FIX_DFfun_DF'_lm:
    "(sett t \<subseteq> Ev ` A) \<longrightarrow> t :t traces ((FIX DFfun) ((DF')::DFPN)) M"
  apply (induct_tac t rule: induct_trace)
  
    (* <> *)
    apply (simp)
    
    (* <Tick> *)
    apply (simp add: noTick_def image_def)
    
    (* <Ev a>^^^s *)
    apply (case_tac "a : A")

    apply (intro impI)
    apply (simp add: FIX_def)
    apply (simp add: in_traces)
    
    apply (erule disjE)
    apply (simp)
    apply (rule_tac x="Suc 0" in exI)
    apply (simp add: FIXn_def)
    apply (simp add: Subst_procfun_prod_def)
    apply (simp add: Int_pre_choice_def)
    apply (simp add: in_traces)

    apply (erule exE)
    apply (rule_tac x="Suc n" in exI)
    apply (simp add: FIXn_def)
    apply (simp add: Subst_procfun_prod_def)
    apply (simp add: Int_pre_choice_def)
    apply (simp add: in_traces)

    apply (force)
done

lemma in_traces_FIX_DFfun_DF':
  "sett t \<subseteq> Ev ` A \<Longrightarrow> t :t traces ((FIX DFfun) (DF')) M"
by (simp add: in_traces_FIX_DFfun_DF'_lm)




subsection \<open> in traces DF scenarios \<close>

lemma Tickt_notin_traces_DF' : "<Tick> ~:t traces (($DF')::(DFPN, 'e) proc) MT"
  apply (simp add: traces_DF'_eq_DFfun)
  apply (simp add: Int_pre_choice_def in_traces)
done

lemma not_noTick_notin_traces_DF' : "\<not> noTick s \<Longrightarrow> s ~:t traces (($DF')::(DFPN, 'e) proc) MT"
  apply (induct s rule: induct_trace)
  apply (simp)
  apply (simp add: Tickt_notin_traces_DF')
  apply (simp (no_asm) add: traces_DF'_eq_DFfun)
  apply (simp add: Int_pre_choice_def)
  apply (subst in_traces, simp)
  apply (subst in_traces, simp)
done

lemma Tickt_notin_traces_DF : "<Tick> ~:t traces DF MT"
by (simp add: DF_def Tickt_notin_traces_DF')

lemma not_noTick_notin_traces_DF : "\<not> noTick s \<Longrightarrow> s ~:t traces (DF::(DFPN, 'e) proc) MT"
by (simp add: DF_def not_noTick_notin_traces_DF')


lemma one_appt_in_traces_DF' :
    "<Ev a> ^^^ t :t traces (($DF')::(DFPN, 'e) proc) MT \<Longrightarrow> t :t traces ($DF') MT"
  apply (subst (asm) traces_DF'_eq_DFfun)
  apply (simp add: Int_pre_choice_def)
  apply (subst (asm) in_traces, simp)
  apply (subst (asm) in_traces, simp)
done


lemma one_appt_in_traces_DF :
    "<Ev a> ^^^ t :t traces (DF::(DFPN, 'e) proc) MT \<Longrightarrow> t :t traces DF MT"
by (simp add: DF_def one_appt_in_traces_DF')


lemma tail_closed_traces_DF' :
    "s ^^^ t :t traces (($DF')::(DFPN, 'e) proc) MT \<Longrightarrow> noTick s \<Longrightarrow> t :t traces ($DF') MT"
  apply (induct s arbitrary: t rule: induct_trace)
  apply (simp)
  apply (simp)
  apply (drule decompo_one_appt_noTick)
  apply (subst (asm) appt_assoc, simp, simp)
  apply (drule_tac t="s ^^^ t" in one_appt_in_traces_DF', simp)
done

lemma tail_closed_traces_DF :
    "s ^^^ t :t traces (DF::(DFPN, 'e) proc) MT \<Longrightarrow> noTick s \<Longrightarrow> t :t traces DF MT"
apply (simp add: DF_def)
by (rule_tac s=s in tail_closed_traces_DF', simp_all add: Evset_def)


subsection \<open> in traces DF \<close>

lemma in_traces_DF':
    "sett t \<subseteq> Ev ` A \<Longrightarrow> t :t traces (($DF')) MT"
  apply (simp add: FIX_traces)
by (simp add: in_traces_FIX_DFfun_DF')

lemma in_traces_DF'_if_noTick :
    "noTick (s::'e trace) \<Longrightarrow> s :t traces ($DF') MT"
  apply (frule sett_subset_Ev_image_if_noTick)
  apply (erule exE)
  apply (simp add: in_traces_DF')
done

lemma in_traces_DF_lm:
    "noTick t \<longrightarrow> t :t traces DF MT"
  apply (simp add: DF_def, rule)
  apply (frule sett_subset_Ev_image_if_noTick)
  apply (erule exE)
  apply (simp add: in_traces_DF')
done

lemma in_traces_DF:
    "noTick t \<Longrightarrow> t :t traces DF MT"
by (simp add: in_traces_DF_lm)



lemma in_traces_DF'_only_if :
    "s :t traces ($DF') MT \<Longrightarrow> \<exists>A. sett s \<subseteq> Ev ` A"
  apply (induct s rule: induct_trace)
  apply (simp)
  apply (simp add: Tickt_notin_traces_DF')
  apply (simp)
  apply (subst (asm) traces_DF'_eq_DFfun)
  apply (simp add: Int_pre_choice_def)
  apply (subst (asm) in_traces, simp)
  apply (subst (asm) in_traces, simp)
  apply (erule exE, blast)
done


lemma in_traces_DF'_only_if_noTick :
    "s :t traces ($DF') MT \<Longrightarrow> noTick s"
  apply (frule in_traces_DF'_only_if)
  apply (erule exE)
by (simp add: noTick_if_sett_subset_Ev_image)


lemma in_traces_DF'_iff :
    "s :t traces ($DF') MT = (\<exists>A. sett s \<subseteq> Ev ` A)"
  apply (rule iffI)
  apply (simp add: in_traces_DF'_only_if)
  apply (erule exE, simp add: in_traces_DF')
done


lemma in_traces_DF_iff_noTick : "s :t traces (DF::(DFPN, 'e) proc) MT = noTick (s::'e trace)"
  apply (simp add: DF_def)
  apply (rule trans, rule in_traces_DF'_iff)
  apply (rule sett_subset_Ev_image_iff_noTick)
done

(*lemmas noTick_iff_in_traces_DF = in_traces_DF_iff_noTick[THEN sym]*)




subsection \<open> failures DF' \<close>


lemma DFfun_eqF_DF' : 
  "DFfun (DF') =F $DF'"
by (cspF_unwind)

lemmas DF'_eqF_DFfun = DFfun_eqF_DF'[THEN cspF_sym]
                  

lemma failures_DF'_eq_DFfun :
    "failures ($DF') MF = failures (DFfun (DF')) MF"
  apply (insert DF'_eqF_DFfun)
  apply (simp add: cspF_eqF_semantics)
by (elim conjE, simp)





subsection \<open> in failures DF' fixed point (FIX) \<close>

lemma in_failures_FIX_DFfun_DF'_lm:
    "(sett t \<subseteq> Ev ` A & (\<exists>a. Ev a \<notin> X)) -->
     (t,X) :f failures ((FIX DFfun) (DF')) M"
  apply (induct_tac t rule: induct_trace)

  (* <> *)
    apply (intro impI conjI)
    apply (simp add: FIX_def in_failures)
    apply (rule_tac x="Suc 0" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def Int_pre_choice_def in_failures)

  (* <Tick> *)
    apply (simp add: noTick_def image_def)

  (* <Ev a> ^^^ s *)
    apply (intro impI)
    apply (elim conjE)
    apply (simp add: FIX_def in_failures)

    apply (elim exE)

    apply (rule_tac x="Suc n" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def Int_pre_choice_def in_failures)
done

lemma in_failures_FIX_DFfun_DF':
  "[| sett t \<subseteq> Ev ` A ; (\<exists>a. Ev a \<notin> X) |] ==>
   (t,X) :f failures ((FIX DFfun) (DF')) M"
by (simp add: in_failures_FIX_DFfun_DF'_lm)



subsection \<open> in failures DF' \<close>

lemma in_failures_DF'_a:
    "[| sett t \<subseteq> Ev ` A ; (\<exists>a. Ev a \<notin> X) |] ==>
     (t,X) :f failures (($DF')::(DFPN, 'e) proc) MF"
  apply (simp add: FIX_failures)
by (simp add: in_failures_FIX_DFfun_DF'_lm)

lemma in_failures_DF'_b:
    "[| noTick t ; (\<exists>a. Ev a \<notin> X) |] ==>
     (t,X) :f failures (($DF')::(DFPN, 'e) proc) MF"
  apply (simp add: FIX_failures)
  apply (simp add: noTick_iff_sett_subset_Evset Evset_eq_Ev_UNIV)
by (simp add: in_failures_FIX_DFfun_DF'_lm)

lemmas in_failures_DF' = in_failures_DF'_a
                         in_failures_DF'_b

lemma in_failures_DF_a:
    "[| sett t \<subseteq> Ev ` A ; (\<exists>a. Ev a \<notin> X) |] ==>
     (t,X) :f failures (DF::(DFPN, 'e) proc) MF"
by (simp add: DF_def in_failures_DF')

lemma in_failures_DF_b:
    "[| noTick t; \<exists>a. Ev a \<notin> X |] ==>
     (t,X) :f failures (DF::(DFPN, 'e) proc) MF"
by (simp add: DF_def in_failures_DF')

lemmas in_failures_DF = in_failures_DF_a
                        in_failures_DF_b



subsection \<open> in failures DF scenarios \<close>

lemma Tickt_notin_failures_DF' : "(<Tick>,X) ~:f failures (($DF')::(DFPN, 'e) proc) MF"
  apply (simp add: failures_DF'_eq_DFfun)
  apply (simp add: Int_pre_choice_def in_failures)
done


lemma one_appt_in_failures_DF' :
    "(<Ev a> ^^^ t,X) :f failures (($DF')::(DFPN, 'e) proc) MF \<Longrightarrow> (t,X) :f failures ($DF') MF"
  apply (subst (asm) failures_DF'_eq_DFfun)
  apply (simp add: Int_pre_choice_def)
  apply (subst (asm) in_failures)
  apply (subst (asm) in_failures, simp)
done

lemma tail_closed_failures_DF' :
    "(s ^^^ t,X) :f failures (($DF')::(DFPN, 'e) proc) MF \<Longrightarrow> noTick s \<Longrightarrow>
     (t,X) :f failures ($DF') MF"
  apply (induct s rule: induct_trace)
  apply (simp_all)

  apply (simp add: appt_assoc)
by (simp add: one_appt_in_failures_DF')


lemma in_failures_DF'_only_if_EX_nonTick_refusal :
    "(s, X) :f failures (($DF')::(DFPN, 'e) proc) MF \<Longrightarrow> \<exists> a. Ev a \<notin> X"
  apply (induct s rule: induct_trace)
  
  apply (simp add: failures_DF'_eq_DFfun)
  apply (simp add: Int_pre_choice_def in_failures)
  
  apply (simp add: failures_DF'_eq_DFfun)
  apply (simp add: Int_pre_choice_def in_failures)
  
  apply (simp add: failures_DF'_eq_DFfun)
  apply (simp add: Int_pre_choice_def)
  apply (subst (asm) in_failures)
  apply (subst (asm) in_failures, simp)
  apply (simp add: failures_DF'_eq_DFfun)
  apply (simp add: Int_pre_choice_def)
done


lemma Evset_refusals_notin_failures_DF' :
    "(s, Evset) ~:f failures (($DF')::(DFPN, 'e) proc) MF"
  apply (induct_tac s rule: induct_trace)
  
  apply (simp add: failures_DF'_eq_DFfun)
  apply (simp add: Int_pre_choice_def in_failures)
  apply (simp add: Evset_def)
  
  apply (simp add: failures_DF'_eq_DFfun)
  apply (simp add: Int_pre_choice_def in_failures)
  
  apply (simp add: failures_DF'_eq_DFfun)
  apply (simp add: Int_pre_choice_def)
  apply (subst in_failures, simp)
  apply (subst in_failures, simp)
  apply (simp add: failures_DF'_eq_DFfun)
  apply (simp add: Int_pre_choice_def)
done


lemma UNIV_refusals_notin_failures_DF' :
    "(s, UNIV) ~:f failures (($DF')::(DFPN, 'e) proc) MF"
  apply (induct_tac s rule: induct_trace)
  
  apply (simp add: failures_DF'_eq_DFfun)
  apply (simp add: Int_pre_choice_def in_failures)
  
  apply (simp add: failures_DF'_eq_DFfun)
  apply (simp add: Int_pre_choice_def in_failures)
  
  apply (simp add: failures_DF'_eq_DFfun)
  apply (simp add: Int_pre_choice_def)
  apply (subst in_failures, simp)
  apply (subst in_failures, simp)
  apply (simp add: failures_DF'_eq_DFfun)
  apply (simp add: Int_pre_choice_def)
done




(*
lemma Evset_subset_iff : "(Evset \<subseteq> X) = (X = Evset \<or> X = UNIV)"
  apply (auto simp add: Evset_def subset_iff)
by (case_tac x, fast, fast)


lemma not_full_refusing1 :
    "X \<noteq> UNIV \<Longrightarrow> ~ Evset \<subseteq> X \<Longrightarrow>
     \<exists>a. Ev a \<notin> X"
      apply (simp add: set_eq_iff Evset_def subset_iff)
      apply (elim conjE disjE exE)
      apply (case_tac t, fast, fast)
done


lemma not_full_refusing2 :
    "X \<noteq> UNIV \<Longrightarrow> Tick : X \<Longrightarrow>
     \<exists>a. Ev a \<notin> X"
      apply (simp add: set_eq_iff subset_iff)
      apply (elim conjE disjE exE)
      apply (case_tac x, fast, fast)
done


lemmas not_full_refusing =  not_full_refusing1 not_full_refusing2

lemma refusing_Tick : "~ X \<subseteq> Evset \<Longrightarrow> Tick : X"
  by (simp add: Evset_def subset_iff)

lemma not_refusing_an_Ev : "~ X \<subseteq> Evset \<Longrightarrow> X \<noteq> UNIV \<Longrightarrow> \<exists>a. Ev a \<notin> X"
  apply (simp add: Evset_def subset_iff set_eq_iff)
  apply (elim exE)
  apply (case_tac x, fast, fast)
done

lemma not_refusing_UNIV : "X \<noteq> UNIV \<Longrightarrow> Tick \<notin> X \<or> (\<exists>a. Ev a \<notin> X)"
  apply (simp add: Evset_def subset_iff set_eq_iff)
  apply (elim exE)
  apply (case_tac x, fast, fast)
done*)






lemma in_failures_DF'_only_if_noTick :
    "(s, X) :f failures (($DF'):: (DFPN, 'e) proc) MF \<Longrightarrow> noTick s"
  apply (frule_tac P="$DF'" in proc_T2)
by (simp add: fstF_MF_MT in_traces_DF'_only_if_noTick)




section \<open> deadlock-free non-terminating \<close>

lemma DF'_is_NonTickDeadlockFree:
    "(($DF') :: (DFPN, 'e) proc) isNonTickDeadlockFree"
  apply (simp add: NonTickDeadlockFree_def)
  apply (rule allI)
  apply (simp add: Evset_refusals_notin_failures_DF')
done

lemma DF_is_NonTickDeadlockFree:
    "(DF:: (DFPN, 'e) proc) isNonTickDeadlockFree"
by (simp add: DF_def DF'_is_NonTickDeadlockFree)



subsection \<open> semantical approach --> syntactical approach \<close>


lemma DF'_NonTickDeadlockFree:
    "(($DF'):: (DFPN, 'e) proc) <=F P ==> (P::('p, 'e) proc) isNonTickDeadlockFree"
  apply (insert DF'_is_NonTickDeadlockFree)
  apply (simp add: NonTickDeadlockFree_def insert_UNIV)
  apply (simp add: cspF_refF_semantics)
  apply (auto)
done


lemma DF_NonTickDeadlockFree:
    "(DF:: (DFPN, 'e) proc) <=F P ==> (P::('p, 'e) proc) isNonTickDeadlockFree"
by (simp add: DF_def DF'_NonTickDeadlockFree)



lemma NonTickDeadlockFree_DF':
    "P isNonTickDeadlockFree ==> (($DF') :: (DFPN, 'e) proc) <=F (P::('p, 'e) proc)"
  apply (simp add: NonTickDeadlockFree_def)
  apply (simp add: cspF_refF_semantics)
  apply (rule conjI)

  (* trace *)
  apply (simp add: subdomT_iff fstF_MF_MT)
  apply (intro allI impI)
  apply (rule in_traces_DF')
    apply (frule noTick_if_Evset_notin_failures, simp)
    apply (frule sett_subset_Ev_image_if_noTick, force)
  
  (* failures *)
  apply (simp add: subsetF_iff)
  apply (intro allI impI)
  apply (rule in_failures_DF')
    apply (frule noTick_if_Evset_notin_failures, simp)
    apply (frule sett_subset_Ev_image_if_noTick, force)
    (* \<exists>a. Ev a \<notin> X *)
    apply (drule_tac x=s in spec)
      apply (erule contrapos_np, simp)
      apply (rule memF_F2, simp)
      apply (simp add: all_Ev_in_Evset_iff)
done


lemma NonTickDeadlockFree_DF:
    "P isNonTickDeadlockFree ==> ($DF':: (DFPN, 'e) proc) <=F (P::('p, 'e) proc)"
by (simp add: DF_def NonTickDeadlockFree_DF')




subsection \<open> syntactical approach <--> semantical approach \<close>


theorem NonTickDeadlockFree_DF'_ref:
    "P isNonTickDeadlockFree = (($DF':: (DFPN, 'e) proc) <=F P)"
  apply (rule)
  apply (simp add: NonTickDeadlockFree_DF')
  apply (simp add: DF'_NonTickDeadlockFree)
done


theorem NonTickDeadlockFree_DF_ref:
    "P isNonTickDeadlockFree = (($DF':: (DFPN, 'e) proc) <=F P)"
  apply (rule)
  apply (simp add: NonTickDeadlockFree_DF')
  apply (simp add: DF'_NonTickDeadlockFree)
done


end