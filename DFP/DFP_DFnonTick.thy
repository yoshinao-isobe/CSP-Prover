           (*-------------------------------------------*
            |                     DF A                  |
            |                                           |
            |                 2022 / 2023               |
            |                                           |
            |        CSP-Prover on Isabelle2021         |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_DFnonTick
imports DFP_law_DFtick
        DFP_noTick
begin


section \<open> The Non-Terminating Deadlock-free Alphabetised (DF(A)) Process \<close>

text \<open> Roscoe's DF(A) process \<close>

datatype ('event) DFalphaPN = DF' "'event set"

primrec DFalphafun :: "('event DFalphaPN, 'event) pnfun"
where
  "DFalphafun (DF' A) = (! x:A ->  $(DF' A)) "

overloading Set_DFalphafun == 
  "PNfun :: ('event DFalphaPN, 'event) pnfun"
begin
  definition "PNfun :: ('event DFalphaPN, 'event) pnfun == DFalphafun"
end

declare Set_DFalphafun_def [simp]



lemma guardedfun_DFalphafun [simp]: "guardedfun DFalphafun"
  apply (simp add: guardedfun_def)
by (rule allI, induct_tac p, simp)



(*abbreviation DF :: "'event set \<Rightarrow> ('event DFalphaPN, 'event) proc"
where
    "DF(A) == $(DF' A)"*)




subsection \<open> deadlock-free \<close>

fun DF_induct_Hypotheses :: "'e DFalphaPN \<Rightarrow> (DFtickName, 'e) proc"
where
    "DF_induct_Hypotheses (DF' A) = $DFtick"

lemma Lemma_DFalphaPN_To_DFtick :
    "DF_induct_Hypotheses p \<sqsubseteq>F (DFalphafun p) << DF_induct_Hypotheses"
  apply (induct_tac p, simp, cspF_unwind, rule cspF_Int_choice_left1, cspF_auto)
  apply (rule cspF_decompo_ref, simp_all)
done

lemma dfp_DF': "($DFtick::(DFtickName, 'e) proc) <=F ($(DF' A)::('e DFalphaPN,'e)proc)"
  apply (rule_tac Pf="DFalphafun" and f="DF_induct_Hypotheses" in cspF_fp_induct_ref_right)
  apply (simp, case_tac FPmode, simp_all)
  apply (rule Lemma_DFalphaPN_To_DFtick)
done


lemma DF'_is_DeadlockFree: "($(DF' A)::('e DFalphaPN,'e)proc) isDeadlockFree"
  apply (simp add: DeadlockFree_DFtick_ref)                         
by (rule dfp_DF')


lemma DF'_DeadlockFree:
    "($(DF' A)::('e DFalphaPN,'e)proc) <=F P ==> P isDeadlockFree"
  apply (insert DF'_is_DeadlockFree)
  apply (simp add: DeadlockFree_def)
  apply (simp add: cspF_refF_semantics)
  apply (auto)
done





subsection \<open> traces DF(A) \<close>

lemma DFalphafun_eqT_DF' : 
  "((DFalphafun (DF' A))::('e DFalphaPN, 'e) proc) =T $DF' (A::('e set))"
by (cspT_unwind)

lemmas DF'_eqT_DFalphafun = DFalphafun_eqT_DF'[THEN cspT_sym]


lemma traces_DF'_eq_DFalphafun :
    "traces (($DF' A)::('e DFalphaPN, 'e) proc) MT = traces ((DFalphafun (DF' A))::('e DFalphaPN, 'e) proc) MT"
  apply (insert DF'_eqT_DFalphafun)
by (simp add: cspT_semantics)



subsection \<open> in traces DF(A) fixed point (FIX) \<close>

lemma in_traces_FIX_DFalphafun_DF'_lm:
    "(sett t \<subseteq> Ev ` A) \<longrightarrow> t :t traces ((FIX DFalphafun) ((DF' A)::'e DFalphaPN)) M"
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

lemma in_traces_FIX_DFalphafun_DF':
  "sett t \<subseteq> Ev ` A \<Longrightarrow> t :t traces ((FIX DFalphafun) (DF' A)) M"
by (simp add: in_traces_FIX_DFalphafun_DF'_lm)




subsection \<open> in traces DF(A) scenarios \<close>

lemma Tickt_notin_traces_DF' : "<Tick> ~:t traces (($DF' A)::('e DFalphaPN, 'e) proc) MT"
  apply (simp add: traces_DF'_eq_DFalphafun)
  apply (simp add: Int_pre_choice_def in_traces)
done

lemma not_noTick_notin_traces_DF' : "\<not> noTick s \<Longrightarrow> s ~:t traces (($DF' A)::('e DFalphaPN, 'e) proc) MT"
  apply (induct s rule: induct_trace)
  apply (simp)
  apply (simp add: Tickt_notin_traces_DF')
  apply (simp (no_asm) add: traces_DF'_eq_DFalphafun)
  apply (simp add: Int_pre_choice_def)
  apply (subst in_traces, simp)
  apply (subst in_traces, simp)
done


lemma one_appt_in_traces_DF' :
    "a : A \<Longrightarrow> <Ev a> ^^^ t :t traces (($DF' A)::('e DFalphaPN, 'e) proc) MT \<Longrightarrow> t :t traces ($DF' A) MT"
  apply (subst (asm) traces_DF'_eq_DFalphafun)
  apply (simp add: Int_pre_choice_def)
  apply (subst (asm) in_traces, simp)
  apply (subst (asm) in_traces, simp)
done


lemma one_appt_notin_traces_DF' :
    "a \<notin> A \<Longrightarrow> <Ev a> ^^^ t ~:t traces (($DF' A)::('e DFalphaPN, 'e) proc) MT"
  apply (simp add: traces_DF'_eq_DFalphafun)
  apply (simp add: Int_pre_choice_def)
  apply (simp add: in_traces)
done


lemma tail_closed_traces_DF' :
    "s ^^^ t :t traces (($DF' A)::('e DFalphaPN, 'e) proc) MT \<Longrightarrow> noTick s \<Longrightarrow> t :t traces ($DF' A) MT"
  apply (induct s arbitrary: t rule: induct_trace)
  apply (simp)
  apply (simp)
  apply (drule decompo_one_appt_noTick)
  apply (subst (asm) appt_assoc, simp, simp)
  apply (case_tac "a : A")
  apply (drule_tac t="s ^^^ t" in one_appt_in_traces_DF', simp, assumption)
  apply (subst (asm) one_appt_notin_traces_DF', simp, clarify)
done



subsection \<open> in traces DF(A) \<close>

lemma in_traces_DF':
    "sett t \<subseteq> Ev ` A \<Longrightarrow> t :t traces (($DF' A)) MT"
  apply (simp add: FIX_traces)
by (simp add: in_traces_FIX_DFalphafun_DF')


lemma in_traces_DF'_if_noTick :
    "noTick (s::'e trace) \<Longrightarrow> \<exists>A. s :t traces ($DF' (A::'e set)) MT"
  apply (frule sett_subset_Ev_image_if_noTick)
  apply (erule exE)
  apply (rule_tac x=A in exI)
  apply (simp add: in_traces_DF')
done



lemma in_traces_DF'_only_if :
    "s :t traces ($DF' (A::'e set)) MT \<Longrightarrow> sett s \<subseteq> Ev ` A"
  apply (induct s rule: induct_trace)
  apply (simp)
  apply (simp add: Tickt_notin_traces_DF')
  apply (simp)
  apply (subst (asm) traces_DF'_eq_DFalphafun)
  apply (simp add: Int_pre_choice_def)
  apply (subst (asm) in_traces, simp)
  apply (subst (asm) in_traces, simp)
done


lemma in_traces_DF'_only_if_noTick :
    "s :t traces (($DF' A)::('e DFalphaPN, 'e) proc) MT \<Longrightarrow> noTick s"
  apply (frule in_traces_DF'_only_if)
by (simp add: noTick_if_sett_subset_Ev_image)


lemma in_traces_DF'_iff :
    "s :t traces ($DF' (A::'e set)) MT = (sett s \<subseteq> Ev ` A)"
  apply (rule iffI)
  apply (simp add: in_traces_DF'_only_if)
  apply (simp add: in_traces_DF')
done




subsection \<open> failures DF(A) \<close>


lemma DFalphafun_eqF_DF' : 
  "DFalphafun (DF' A) =F $DF' A"
by (cspF_unwind)

lemmas DF'_eqF_DFalphafun = DFalphafun_eqF_DF'[THEN cspF_sym]
                  

lemma failures_DF'_eq_DFalphafun :
    "failures ($DF' A) MF = 
     failures (DFalphafun (DF' A)) MF"
  apply (insert DF'_eqF_DFalphafun[of A])
by (simp add: cspF_eqF_semantics)





subsection \<open> in failures DF(A) fixed point (FIX) \<close>

lemma in_failures_FIX_DFalphafun_DF'_lm:
    "(sett t \<subseteq> Ev ` A & (\<exists>a\<in>A. Ev a \<notin> X)) -->
     (t,X) :f failures ((FIX DFalphafun) (DF' A)) M"
  apply (induct_tac t rule: induct_trace)

  (* <> *)
    apply (intro impI conjI)
    apply (simp add: FIX_def in_failures)
    apply (rule_tac x="Suc 0" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def Int_pre_choice_def in_failures)

  (* <Tick> *)
    apply (simp add: noTick_def image_def)

  (* <Ev a> ^^^ s *)
  apply (case_tac "a : A")
    apply (simp)
    apply (intro impI)
    apply (elim conjE)
    apply (simp add: FIX_def in_failures)

    apply (elim exE)

    apply (rule_tac x="Suc n" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def Int_pre_choice_def in_failures)

    apply (intro impI)
    apply (elim conjE)
    apply (force)
done

lemma in_failures_FIX_DFalphafun_DF':
  "[| sett t \<subseteq> Ev ` A ; (\<exists>a\<in>A. Ev a \<notin> X) |] ==>
   (t,X) :f failures ((FIX DFalphafun) (DF' A)) M"
by (simp add: in_failures_FIX_DFalphafun_DF'_lm)



subsection \<open> in failures DF(A) \<close>

lemma in_failures_DF':
    "[| sett t \<subseteq> Ev ` A ; (\<exists>a\<in>A. Ev a \<notin> X) |] ==>
     (t,X) :f failures (($DF' A)::('e DFalphaPN, 'e) proc) MF"
  apply (simp add: FIX_failures)
by (simp add: in_failures_FIX_DFalphafun_DF'_lm)



subsection \<open> in failures DF(A) scenarios \<close>

lemma Tickt_notin_failures_DF' : "(<Tick>,X) ~:f failures (($DF' A)::('e DFalphaPN, 'e) proc) MF"
  apply (simp add: failures_DF'_eq_DFalphafun)
  apply (simp add: Int_pre_choice_def in_failures)
done


lemma one_appt_in_failures_DF' :
    "(<Ev a> ^^^ t,X) :f failures (($DF' A)::('e DFalphaPN, 'e) proc) MF \<Longrightarrow> (t,X) :f failures ($DF' A) MF"
  apply (subst (asm) failures_DF'_eq_DFalphafun)
  apply (simp add: Int_pre_choice_def)
  apply (subst (asm) in_failures)
  apply (subst (asm) in_failures, simp)
done

lemma tail_closed_failures_DF' :
    "(s ^^^ t,X) :f failures (($DF' A)::('e DFalphaPN, 'e) proc) MF \<Longrightarrow> noTick s \<Longrightarrow>
     (t,X) :f failures ($DF' A) MF"
  apply (induct s rule: induct_trace)
  apply (simp_all)

  apply (simp add: appt_assoc)
by (simp add: one_appt_in_failures_DF')


lemma in_failures_DF'_only_if_EX_nonTick_refusal :
    "(s, X) :f failures (($DF' A)::('e DFalphaPN, 'e) proc) MF \<Longrightarrow> \<exists> a. Ev a \<notin> X"
  apply (induct s rule: induct_trace)
  
  apply (simp add: failures_DF'_eq_DFalphafun)
  apply (simp add: Int_pre_choice_def in_failures)
  apply (force)
  
  apply (simp add: failures_DF'_eq_DFalphafun)
  apply (simp add: Int_pre_choice_def in_failures)
  
  apply (simp add: failures_DF'_eq_DFalphafun)
  apply (simp add: Int_pre_choice_def)
  apply (subst (asm) in_failures)
  apply (subst (asm) in_failures, simp)
  apply (simp add: failures_DF'_eq_DFalphafun)
  apply (simp add: Int_pre_choice_def)
done


lemma Evset_refusals_notin_failures_DF' :
    "(s, Evset) ~:f failures (($DF' A)::('e DFalphaPN, 'e) proc) MF"
  apply (induct_tac s rule: induct_trace)
  
  apply (simp add: failures_DF'_eq_DFalphafun)
  apply (simp add: Int_pre_choice_def in_failures)
  apply (simp add: Evset_def)
  
  apply (simp add: failures_DF'_eq_DFalphafun)
  apply (simp add: Int_pre_choice_def in_failures)
  
  apply (simp add: failures_DF'_eq_DFalphafun)
  apply (simp add: Int_pre_choice_def)
  apply (subst in_failures, simp)
  apply (subst in_failures, simp)
  apply (simp add: failures_DF'_eq_DFalphafun)
  apply (simp add: Int_pre_choice_def)
done


lemma UNIV_refusals_notin_failures_DF' :
    "(s, UNIV) ~:f failures (($DF' A)::('e DFalphaPN, 'e) proc) MF"
  apply (induct_tac s rule: induct_trace)
  
  apply (simp add: failures_DF'_eq_DFalphafun)
  apply (simp add: Int_pre_choice_def in_failures)
  
  apply (simp add: failures_DF'_eq_DFalphafun)
  apply (simp add: Int_pre_choice_def in_failures)
  
  apply (simp add: failures_DF'_eq_DFalphafun)
  apply (simp add: Int_pre_choice_def)
  apply (subst in_failures, simp)
  apply (subst in_failures, simp)
  apply (simp add: failures_DF'_eq_DFalphafun)
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
    "(s, X) :f failures (($DF' A):: ('e DFalphaPN, 'e) proc) MF \<Longrightarrow> noTick s"
  apply (frule_tac P="$DF' A" in proc_T2)
by (simp add: fstF_MF_MT in_traces_DF'_only_if_noTick)







subsection \<open> is non-terminating deadlock-free \<close>

lemma DF'_is_NonTickDeadlockFree:
    "(($DF' A) :: ('e DFalphaPN, 'e) proc) isNonTickDeadlockFree"
  apply (simp add: NonTickDeadlockFree_def)
  apply (rule allI)
  apply (simp add: Evset_refusals_notin_failures_DF')
done



subsection \<open> semantical approach --> syntactical approach \<close>


lemma DF'_NonTickDeadlockFree:
    "(($DF' A):: ('e DFalphaPN, 'e) proc) <=F P ==> (P::('p, 'e) proc) isNonTickDeadlockFree"
  apply (insert DF'_is_NonTickDeadlockFree)
  apply (simp add: NonTickDeadlockFree_def insert_UNIV)
  apply (simp add: cspF_refF_semantics)
  apply (auto)
done



lemma NonTickDeadlockFree_DF':
    "P isNonTickDeadlockFree ==> \<exists>A. ($DF' (A::'e set)) <=F (P::('p, 'e) proc)"
  apply (rule_tac x=UNIV in exI)

  apply (simp add: NonTickDeadlockFree_def)
  apply (simp add: cspF_refF_semantics)
  apply (rule conjI)

  (* trace *)
  apply (simp add: subdomT_iff)
  apply (intro allI impI)
  apply (simp add: fstF_MF_MT)
  apply (rule in_traces_DF')
  apply (simp only: Ev_UNIV_eq_Evset)
  apply (simp only: sett_subset_Evset_iff_noTick)
  apply (simp add: noTick_if_Evset_notin_failures)
  
  (* failures *)
  apply (simp add: subsetF_iff)
  apply (intro allI impI)

  apply (rule in_failures_DF')
  apply (simp only: Ev_UNIV_eq_Evset)
  apply (simp only: sett_subset_Evset_iff_noTick)
  apply (simp add: noTick_if_Evset_notin_failures)

  (* \<exists>a. Ev a \<notin> X *)
  apply (drule_tac x=s in spec)
    apply (erule contrapos_np, simp)
    apply (rule memF_F2, simp)
    apply (simp add: all_Ev_in_Evset_iff)
done




subsection \<open> syntactical approach <--> semantical approach \<close>

theorem NonTickDeadlockFree_DF_ref:
    "P isNonTickDeadlockFree = (\<exists>A::'e set. (($DF' A)::('e DFalphaPN, 'e)proc) <=F P)"
  apply (rule)
  apply (frule NonTickDeadlockFree_DF', elim exE, force)
  apply (elim exE, simp add: DF'_NonTickDeadlockFree)
done


end