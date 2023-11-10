theory CSP_F_law_CHAOS
imports CSP_T.CSP_T_law_CHAOS
        CSP_F_MF_MT
        CSP_F_law_fix
        CSP_F_law_fp
        CSP_F_law_step
        CSP_F_law_ref
begin


section \<open> Chaos (Hoare 78) \<close>


subsection \<open> Chaos semantics \<close>


lemmas Chaos_setF = Rep_int_choice_setF Act_prefix_setF STOP_setF


lemma cspF_Chaos :
    "(($Chaos A)::('e ChaosName,'e) proc) =F (((Chaosfun (Chaos A)))::('e ChaosName, 'e) proc)"
by (rule cspF_unwind, simp_all)


lemma failures_Chaos :
    "failures ($Chaos A) MF = failures (Chaosfun (Chaos A)) MF"
  apply (insert cspF_Chaos[of A])
by (simp add: cspF_semantics)



subsubsection \<open> failures included in Chaos \<close>



subsection \<open> NOT in failures Chaos S \<close>

lemma Tickt_notin_failures_included_in_Chaos :
    "(<Tick>,X) ~:f failures (($Chaos A)::('e ChaosName,'e) proc) MF"
  apply (rule notI)
  apply (drule proc_T2)
  apply (simp add: fstF_MF_MT)
by (simp add: Tickt_notin_traces_included_in_Chaos)

lemma Tickt_notin_failures_included_in_FIX_Chaos :
    "(<Tick>,X) ~:f failures ((FIX Chaosfun) (Chaos A)::('e ChaosName,'e) proc) MF"
  apply (rule notI)
  apply (drule proc_T2)
  apply (simp add: fstF_MF_MT)
by (simp add: Tickt_notin_traces_included_in_FIX_Chaos)



subsection \<open> in failures Chaos S \<close>


lemma failures_included_in_Chaos_lm :
    "sett t \<subseteq> Ev ` A & X \<subseteq> Evset - Ev ` A -->
     (t,X) :f failures ((FIX Chaosfun) ((Chaos A)::'e ChaosName)) M"
  apply (induct_tac t rule: induct_trace)

  (* <> *)
    apply (intro impI conjI)
    apply (simp add: FIX_def in_failures)

    apply (rule_tac x="Suc 0" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)

  (* <Tick> *)
    apply (simp add: image_def)

  (* <Ev a> ^^^ s *)
    apply (simp)
    apply (intro impI)
    apply (simp)
    apply (elim conjE)
    apply (simp add: FIX_def in_failures)

    apply (elim disjE exE)

    apply (rule_tac x="Suc n" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)
    apply (simp add: image_def Int_pre_choice_def in_failures)
done

lemma failures_included_in_Chaos :
    "[| sett t \<subseteq> Ev ` A ; X \<subseteq> Evset - Ev ` A |] ==>
     (t,X) :f failures ((FIX Chaosfun) (Chaos A)) M"
by (simp add: failures_included_in_Chaos_lm)






subsection \<open> NOT $Chaos {} =F DIV \<close>

lemma nonempty_failures_STOP [simp]: "{f. \<exists>X. f = (<>, X)} \<noteq> {}"
by (auto)

lemma not_cspF_Chaos_eqF_DIV : "~ (($Chaos {})::('a ChaosName,'a) proc) =F (DIV::('pn,'a) proc)"
  apply (rule notI)
  apply (simp add: cspF_cspT_semantics Int_pre_choice_def)
  apply (erule conjE)
  (*apply (simp add: fstF_MF_MT)
  apply (erule cspT_rw_left_eqE[of _ MT])
  apply (rule cspT_Chaos_eqT_DIV)
  apply (simp)*)
  apply (simp add: failures_Chaos Int_pre_choice_def)
  apply (subst (asm) failures_iff)
  apply (subst (asm) failures_iff)
  apply (subst (asm) failures_iff)
  apply (subst (asm) failures_iff)
  apply (simp add: UnionF_def)
  apply (auto simp add: Abs_setF_inverse)
  apply (auto simp add: Rep_setF_inverse)
  apply (simp add: Abs_setF_inject Chaos_setF empF_def)
done


lemma not_cspF_CHAOS_eqF_DIV : "~ CHAOS {} =F DIV"
by (simp add: CHAOS_def, rule not_cspF_Chaos_eqF_DIV)



subsection \<open> $Chaos <=F DIV \<close>


lemmas cspF_DIV_ref_Chaos = cspF_DIV_top

                                          
lemma cspF_Chaos_ref_DIV : "~ DIV <=F (($Chaos {})::('a ChaosName,'a) proc)"
  apply (rule notI)

  apply (simp add: cspF_cspT_semantics)
  apply (erule conjE)

  (*apply (simp add: fstF_MF_MT)
  apply (erule cspT_rw_rightE)
  apply (rule cspT_Chaos_eqT_DIV, simp)*)

  apply (simp add: failures_Chaos Int_pre_choice_def)
  apply (subst (asm) failures_iff)
  apply (subst (asm) failures_iff)
  apply (subst (asm) failures_iff)
  apply (subst (asm) failures_iff)
  apply (subst (asm) failures_iff)
  apply (simp add: UnionF_def)
  apply (simp add: Abs_setF_inverse)
  apply (simp add: Rep_setF_inverse)
  apply (erule subsetFE)
  apply (simp add: memF_def Abs_setF_inverse STOP_setF empF_def)
done


subsection \<open> $Chaos and STOP \<close>


lemma cspF_Chaos_ref_STOP : "(($Chaos S)::('a ChaosName,'a) proc) <=F STOP"
  apply (rule cspF_rw_left, rule cspF_unwind, simp_all, simp, simp)
  apply (rule cspF_Int_choice_left2)
by (simp)




subsection \<open> ~ $Chaos S <=T SKIP \<close>


lemma cspT_Chaos_not_ref_SKIP : "~ (($Chaos S)::('a ChaosName,'a) proc) <=T SKIP"
  apply (rule notI)
  apply (erule cspT_rw_leftE)
  apply (rule cspT_FIX[of Chaosfun], simp_all)
  apply (simp add: cspT_semantics)

  apply (simp add: subdomT_iff in_traces)
  apply (simp add: Tickt_notin_traces_included_in_FIX_Chaos)
done



section \<open> ChaosTick \<close>


lemmas SKIP_domT = one_t_set_in[of Tick]


subsection \<open> ChaosTick semantics \<close>


lemmas ChaosTick_setF = Chaos_setF SKIP_setF


lemma cspF_ChaosTick :
    "(($ChaosTick A)::('e ChaosName,'e) proc) =F (((Chaosfun (ChaosTick A)))::('e ChaosName, 'e) proc)"
by (rule cspF_unwind, simp_all)


lemma failures_ChaosTick :
    "failures ($ChaosTick A) MF = failures (Chaosfun (ChaosTick A)) MF"
  apply (insert cspF_ChaosTick[of A])
by (simp add: cspF_eqF_semantics)



subsection \<open> in failures ChaosTick S \<close>


lemma Tickt_in_failures_included_in_ChaosTick : "(<Tick>, X) :f failures ((FIX Chaosfun) (ChaosTick A)) M"
    apply (insert Tickt_in_traces_included_in_ChaosTick[of A "fstF \<circ> M"])
    apply (insert proc_domF[of "(FIX Chaosfun) (ChaosTick A)" M])
    apply (frule_tac s="<>" in domF_T3, simp_all)
done


lemma failures_included_in_ChaosTick_lm :
    "sett t \<subseteq> Ev ` S \<union> {Tick} & Ev ` S \<inter> X = {} -->
     (t,X) :f failures ((FIX Chaosfun) (ChaosTick S)) M"
  apply (induct_tac t rule: induct_trace)

  (* <> *)
    apply (intro impI conjI)
    apply (simp add: FIX_def in_failures)
    apply (rule_tac x="Suc 0" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)

  (* <Tick> *)
    apply (simp)
    apply (simp add: Tickt_in_failures_included_in_ChaosTick)

  (* <Ev a> ^^^ s *)
    apply (simp)
    apply (intro impI)
    apply (simp)
    apply (elim conjE)

    apply (simp add: FIX_def in_failures)
    apply (elim exE)
    apply (rule_tac x="Suc n" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def Int_pre_choice_def in_failures)
    apply (simp add: image_def)
done

lemma failures_included_in_ChaosTick :
  "[| sett t \<subseteq> Ev ` S \<union> {Tick} ; Ev ` S \<inter> X = {} |] ==>
   (t,X) :f failures ((FIX Chaosfun) (ChaosTick S)) M"
by (simp add: failures_included_in_ChaosTick_lm)





subsection \<open> NOT $ChaosTick {} =F DIV \<close>

lemma not_cspF_ChaosTick_eqF_DIV : "~ (($ChaosTick {})::('a ChaosName,'a) proc) =F DIV"
  apply (rule notI)
  apply (erule cspF_rw_leftE)
  apply (rule cspF_unwind, simp, simp)
  apply (simp add: cspF_semantics Int_pre_choice_def)
  apply (subst (asm) traces_iff)
  apply (subst (asm) traces_iff)
  apply (subst (asm) traces_iff)
  apply (simp add: UnionT_def)
  apply (subst (asm) Abs_domT_inject)
  apply (auto simp add: Abs_domT_inverse)
  apply (simp add: traces_iff)
  apply (auto simp add: UnionT_def)
  apply (auto simp add: Abs_domT_inverse)
done


lemma not_cspF_CHAOSTick_eqF_DIV : "~ CHAOSTick {} =F DIV"
by (simp add: CHAOSTick_def, rule not_cspF_ChaosTick_eqF_DIV)




subsection \<open> $ChaosTick {} =F STOP |~| SKIP \<close>


lemma cspF_ChaosTick_eqF_STOP_SKIP : "(($ChaosTick {})::('a ChaosName,'a) proc) =F STOP  |~| SKIP"
  apply (rule cspF_rw_left, rule cspF_unwind)
  apply (simp, simp)
  apply (simp add: cspF_semantics Int_pre_choice_def)
  apply (simp add: traces_iff UnionT_def Abs_domT_inverse)
  apply (simp add: failures_iff UnionF_def Abs_setF_inverse)
done



subsection \<open> CHAOSTick {} =F STOP |~| SKIP \<close>


lemma cspF_CHAOSTick_STOP_SKIP : "CHAOSTick {} =F STOP |~| SKIP"
by (simp add: CHAOSTick_def, rule cspF_ChaosTick_eqF_STOP_SKIP)




subsection \<open> $ChaosTick S <=F DIV \<close>


lemmas cspF_DIV_ref_ChaosTick = cspF_DIV_top

lemma not_cspF_ChaosTick_ref_DIV : "~ DIV <=F (($ChaosTick {})::('a ChaosName,'a) proc)"
  apply (rule notI)

  apply (simp add: cspF_cspT_semantics)
  apply (erule conjE)

  (*apply (simp add: fstF_MF_MT)
  apply (erule cspT_rw_rightE)
  apply (rule cspT_Chaos_eqT_DIV, simp)*)

  apply (simp add: failures_ChaosTick Int_pre_choice_def)
  apply (subst (asm) failures_iff)
  apply (subst (asm) failures_iff)
  apply (subst (asm) failures_iff)
  apply (subst (asm) failures_iff)
  apply (subst (asm) failures_iff)
  apply (subst (asm) failures_iff)
  apply (subst (asm) failures_iff)
  apply (simp add: UnionF_def)
  apply (simp add: subsetF_iff)
  apply (simp add: memF_def Abs_setF_inverse ChaosTick_setF empF_def)
  apply (simp only: not_ex[THEN sym])
  apply (erule contrapos_np, simp)
  apply (rule_tac x="<>" in exI)
  apply (rule_tac x="Evset" in exI)
  apply (subst Abs_setF_inverse)
  apply (simp add: setF_def HC_F2_def)
  apply (intro allI impI, elim conjE disjE)
  apply (rule disjI1, simp)
  apply (rule disjI2, rule disjI1, simp)
  apply (rule disjI2, rule disjI2, simp)
  apply (simp add: Abs_setF_inverse ChaosTick_setF)
done



subsection \<open> $ChaosTick S <=F STOP |~| SKIP \<close>


lemma cspF_STOP_SKIP_ref_ChaosTick : "(($ChaosTick S)::('a ChaosName,'a) proc) <=F STOP |~| SKIP"
  apply (rule cspF_rw_left)
  apply (rule cspF_FIX[of Chaosfun], simp_all)
  apply (simp add: cspF_semantics)

  apply (simp add: subdomT_iff in_traces)

  apply (simp add: subsetF_iff in_failures)

  apply (simp add: Tickt_in_traces_included_in_ChaosTick)
  apply (simp add: Tickt_in_failures_included_in_ChaosTick)
  apply (intro allI conjI impI)

    apply (simp add: FIX_def in_failures)
    apply (rule_tac x="Suc 0" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)

    apply (simp add: FIX_def in_failures)
    apply (rule_tac x="Suc 0" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)
done



subsection \<open> $ChaosTick S <=F STOP \<close>


lemma cspF_STOP_ref_ChaosTick :
    "(($ChaosTick S)::('a ChaosName,'a) proc) <=F STOP"
  apply (rule cspF_trans)
  apply (rule cspF_STOP_SKIP_ref_ChaosTick)
  apply (rule cspF_Int_choice_left1)
  apply (simp)
done



subsection \<open> $ChaosTick S <=F SKIP \<close>


lemma cspF_SKIP_ref_ChaosTick :
    "(($ChaosTick S)::('a ChaosName,'a) proc) <=F SKIP"
  apply (rule cspF_trans)
  apply (rule cspF_STOP_SKIP_ref_ChaosTick)
  apply (rule cspF_Int_choice_left2)
  apply (simp)
done




section \<open> ChaosR (Chaos from Roscoe book) \<close>


subsection \<open> ChaosR semantics \<close>


lemmas ChaosR_setF = Ext_pre_choice_setF Act_prefix_setF


lemma cspF_ChaosR :
    "(($ChaosR A)::('e ChaosName,'e) proc) =F (((Chaosfun (ChaosR A)))::('e ChaosName, 'e) proc)"
by (rule cspF_unwind, simp_all)


lemma failures_ChaosR :
    "failures ($ChaosR A) MF = failures (Chaosfun (ChaosR A)) MF"
  apply (insert cspF_ChaosR[of A])
by (simp add: cspF_eqF_semantics)





subsection \<open> ChaosR relation to Chaos (Hoare) \<close>



lemma cspF_ChaosR_refF_Chaos :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
     (($ChaosR A)::('e ChaosName,'e) proc) <=F (($Chaos A)::('e ChaosName,'e) proc)"
  apply (rule cspF_fp_induct_right[of _ _ "\<lambda>p. case p of Chaos A \<Rightarrow> $ChaosR A | _ \<Rightarrow> $p"])
  apply (simp_all, simp)
  apply (induct_tac p, simp)
  apply (rule cspF_rw_left, rule cspF_unwind, simp_all, simp, simp)
    apply (simp add: Int_pre_choice_def)
    apply (simp add: cspF_semantics fstF_MF_MT)
    apply (rule, rule)
    apply (simp add: in_traces)
    apply (elim disjE bexE)
    apply (rule disjI1, simp)
    apply (rule disjI1, simp)
    apply (rule disjI2)
    apply (rule disjI1)
    apply (elim exE conjE)
    apply (force)
    apply (rule disjI1, simp)

    apply (rule)
    apply (simp add: in_failures)
    apply (elim disjE bexE conjE)
    apply (rule disjI2)
    apply (rule disjI2, simp add: image_def)
    apply (force)
    apply (rule disjI2)
    apply (rule disjI2, simp add: image_def)
  apply (rule cspF_rw_left, rule cspF_unwind, simp_all, simp, simp)
  apply (rule cspF_rw_left, rule cspF_unwind, simp_all, simp, simp)
  apply (rule cspF_rw_left, rule cspF_unwind, simp_all, simp, simp)
done


lemma cspF_Chaos_refF_ChaosR :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
     (($Chaos A)::('e ChaosName,'e) proc) <=F (($ChaosR A)::('e ChaosName,'e) proc)"
  apply (rule cspF_fp_induct_right[of _ _ "\<lambda>p. case p of ChaosR A \<Rightarrow> $Chaos A | _ \<Rightarrow> $p"])
  apply (simp_all, simp)
  apply (induct_tac p, simp)
  apply (rule cspF_rw_left, rule cspF_unwind, simp_all, simp, simp)
  apply (rule cspF_rw_left, rule cspF_unwind, simp_all, simp, simp)
  apply (rule cspF_rw_left, rule cspF_unwind, simp_all, simp, simp)
    apply (simp add: Int_pre_choice_def)
    apply (simp add: cspF_semantics)
    apply (rule, rule)
    apply (simp add: in_traces)
    apply (elim disjE bexE)
    apply (rule disjI1, simp)
    apply (rule disjI2)
    apply (rule disjI1)
    apply (elim exE conjE)
    apply (force)
    apply (rule disjI1, simp)
    apply (rule)
    apply (simp add: in_failures)
    apply (elim disjE exE conjE)
    apply (rule disjI2, simp)
    apply (rule disjI1)
    apply (force)
    apply (rule disjI2, simp)
  apply (rule cspF_rw_left, rule cspF_unwind, simp_all, simp, simp)
done



lemma cspF_ChaosR_eqF_Chaos :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
     (($ChaosR A)::('e ChaosName,'e) proc) =F (($Chaos A)::('e ChaosName,'e) proc)"
  apply (rule cspF_ref_eq)
  apply (rule cspF_ChaosR_refF_Chaos, simp_all)
  apply (rule cspF_Chaos_refF_ChaosR, simp_all)
done

lemmas cspF_Chaos_eqF_ChaosR = cspF_ChaosR_eqF_Chaos[THEN cspF_sym]



end