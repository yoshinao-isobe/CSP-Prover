theory CSP_T_law_CHAOS
imports CSP.CSP_CHAOS
        CSP_T_law_fix
        CSP_T_law_fp
        CSP_T_law_step
        CSP_T_law_ref
begin


section \<open> Chaos (Hoare 78) and (Isobe) \<close>


subsection \<open> Chaos semantics \<close>


lemmas Chaos_domT = Rep_int_choice_domT Act_prefix_domT


lemma cspT_Chaos :
    "(($Chaos A)::('e ChaosName,'e) proc) =T (((Chaosfun (Chaos A)))::('e ChaosName, 'e) proc)"
by (rule cspT_unwind, simp_all)


lemma traces_Chaos :
    "traces ($Chaos A) MT = traces (Chaosfun (Chaos A)) MT"
  apply (insert cspT_Chaos)
by (simp add: cspT_eqT_semantics)


subsubsection \<open> traces included in Chaos \<close>



subsection \<open> NOT in traces Chaos S \<close>

lemma Tickt_notin_traces_included_in_Chaos :
    "<Tick> ~:t traces (($Chaos A)::('e ChaosName,'e) proc) MT"
  apply (simp add: traces_Chaos Int_pre_choice_def)
by (simp add: in_traces)

lemma Tickt_notin_traces_included_in_FIX_Chaos :
    "<Tick> ~:t traces ((FIX Chaosfun) (Chaos A)::('e ChaosName,'e) proc) MT"
  apply (simp add: FIX_def in_traces)
  apply (intro allI)
  apply (induct_tac n)
  apply (simp add: FIXn_def Subst_procfun_prod_def in_traces)
  apply (simp add: FIXn_def Subst_procfun_prod_def in_traces)
  apply (simp add: traces_Chaos Int_pre_choice_def)
by (simp add: in_traces)



subsection \<open> in traces Chaos S \<close>


lemma traces_included_in_Chaos_lm :
    "sett t \<subseteq> Ev ` A -->
     t :t traces ((FIX Chaosfun) ((Chaos A)::'e ChaosName)) M"
  apply (induct_tac t rule: induct_trace)

  (* <> *)
    apply (intro impI conjI)
    apply (simp add: FIX_def in_traces)

  (* <Tick> *)
    apply (simp add: image_def)

  (* <Ev a> ^^^ s *)
    apply (simp)
    apply (intro impI)
    apply (simp)
    apply (elim conjE)
    apply (simp add: FIX_def in_traces)

    apply (elim disjE exE)

    apply (rule_tac x="Suc 0" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_traces)
    apply (simp add: image_def Int_pre_choice_def in_traces)

    apply (rule_tac x="Suc n" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_traces)
    apply (simp add: image_def Int_pre_choice_def in_traces)
done

lemma traces_included_in_Chaos :
    "[| sett t \<subseteq> Ev ` S |] ==>
     t :t traces ((FIX Chaosfun) (Chaos S)) M"
by (simp add: traces_included_in_Chaos_lm)




subsection \<open> $Chaos and DIV \<close>


lemmas cspT_DIV_ref_Chaos = cspT_DIV_top


lemma cspT_Chaos_ref_DIV : "DIV <=T (($Chaos {})::('a ChaosName,'a) proc)"
  apply (simp add: cspT_semantics)
  apply (simp add: traces_Chaos Int_pre_choice_def)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (simp add: CollectT_open_memT Chaos_domT)
  apply (simp add: UnionT_def Rep_domT_inverse)
done


subsection \<open> $Chaos and STOP \<close>


lemma cspT_Chaos_ref_STOP : "(($Chaos S)::('a ChaosName,'a) proc) <=T STOP"
by (rule cspT_top)




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


lemmas ChaosTick_domT = Chaos_domT SKIP_domT


lemma cspT_ChaosTick :
    "(($ChaosTick A)::('e ChaosName,'e) proc) =T (((Chaosfun (ChaosTick A)))::('e ChaosName, 'e) proc)"
by (rule cspT_unwind, simp_all)


lemma traces_ChaosTick :
    "traces ($ChaosTick A) MT = traces (Chaosfun (ChaosTick A)) MT"
  apply (insert cspT_ChaosTick)
by (simp add: cspT_eqT_semantics)


subsubsection \<open> traces included in ChaosTick \<close>



subsection \<open> in traces ChaosTick S \<close>


lemma Tickt_in_traces_included_in_ChaosTick :
    "<Tick> :t traces ((FIX Chaosfun) (ChaosTick S)) M"
  apply (simp add: FIX_def in_traces)
  apply (rule_tac x="Suc 0" in exI)
  apply (simp add: FIXn_def Subst_procfun_prod_def in_traces)
done


lemma traces_included_in_ChaosTick_lm :
    "sett t \<subseteq> Ev ` S \<union> {Tick} -->
     t :t traces ((FIX Chaosfun) (ChaosTick S)) M"
  apply (induct_tac t rule: induct_trace)

  (* <> *)
    apply (intro impI conjI)
    apply (simp add: FIX_def in_traces)

  (* <Tick> *)
    apply (simp)
    apply (simp add: FIX_def in_traces)
    apply (rule_tac x="Suc 0" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_traces)

  (* <Ev a> ^^^ s *)
    apply (simp)
    apply (intro impI)
    apply (simp)
    apply (elim conjE)
    apply (simp add: FIX_def in_traces)

    apply (elim disjE exE)

    apply (rule_tac x="Suc 0" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_traces)
    apply (simp add: image_def Int_pre_choice_def in_traces)

    apply (rule_tac x="Suc n" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_traces)
    apply (simp add: image_def Int_pre_choice_def in_traces)
done

lemma traces_included_in_ChaosTick :
    "[| sett t \<subseteq> Ev ` S \<union> {Tick} |] ==>
     t :t traces ((FIX Chaosfun) (ChaosTick S)) M"
by (simp add: traces_included_in_ChaosTick_lm)






subsection \<open> $Chaos {} =T DIV \<close>


lemma cspT_Chaos_eqT_DIV : "(($Chaos {})::('a ChaosName,'a) proc) =T DIV"
  apply (rule cspT_rw_left)
  apply (rule cspT_unwind, simp, simp)
  apply (simp add: cspT_semantics Int_pre_choice_def)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (simp add: UnionT_def)
  apply (subst Abs_domT_inject)
  apply (auto simp add: Abs_domT_inverse)
  apply (simp add: traces_iff)
  apply (auto simp add: Abs_domT_inverse)
  apply (simp add: traces_iff)
  apply (auto simp add: Abs_domT_inverse)
done


lemma cspT_CHAOS_eqF_DIV : "CHAOS {} =T DIV"
by (simp add: CHAOS_def, rule cspT_Chaos_eqT_DIV)




subsection \<open> $Chaos {} =T STOP \<close>


lemma cspT_Chaos_eqT_STOP : "(($Chaos {})::('a ChaosName,'a) proc) =T STOP"
  apply (rule cspT_rw_left)
  apply (rule cspT_unwind, simp, simp)
  apply (simp add: cspT_semantics Int_pre_choice_def)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (simp add: UnionT_def)
  apply (subst Abs_domT_inject)
  apply (auto simp add: Abs_domT_inverse)
  apply (simp add: traces_iff)
  apply (auto simp add: Abs_domT_inverse)
  apply (simp add: traces_iff)
  apply (auto simp add: Abs_domT_inverse)
done


lemma cspT_CHAOS_eqF_STOP : "CHAOS {} =T STOP"
by (simp add: CHAOS_def, rule cspT_Chaos_eqT_STOP)



subsection \<open> $ChaosTick S <=T DIV \<close>


lemmas cspT_DIV_ref_ChaosTick = cspT_DIV_top


lemma set_nilt_one_t_nilt_simps [simp]: "{<>, <a>,<>} = {<>, <a>}"
by (fast)

lemma cspT_ChaosTick_not_ref_DIV : "~ DIV <=T (($ChaosTick {})::('a ChaosName,'a) proc)"
  apply (simp add: cspT_semantics)
  apply (simp add: traces_ChaosTick Int_pre_choice_def)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (simp add: CollectT_open_memT Chaos_domT)
  apply (simp add: UnionT_def Abs_domT_inverse)
  apply (simp add: subdomT_def Abs_domT_inverse)
done




subsection \<open> $ChaosTick S <=T STOP \<close>


lemmas cspT_STOP_ref_ChaosTick = cspT_STOP_top

lemma cspT_ChaosTick_not_ref_STOP : "~ STOP <=T (($ChaosTick {})::('a ChaosName,'a) proc)"
  apply (simp add: cspT_semantics)
  apply (simp add: traces_ChaosTick Int_pre_choice_def)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (subst traces_iff)
  apply (simp add: CollectT_open_memT Chaos_domT)
  apply (simp add: UnionT_def Abs_domT_inverse)
  apply (simp add: subdomT_def Abs_domT_inverse)
done




subsection \<open> $ChaosTick S <=T SKIP \<close>


lemma cspT_SKIP_ref_ChaosTick : "(($ChaosTick S)::('a ChaosName,'a) proc) <=T SKIP"
  apply (rule cspT_rw_left)
  apply (rule cspT_FIX[of Chaosfun], simp_all)
  apply (simp add: cspT_semantics)

  apply (simp add: subdomT_iff in_traces)
  apply (simp add: Tickt_in_traces_included_in_ChaosTick)
done






section \<open> ChaosR (Chaos from Roscoe book) \<close>


subsection \<open> ChaosR semantics \<close>


lemmas ChaosR_domT = Ext_pre_choice_domT Act_prefix_domT


lemma cspT_ChaosR :
    "(($ChaosR A)::('e ChaosName,'e) proc) =T (((Chaosfun (ChaosR A)))::('e ChaosName, 'e) proc)"
by (rule cspT_unwind, simp_all)


lemma traces_ChaosR :
    "traces ($ChaosR A) MT = traces (Chaosfun (ChaosR A)) MT"
  apply (insert cspT_ChaosR)
by (simp add: cspT_eqT_semantics)





subsection \<open> ChaosR relation to Chaos (Hoare) \<close>



lemma cspT_ChaosR_refT_Chaos :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
     (($ChaosR A)::('e ChaosName,'e) proc) <=T (($Chaos A)::('e ChaosName,'e) proc)"
  apply (rule cspT_fp_induct_right[of _ _ "\<lambda>p. case p of Chaos A \<Rightarrow> $ChaosR A | _ \<Rightarrow> $p"])
  apply (simp_all, simp)
  apply (induct_tac p, simp)
  apply (rule cspT_rw_left, rule cspT_unwind, simp_all, simp, simp)
    apply (simp add: Int_pre_choice_def)
    apply (simp add: cspT_semantics)
    apply (rule)
    apply (simp add: in_traces)
    apply (elim disjE bexE)
    apply (rule disjI1, simp)
    apply (rule disjI1, simp)
    apply (rule disjI2)
    apply (rule disjI1)
    apply (elim exE conjE)
    apply (force)
    apply (rule disjI1, simp)
  apply (rule cspT_rw_left, rule cspT_unwind, simp_all, simp, simp)
  apply (rule cspT_rw_left, rule cspT_unwind, simp_all, simp, simp)
  apply (rule cspT_rw_left, rule cspT_unwind, simp_all, simp, simp)
done


lemma cspT_Chaos_refT_ChaosR :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
     (($Chaos A)::('e ChaosName,'e) proc) <=T (($ChaosR A)::('e ChaosName,'e) proc)"
  apply (rule cspT_fp_induct_right[of _ _ "\<lambda>p. case p of ChaosR A \<Rightarrow> $Chaos A | _ \<Rightarrow> $p"])
  apply (simp_all, simp)
  apply (induct_tac p, simp)
  apply (rule cspT_rw_left, rule cspT_unwind, simp_all, simp, simp)
  apply (rule cspT_rw_left, rule cspT_unwind, simp_all, simp, simp)
  apply (rule cspT_rw_left, rule cspT_unwind, simp_all, simp, simp)
    apply (simp add: Int_pre_choice_def)
    apply (simp add: cspT_semantics)
    apply (rule)
    apply (simp add: in_traces)
    apply (elim disjE bexE)
    apply (rule disjI1, simp)
    apply (rule disjI2)
    apply (rule disjI1)
    apply (elim exE conjE)
    apply (force)
    apply (rule disjI1, simp)
  apply (rule cspT_rw_left, rule cspT_unwind, simp_all, simp, simp)
done



lemma cspT_ChaosR_eqT_Chaos :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
     (($ChaosR A)::('e ChaosName,'e) proc) =T (($Chaos A)::('e ChaosName,'e) proc)"
  apply (rule cspT_ref_eq)
  apply (rule cspT_ChaosR_refT_Chaos, simp_all)
  apply (rule cspT_Chaos_refT_ChaosR, simp_all)
done

lemmas cspT_Chaos_eqT_ChaosR = cspT_ChaosR_eqT_Chaos[THEN cspT_sym]



(*
lemma cspT_ChaosR_refT_Chaos_empty :
    "(($ChaosR {})::('e ChaosName,'e) proc) <=T (($Chaos {})::('e ChaosName,'e) proc)"
  apply (rule cspT_rw_left, rule cspT_unwind, simp_all, simp, simp)
  apply (rule cspT_trans)
  apply (rule cspT_DIV_top)
  apply (rule cspT_Chaos_ref_DIV)
done


lemma cspT_Chaos_refT_ChaosR_empty :
    "(($Chaos {})::('e ChaosName,'e) proc) <=T (($ChaosR {})::('e ChaosName,'e) proc)"
  apply (rule cspT_rw_left, rule cspT_unwind, simp_all, simp, simp)
  apply (rule cspT_rw_right, rule cspT_unwind, simp_all, simp, simp)
  apply (rule cspT_decompo, simp_all)
  apply (simp add: Int_pre_choice_def)

  apply (simp add: cspT_semantics)
  apply (rule, simp add: in_traces)
done


lemma cspT_ChaosR_eqT_Chaos_empty :
    "(($ChaosR {})::('e ChaosName,'e) proc) =T (($Chaos {})::('e ChaosName,'e) proc)"
  apply (rule cspT_ref_eq)
  apply (rule cspT_ChaosR_refT_Chaos_empty)
  apply (rule cspT_Chaos_refT_ChaosR_empty)
done

lemmas cspT_Chaos_eqT_ChaosR_empty = cspT_ChaosR_eqT_Chaos_empty[THEN cspT_sym]
*)


end