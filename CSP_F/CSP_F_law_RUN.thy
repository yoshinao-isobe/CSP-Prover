theory CSP_F_law_RUN
imports CSP_T.CSP_T_law_RUN
        CSP_F_MF_MT
        CSP_F_law_fix
        CSP_F_law_step
        CSP_F_law_ref
begin



section \<open> RUN semantics \<close>


lemmas Run_setF = Ext_pre_choice_setF


subsubsection \<open> failures RUN \<close>


lemma cspF_Run :
    "(($Run A)::('e RunName, 'e) proc) =F (((Runfun (Run A)))::('e RunName, 'e) proc)"
by (rule cspF_unwind, simp_all)


lemma failures_Run :
    "failures ($Run A) MF = failures (? a:A -> $Run A) MF"
  apply (insert cspF_Run[of A])
by (simp add: cspF_eqF_semantics)


subsection \<open> in failures Run S \<close>


lemma failures_included_in_Run_lm :
    "noTick t & sett t \<subseteq> Ev ` S & Ev ` S \<inter> X = {} -->
     (t,X) :f failures ((FIX Runfun) (Run S)) M"
  apply (induct_tac t rule: induct_trace)

  (* <> *)
    apply (intro impI conjI)
    apply (simp add: FIX_def in_failures)
    apply (rule_tac x="Suc 0" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)

  (* <Tick> *)
    apply (simp)

  (* <Ev a> ^^^ s *)
    apply (simp)
    apply (intro impI)
    apply (simp)
    apply (elim conjE)
    apply (simp add: FIX_def in_failures)

    apply (elim exE)

    apply (rule_tac x="Suc n" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)
    apply (simp add: image_def)
done

lemma failures_included_in_Run :
  "[| noTick t ; sett t \<subseteq> Ev ` S ; Ev ` S \<inter> X = {} |] ==>
   (t,X) :f failures ((FIX Runfun) (Run S)) M"
by (simp add: failures_included_in_Run_lm)




subsection \<open> $Run {} =F DIV \<close>


lemmas DIV_setF = emptyset_in_setF

lemma not_cspF_Run_DIV : "~ (($Run {})::('a RunName,'a) proc) =F DIV"
  apply (rule notI)
  apply (erule cspF_rw_leftE)
  apply (rule cspF_unwind, simp, simp)
  apply (simp add: cspF_semantics)
  apply (simp add: traces_iff)
  apply (simp add: failures_iff)
  by (simp add: Abs_setF_inject STOP_setF empF_def)



subsection \<open> RUN {} =F DIV \<close>


lemma not_cspF_RUN_DIV : "~ RUN {} =F DIV"
by (simp add: RUN_def, rule not_cspF_Run_DIV)




subsection \<open> $Run {} =F STOP \<close>


lemma cspF_Run_STOP : "(($Run {})::('a RunName,'a) proc) =F STOP"
  apply (rule cspF_rw_left, rule cspF_unwind)
  apply (simp, simp)
  apply (simp add: cspF_semantics)
  apply (simp add: traces_iff)
  apply (simp add: failures_iff)
done



subsection \<open> RUN {} =F STOP \<close>


lemma cspF_RUN_STOP : "RUN {} =F STOP"
by (simp add: RUN_def, rule cspF_Run_STOP)




subsection \<open> $Run S <=F DIV \<close>


lemma cspF_Run_ref_DIV : "(($Run S)::('a RunName,'a) proc) <=F DIV"
by (rule cspF_DIV_top)



subsection \<open> $Run S <=F STOP \<close>


lemma cspF_Run_ref_STOP : "(($Run {})::('a RunName,'a) proc) <=F STOP"
  apply (rule cspF_rw_left, rule cspF_unwind)
  apply (simp, simp)
  apply (simp add: cspF_semantics)
  apply (simp add: traces_iff)
  apply (simp add: failures_iff)
done


lemma not_cspF_Run_ref_STOP : "S \<noteq> {} \<Longrightarrow> ~ (($Run S)::('a RunName,'a) proc) <=F (STOP::('a RunName,'a) proc)"
  apply (rule notI)

  apply (erule cspF_rw_leftE)
  apply (rule cspF_FIX[of Runfun], simp_all)
  apply (simp add: cspF_semantics)

  apply (simp add: subdomT_iff in_traces)

  apply (simp add: subsetF_iff in_failures)

  apply (erule contrapos_np, simp)
  apply (drule_tac x=UNIV in spec)

    apply (simp add: FIX_def in_failures)
    apply (elim exE)
    apply (case_tac n)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_failures)
done



subsection \<open> ~ $Run S <=F SKIP \<close>


lemma not_cspF_Run_ref_SKIP :
    "~ (($Run S)::('a RunName,'a) proc) <=F (SKIP::('a RunName,'a) proc)"
  apply (simp add: cspF_cspT_semantics fstF_MF_MT)
  apply (simp add: not_cspT_Run_SKIP)
done


end