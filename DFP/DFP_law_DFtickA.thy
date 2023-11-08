           (*-------------------------------------------*
            |                  DFtickA X                |
            |                                           |
            |                 2022 / 2023               |
            |                                           |
            |        CSP-Prover on Isabelle2021         |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_law_DFtickA
imports DFP_DFtickA
begin


subsection \<open> Hiding \<close>


lemma cspF_DFtickA_empty_refF :
    "(($DFtickA {})::('e DFtickName, 'e) proc) <=F SKIP"
  apply (cspF_unwind, cspF_auto)
by (rule cspF_Int_choice_left2, simp)

lemma cspF_DFtickA_empty_eqF :
    "(($DFtickA {})::('e DFtickName, 'e) proc) =F DIV |~| SKIP"
by (cspF_unwind)





lemma hide_tr_empty : "s --tr {} = s"
by (induct_tac s rule: induct_trace, simp_all)

lemma cspF_Hidding_empty_refF :
    "P -- {} <=F P"
  apply (simp add: cspF_semantics)
  apply (rule)
  apply (rule subdomTI, simp add: in_traces hide_tr_empty)
  apply (rule subsetFI, simp add: in_failures hide_tr_empty)
done

lemma cspF_Hidding_empty_eqF :
    "P -- {} =F P"
  apply (simp add: cspF_semantics)
  apply (intro conjI)
  apply (simp add: traces_iff hide_tr_empty)
  apply (simp add: failures_iff hide_tr_empty)

  apply (auto simp add: memF_def Abs_setF_inverse)
by (simp add: Rep_setF_inverse)



(*((\<exists>a\<in>A. Ev a \<notin> Y) \<or> *)
lemma DeadlockFree_Hiding :
    "A \<noteq> {} \<Longrightarrow>
     \<forall>t. t :t traces (P -- X) (fstF \<circ> MF) \<longrightarrow> sett t \<subseteq> Ev ` A \<union> {Tick} \<Longrightarrow>
     \<forall>t Y. (t, Y) :f failures (P -- X) MF \<longrightarrow> Y \<subseteq> Evset \<Longrightarrow>
     Ev ` A \<subseteq> Ev ` X \<Longrightarrow>
     [insert Tick (Ev ` A)]-DeadlockFree P \<Longrightarrow> [insert Tick (Ev ` A)]-DeadlockFree (P -- X)"
  apply (simp add: DeadlockFree_def)
  apply (rule allI, rule impI)
  apply (simp add: in_failures in_traces)
  apply (rule allI, rule impI)
  apply (simp)
  apply (erule disjE, simp add: image_def)
  apply (rule non_memF_F2[of _ "insert Tick (Ev ` A)"], simp, blast)
done









lemma traces_hidding_if :
    "\<forall>t. t :t traces (P) (fstF \<circ> MF) \<longrightarrow> sett t \<subseteq> Ev ` A \<union> {Tick} \<Longrightarrow>
     \<forall>t. t :t traces (P -- X) (fstF \<circ> MF) \<longrightarrow> sett t \<subseteq> Ev ` A \<union> {Tick}"
  apply (simp add: in_traces)
  apply (force)
done

lemma failures_hidding_if:
    "\<forall>t Y. (t, Y) :f failures (P) MF \<longrightarrow> (Y \<subseteq> Evset) \<Longrightarrow>
     \<forall>t Y. (t, Y) :f failures (P -- X) MF \<longrightarrow> (Y \<subseteq> Evset)"
  apply (simp add: in_failures)
  apply (force)
done


lemma dfpA_Hiding :
    "Ev ` A \<subseteq> Ev ` X \<Longrightarrow>
     \<forall>t. t :t traces P (fstF \<circ> MF) \<longrightarrow> sett t \<subseteq> Ev ` A \<union> {Tick} \<Longrightarrow>
     \<forall>t Y. (t,Y) :f failures P MF \<longrightarrow> Y \<subseteq> Evset \<Longrightarrow>
     $DFtickA A <=F P \<Longrightarrow> $DFtickA A <=F P -- X"
  apply (case_tac "X = {}")
  (* X = {} *)
  apply (simp)
    apply (rule cspF_rw_left, rule cspF_DFtickA_empty_eqF)
    apply (erule cspF_rw_leftE, rule cspF_DFtickA_empty_eqF)

    apply (rule cspF_rw_right, rule cspF_Hidding_empty_eqF, simp)

  (* X \<noteq> {} *)
  apply (subgoal_tac "Ev ` A \<subseteq> Ev ` X ==> Ev ` A \<subseteq> Ev ` X \<union> {Tick}")

  apply (simp)
  apply (insert traces_hidding_if[of P A X])
  apply (drule impI, drule mp, intro allI impI, simp)
  apply (insert failures_hidding_if[of P X])
  apply (drule impI, drule mp, intro allI impI, simp)

  apply (simp add: DeadlockFree_DFtickA_ref[THEN sym])
  apply (rule DeadlockFree_Hiding[of X], simp_all)
  apply (intro allI impI)
  apply (drule_tac x=t in spec)
  apply (drule_tac x=t in spec)
  apply (drule_tac x=t in spec)
  apply (drule_tac x=t in spec, simp)
  apply (elim subsetE, intro subsetI, fast)

  apply (fast)
done


end