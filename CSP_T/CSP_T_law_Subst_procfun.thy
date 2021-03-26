           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2020         |
            |                  March 2021  (modified)   |
            |                                           |
            |        Joabe Jesus (eComp POLI UPE)       |
            |        Joabe Jesus (CIn UFPE)             |
            *-------------------------------------------*)

theory CSP_T_law_Subst_procfun
imports CSP_T_law_decompo CSP_T_law_basic
begin

lemma cspT_Subst_procfun_comp :
    "P << Pf = Q
     \<Longrightarrow> Q << Qf =T[M1,M2] P << (Pf <<< Qf)
     \<Longrightarrow> (P << Pf) << Qf =T[M1,M2] P << (Pf <<< Qf)"
by (simp add: Subst_procfun_prod_def)

lemma cspT_Subst_procfun_comp_simp :
    "P << Pf = Q
     \<Longrightarrow> Q << Qf =T[M1,M2] R
     \<Longrightarrow> (P << Pf) << Qf =T[M1,M2] R"
by (simp add: Subst_procfun_prod_def)


lemma cspT_Subst_procfun_id :
    "noPN(P) \<Longrightarrow> P << Pf =T[M,M] (P::('p,'e)proc)"
  apply (induct P, simp_all)
by (rule cspT_decompo, simp_all)+


lemma cspT_Subst_procfun_id2 :
    "noPN(P) \<Longrightarrow> (P << Pf1) << Pf2 =T[M,M] (P::('p,'e)proc)"
  apply (induct P, simp_all)
by (rule cspT_decompo, simp_all)+


lemma cspT_Subst_procfun_cong :
    "P = Q \<Longrightarrow> P << Pf =T[M,M] Q << Pf"
by (simp)

end