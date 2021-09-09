           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021               |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory CSP_F_law_Subst_procfun
imports CSP_F_law_basic
begin



lemma cspF_Pf_pn_map : "\<exists> x. Pf y = $x \<and> $x =F[M,N] $z \<Longrightarrow> Pf y =F[M,N] $z"
by (erule exE, erule conjE, simp)

lemma cspF_Subst_procfun_map :
    "\<forall>x. \<exists>y. Pf x = $y \<and> $x =F[N,M] $y \<Longrightarrow> P << Pf =F[M,N] (P::('p,'e)proc)"
apply (induct P, simp_all)
apply (rule cspF_decompo, simp_all)+
apply (erule_tac x="x" in allE)
apply (erule exE, erule conjE)
apply (simp, rule cspF_sym)
by (simp)

lemma cspF_Subst_procfun_pn_map :
    "\<exists> x. Pf y = $x \<and> $x =F[M,N] $z \<Longrightarrow> ($y) << Pf =F[M,N] (($z)::('p,'e)proc)"
by (erule exE, simp)


lemma cspF_Pf_pn_id : "\<exists> x. Pf y = $x \<and> $x =F[M,N] $y \<Longrightarrow> Pf y =F[M,N] $y"
by (rule cspF_Pf_pn_map)


lemma cspF_Subst_procfun_id :
    "noPN(P) \<Longrightarrow> P << Pf =F[M,M] (P::('p,'e)proc)"
  apply (induct P, simp_all)
by (rule cspF_decompo, simp_all)+

lemma cspF_Subst_procfun_id2 :
    "\<forall>x. Pf x = $x \<Longrightarrow> P << Pf =F[M,M] (P::('p,'e)proc)"
apply (rule cspF_Subst_procfun_map)
by (rule allI, rule_tac x="x" in exI, simp)

lemma cspF_Subst_procfun_pn_id :
    "\<exists> x. Pf y = $x \<and> $x =F[M,N] $y \<Longrightarrow> ($y) << Pf =F[M,N] (($y)::('p,'e)proc)"
by (rule cspF_Subst_procfun_pn_map)

lemma cspF_Subst_procfun_cong :
    "P = Q \<Longrightarrow> P << Pf =F[M,M] Q << Pf"
by (simp)

lemma cspF_Subst_procfun_pn_cong :
    "Pf P = Pf Q \<Longrightarrow> ($P) << Pf =F[M,M] ($Q) << Pf"
by (simp)


lemma cspF_Subst_procfun_comp :
    "P << Pf = Q
     \<Longrightarrow> Q << Qf =F[M1,M2] P << (Pf <<< Qf)
     \<Longrightarrow> (P << Pf) << Qf =F[M1,M2] P << (Pf <<< Qf)"
by (simp add: Subst_procfun_prod_def)

lemma cspF_Subst_procfun_comp_simp :
    "P << Pf = Q
     \<Longrightarrow> Q << Qf =F[M1,M2] R
     \<Longrightarrow> (P << Pf) << Qf =F[M1,M2] R"
by (simp add: Subst_procfun_prod_def)

lemma cspF_Subst_procfun_comp_id :
    "noPN(P) \<Longrightarrow> (P << Pf1) << Pf2 =F[M,M] (P::('p,'e)proc)"
  apply (induct P, simp_all)
by (rule cspF_decompo, simp_all)+

end