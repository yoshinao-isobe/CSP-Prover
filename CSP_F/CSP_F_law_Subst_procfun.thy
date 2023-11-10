           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021               |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory CSP_F_law_Subst_procfun
imports CSP_F_law_basic
begin


lemma cspF_Subst_procfun_id :
    "noPN(P) ==> P << (Pf::'a \<Rightarrow> ('b,'e) proc) =F[M1,M2] P"
  apply (induct P, simp_all)
  by (rule cspF_decompo, simp_all)+

lemma cspF_Subst_procfun_cong :
    "P = Q ==> (P << Pf) =F[M,M] (Q << Pf)"
  by (simp)

lemma cspF_trans_Subst_procfun_cong :
    "P << Pf =F[M1,M1] R ==> Q << Pf =F[M2,M2] S ==> R =F[M1,M2] S ==> (P << Pf) =F[M1,M2] (Q << Pf)"
  apply (rule cspF_rw_left, simp_all)
  apply (rule cspF_rw_right, simp_all)
  done

lemma cspF_Subst_procfun_step :
    "noPN P ==> P =F[M3,M2] Q ==> (P << (Pf::'a \<Rightarrow> ('b,'e) proc)) =F[M1,M2] (Q::('c,'e) proc)"
  apply (rule cspF_trans_right_eq, simp)
  by (rule cspF_Subst_procfun_id, simp)

lemma cspF_Subst_procfun_comp_step :
    "noPN P ==> P =F[M3,M2] Q ==>
     (P << (Pf::'a \<Rightarrow> ('b,'e) proc)) << (Qf::'b \<Rightarrow> ('c,'e) proc) =F[M1,M2] (Q::('d,'e) proc)"
  apply (rule cspF_trans_right_eq, simp)
  apply (rule cspF_Subst_procfun_step)
  apply (rule noPN_Subst, simp)
  by (rule cspF_Subst_procfun_step, simp, rule cspF_reflex)


lemma cspF_trans_Subst_procfun_step :
    "P << Pf =F[M1,M1] R ==> R =F[M1,M2] Q ==> (P << (Pf::'a \<Rightarrow> ('b,'e) proc)) =F[M1,M2] Q"
  by (rule cspF_rw_left, simp_all)

lemma cspF_trans_Subst_procfun_comp_step :
    "P << Pf = P2 ==> P2 << Qf =F[M1,M2] Q ==>
    (P << (Pf::'a \<Rightarrow> ('b,'e) proc)) << (Qf::'b \<Rightarrow> ('c,'e) proc) =F[M1,M2] Q"
  apply (rule cspF_trans_right_eq, simp)
  by (rule cspF_Subst_procfun_cong, simp)

(*
lemma cspF_Pf_pn_map : "\<exists> x. Pf y = $x \<and> $x =F[M,N] $z ==> Pf y =F[M,N] $z"
by (erule exE, erule conjE, simp)

lemma cspF_Subst_procfun_map :
    "ALL x. \<exists>y. Pf x = $y \<and> $x =F[N,M] $y ==> P << Pf =F[M,N] (P::('p,'e)proc)"
apply (induct P, simp_all)
apply (rule cspF_decompo, simp_all)+
apply (erule_tac x="x" in allE)
apply (erule exE, erule conjE)
apply (simp, rule cspF_sym)
by (simp)

lemma cspF_Subst_procfun_pn_map :
    "\<exists> x. Pf y = $x \<and> $x =F[M,N] $z ==> ($y) << Pf =F[M,N] (($z)::('p,'e)proc)"
by (erule exE, simp)


lemma cspF_Pf_pn_id : "\<exists> x. Pf y = $x \<and> $x =F[M,N] $y ==> Pf y =F[M,N] $y"
by (rule cspF_Pf_pn_map)



lemma cspF_Subst_procfun_id2 :
    "ALL x. Pf x = $x ==> P << Pf =F[M,M] (P::('p,'e)proc)"
apply (rule cspF_Subst_procfun_map)
by (rule allI, rule_tac x="x" in exI, simp)

lemma cspF_Subst_procfun_pn_id :
    "\<exists> x. Pf y = $x \<and> $x =F[M,N] $y ==> ($y) << Pf =F[M,N] (($y)::('p,'e)proc)"
by (rule cspF_Subst_procfun_pn_map)

lemma cspF_Subst_procfun_cong :
    "P = Q ==> P << Pf =F[M,M] Q << Pf"
by (simp)

lemma cspF_Subst_procfun_pn_cong :
    "Pf P = Pf Q ==> ($P) << Pf =F[M,M] ($Q) << Pf"
by (simp)




lemma cspF_Subst_procfun_comp :
    "P << Pf = Q
     ==> Q << Qf =F[M1,M2] P << (Pf <<< Qf)
     ==> (P << Pf) << Qf =F[M1,M2] P << (Pf <<< Qf)"
by (simp add: Subst_procfun_prod_def)

lemma cspF_Subst_procfun_comp_simp :
    "P << Pf = Q
     ==> Q << Qf =F[M1,M2] R
     ==> (P << Pf) << Qf =F[M1,M2] R"
by (simp add: Subst_procfun_prod_def)

lemma cspF_Subst_procfun_comp_id :
    "noPN(P) ==> (P << Pf1) << Pf2 =F[M1,M2] (P::('p,'e)proc)"
  apply (induct P, simp_all)
by (rule cspF_decompo, simp_all)+
*)

lemma cspF_Subst_procfun_Parallel_id :
    "noPN(P) ==> noPN(Q) ==> (P |[X]| Q) << Pf =F[M1,M2] ((P |[X]| Q)::('p,'e)proc)"
  apply (simp, rule cspF_decompo, simp_all)
  by (rule cspF_Subst_procfun_id, simp)+

end