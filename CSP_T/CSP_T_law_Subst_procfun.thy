           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2020         |
            |                  March 2021               |
            |                                           |
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021 (modified)    |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory CSP_T_law_Subst_procfun
imports CSP_T_law_basic
begin


lemma cspT_Subst_procfun_id :
    "noPN(P) ==> P << (Pf::'a \<Rightarrow> ('b,'e) proc) =T[M1,M2] P"
  apply (induct P, simp_all)
by (rule cspT_decompo, simp_all)+

lemma cspT_Subst_procfun_cong :
    "P = Q ==> P << Pf =T[M,M] Q << (Pf::'a \<Rightarrow> ('b,'e) proc)"
by (simp)

lemma cspT_trans_Subst_procfun_cong :
    "P << Pf =T[M1,M1] R ==> Q << Pf =T[M2,M2] S ==> R =T[M1,M2] S ==> (P << Pf) =T[M1,M2] (Q << (Pf::'a \<Rightarrow> ('b,'e) proc))"
  apply (rule cspT_rw_left, simp_all)
  apply (rule cspT_rw_right, simp_all)
  done

lemma cspT_Subst_procfun_step :
    "noPN P ==> P =T[M3,M2] Q ==> (P << (Pf::'a \<Rightarrow> ('b,'e) proc)) =T[M1,M2] Q"
  apply (rule cspT_trans_right_eq, simp)
  by (rule cspT_Subst_procfun_id, simp)

lemma cspT_Subst_procfun_comp_step :
    "noPN P ==> P =T[M3,M2] Q ==> (P << (Pf::'a \<Rightarrow> ('b,'e) proc)) << (Qf::'b \<Rightarrow> ('c,'e) proc) =T[M1,M2] (Q::('d,'e) proc)"
  apply (rule cspT_trans_right_eq, simp)
  apply (rule cspT_Subst_procfun_step)
  apply (rule noPN_Subst, simp)
  by (rule cspT_Subst_procfun_step, simp, rule cspT_reflex)


lemma cspT_trans_Subst_procfun_step :
    "P << Pf =T[M1,M1] R ==> R =T[M1,M2] Q ==> (P << (Pf::'a \<Rightarrow> ('b,'e) proc)) =T[M1,M2] Q"
  by (rule cspT_rw_left, simp_all)

lemma cspT_trans_Subst_procfun_comp_step :
    "P << Pf = P2 ==> P2 << Qf =T[M1,M2] Q ==>
    (P << (Pf::'a \<Rightarrow> ('b,'e) proc)) << (Qf::'b \<Rightarrow> ('c,'e) proc) =T[M1,M2] Q"
  apply (rule cspT_trans_right_eq, simp)
  by (rule cspT_Subst_procfun_cong, simp)



(*
lemma cspT_Subst_procfun_comp :
    "P << Pf = Q
     ==> Q << Qf =T[M1,M2] P << (Pf <<< Qf)
     ==> (P << Pf) << Qf =T[M1,M2] P << (Pf <<< Qf)"
by (simp add: Subst_procfun_prod_def)

lemma cspT_Subst_procfun_comp_simp :
    "P << Pf = Q
     ==> Q << Qf =T[M1,M2] R
     ==> (P << Pf) << Qf =T[M1,M2] R"
by (simp add: Subst_procfun_prod_def)


lemma cspT_Subst_procfun_id2 :
    "noPN(P) ==> (P << Pf1) << Pf2 =T[M,M] (P::('p,'e)proc)"
  apply (induct P, simp_all)
  by (rule cspT_decompo, simp_all)+
*)

lemma cspT_Subst_procfun_Parallel_id :
    "noPN(P) ==> noPN(Q) ==> (P |[X]| Q) << Pf =T[M1,M2] ((P |[X]| Q)::('p,'e)proc)"
  apply (simp, rule cspT_decompo, simp_all)
  by (rule cspT_Subst_procfun_id, simp)+

end