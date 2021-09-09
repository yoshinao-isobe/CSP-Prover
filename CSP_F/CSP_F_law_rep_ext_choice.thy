           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021               |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory CSP_F_law_rep_ext_choice
imports CSP_F_law_decompo CSP_F_law_basic
        CSP_T.CSP_T_law_rep_ext_choice
begin

subsection \<open> Inductive external choice \<close>

lemma cspF_Inductive_ext_choice_Cons_cong :
    "\<lbrakk> P =F Q; [+] Ps =F [+] Qs \<rbrakk> \<Longrightarrow> [+] (P#Ps) =F [+] (Q#Qs)"
by (simp, rule cspF_decompo, simp, simp)

lemma cspF_Inductive_ext_choice_map_cong :
    "\<forall> a \<in> set x. PXf a =F PXg a \<Longrightarrow> ( [+] map PXf x) =F ( [+] map PXg x)"
by (induct x, simp_all, rule cspF_decompo, simp, simp)


lemma cspF_Inductive_ext_choice_One [simp]:
    "[+] [P] =F P"
by (simp, rule cspF_unit)

lemma cspF_Inductive_ext_choice_map_to_List :
    "map PXf x = l \<Longrightarrow> ( [+] map PXf x) =F ( [+] l)"
by (simp)


lemma cspF_Inductive_ext_choice_map_to_List_Cons :
    "l \<noteq> [] \<Longrightarrow> [+] map PXf l =F [+] ( (PXf (hd l)) # map PXf (tl l) )"
  apply (rule cspF_Inductive_ext_choice_map_to_List)
by (induct l, simp, simp add: map_def)



lemma cspF_Subst_procfun_Inductive_ext_choice_map_Nil :
   "( [+] map PXf []) << Bf =F ( [+] map PXf [])"
by (auto)

lemma cspF_Subst_procfun_Inductive_ext_choice_map :
   "\<forall> i \<in> set l. (PXf i) << Pf =F PXg i
    \<Longrightarrow> ( [+] map PXf l) << Pf =F ( [+] map PXg l)"
by (induct l, simp_all, rule cspF_decompo, simp_all)

lemma cspF_Subst_procfun_comp_Inductive_ext_choice_map :
   "\<forall> i \<in> set l. ((PXf i) << Pf) << Qf =F PXg i
    \<Longrightarrow> (( [+] map PXf l) << Pf) << Qf =F ( [+] map PXg l)"
by (induct l, simp_all, rule cspF_decompo, simp_all)


(*------------------------------------------------*
 | Inductive external choice to Ext_prefix_choice |
 *------------------------------------------------*)

theorem cspF_Inductive_ext_choice_to_Ext_pre_choice :
    "[+] map (\<lambda> e . e -> PXf e) l =F[M,M] ? :set l -> PXf"
apply (simp add: cspF_cspT_eqF_semantics failures_Inductive_ext_choice_to_Ext_pre_choice)
by (rule cspT_Inductive_ext_choice_to_Ext_pre_choice)


subsection \<open> Replicated external choice \<close>

lemma cspF_Rep_ext_choice_to_Inductive_ext_choice :
    "finite X \<Longrightarrow> l = (SOME y. y isListOf X)
     \<Longrightarrow> [+] x:X .. PXf x =F[M,M] [+] (map PXf l)"
by (simp add: Rep_ext_choice_def)

lemma cspF_Rep_ext_choice_cong :
    "PXf =F PXg \<and> X = Y \<Longrightarrow> ( [+] x:X .. PXf) =F ( [+] x:Y .. PXg)"
by (simp add: Rep_ext_choice_def cspF_Inductive_ext_choice_map_cong)


(*------------------------------------------------*
 |    Rep external choice to Ext_prefix_choice    |
 *------------------------------------------------*)

theorem cspF_Rep_ext_choice_to_Ext_pre_choice :
    "finite X \<Longrightarrow> [+]X .. (\<lambda>x . x -> PXf x) =F[M,M] ? :X -> (\<lambda>x . PXf x)"
  apply (simp add: Rep_ext_choice_def)
  apply (rule someI2_ex, rule isListOf_EX, simp)
  apply (rule cspF_rw_left)
  apply (rule cspF_Inductive_ext_choice_to_Ext_pre_choice)
  by (simp add: isListOf_set_eq)

end