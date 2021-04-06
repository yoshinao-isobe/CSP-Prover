           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2020         |
            |                  March 2021  (modified)   |
            |                                           |
            |        Joabe Jesus (eComp POLI UPE)       |
            |        Joabe Jesus (CIn UFPE)             |
            *-------------------------------------------*)

theory CSP_T_law_rep_ext_choice
imports CSP_T_law_decompo CSP_T_law_basic
begin

subsection \<open> Inductive external choice \<close>

lemma cspT_Inductive_ext_choice_Cons_cong :
    "\<lbrakk> P =T Q; [+] Ps =T [+] Qs \<rbrakk> \<Longrightarrow> [+] (P#Ps) =T [+] (Q#Qs)"
by (simp, rule cspT_decompo, simp, simp)

lemma cspT_Inductive_ext_choice_map_cong :
    "\<forall> a \<in> set x. PXf a =T PXg a \<Longrightarrow> ( [+] map PXf x) =T ( [+] map PXg x)"
by (induct x, simp_all, rule cspT_decompo, simp, simp)


lemma cspT_Inductive_ext_choice_One [simp]:
    "[+] [P] =T P"
by (simp, rule cspT_unit)

lemma cspT_Inductive_ext_choice_map_to_List :
    "map PXf x = l \<Longrightarrow> ( [+] map PXf x) =T ( [+] l)"
by (simp)


lemma cspT_Inductive_ext_choice_map_to_List_Cons :
    "l \<noteq> [] \<Longrightarrow> [+] map PXf l =T [+] ( (PXf (hd l)) # map PXf (tl l) )"
  apply (rule cspT_Inductive_ext_choice_map_to_List)
by (induct l, simp, simp add: map_def)



lemma cspT_Subst_procfun_Inductive_ext_choice_map_Nil :
   "( [+] map PXf []) << Bf =T ( [+] map PXf [])"
by (auto)

lemma cspT_Subst_procfun_Inductive_ext_choice_map :
   "\<forall> i \<in> set l. (PXf i) << Pf =T PXg i
    \<Longrightarrow> ( [+] map PXf l) << Pf =T ( [+] map PXg l)"
by (induct l, simp_all, rule cspT_decompo, simp_all)

lemma cspT_Subst_procfun_comp_Inductive_ext_choice_map :
   "\<forall> i \<in> set l. ((PXf i) << Pf) << Qf =T PXg i
    \<Longrightarrow> (( [+] map PXf l) << Pf) << Qf =T ( [+] map PXg l)"
by (induct l, simp_all, rule cspT_decompo, simp_all)


(*** Traces Model Comparison to Ext_pre_choice operator ***)

theorem cspT_Inductive_ext_choice_to_Ext_pre_choice :
    "[+] map (\<lambda> e . e -> PXf e) l =T[M,M] ? :set l -> PXf"
by (simp add: cspT_eqT_semantics traces_Inductive_ext_choice_to_Ext_pre_choice)



subsection \<open> Replicated external choice \<close>

lemma cspT_Rep_ext_choice_to_Inductive_ext_choice :
    "finite X \<Longrightarrow> l = (SOME y. y isListOf X)
     \<Longrightarrow> [+] x:X .. PXf x =T[M,M] [+] (map PXf l)"
by (simp add: Rep_ext_choice_def)

lemma cspT_Rep_ext_choice_cong :
    "PXf =T PXg \<and> X = Y \<Longrightarrow> ( [+] x:X .. PXf) =T ( [+] x:Y .. PXg)"
by (simp add: Rep_ext_choice_def cspT_Inductive_ext_choice_map_cong)


(*** Traces Model Comparison to Ext_pre_choice operator ***)

theorem cspT_Rep_ext_choice_to_Ext_pre_choice :
    "finite X \<Longrightarrow> [+]X .. (\<lambda>x . x -> PXf x) =T[M,M] ? :X -> (\<lambda>x . PXf x)"
  apply (simp add: Rep_ext_choice_def)
  apply (rule someI2_ex, rule isListOf_EX, simp)
  apply (rule cspT_rw_left)
    apply (rule cspT_Inductive_ext_choice_to_Ext_pre_choice)
by (simp add: isListOf_set_eq)

end