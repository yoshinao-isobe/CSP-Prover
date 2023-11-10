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

lemma cspF_Inductive_ext_choice_cong :
    "x = y ==> [+] x =F[M,M] [+] y"
  by (simp)

lemma cspF_Inductive_ext_choice_Cons_cong :
    "[| P =F[M1,M2] Q; [+] Ps =F[M1,M2] [+] Qs |] ==> [+] (P#Ps) =F[M1,M2] [+] (Q#Qs)"
  by (simp, rule cspF_decompo, simp, simp)

lemma cspF_Inductive_ext_choice_map_cong_lm :
    "x = y \<longrightarrow> (ALL a:set x. PXf a =F[M1,M2] PXg a) \<longrightarrow> ( [+] map PXf x) =F[M1,M2] ( [+] map PXg y)"
  apply (simp)
  apply (induct y arbitrary: x, simp_all)
  apply (rule, rule)
  apply (simp)
  by (rule cspF_decompo, simp_all)

lemma cspF_Inductive_ext_choice_map_cong :
    "x = y ==> ALL a:set x. PXf a =F[M1,M2] PXg a ==> ( [+] map PXf x) =F[M1,M2] ( [+] map PXg y)"
  by (simp add: cspF_Inductive_ext_choice_map_cong_lm)


lemma cspF_Inductive_ext_choice_append :
    "[+] (l @ l2) =F[M,M] ( [+] l) [+] ( [+] l2)"
  apply (induct_tac l)
  apply (simp, rule cspF_rw_right, rule cspF_Ext_choice_unit, simp)
  apply (simp, rule cspF_rw_right, rule cspF_Ext_choice_assoc[THEN cspF_sym])
  by (rule cspF_decompo, simp_all)


lemma cspF_Inductive_ext_choice_one [simp]:
    "[+] [P] =F[M,M] P"
  by (simp, rule cspF_unit)

lemma cspF_Inductive_ext_choice_singleton [simp]:
    "[+] asList {P} =F[M,M] P"
  by (simp add: asList_def, rule cspF_unit)


lemma cspF_Subst_procfun_Inductive_ext_choice_map :
   "ALL i:set l. (PXf i) << Pf =F[M1,M2] PXg i
    ==> ( [+] map PXf l) << Pf =F[M1,M2] ( [+] map PXg l)"
by (induct l, simp_all, rule cspF_decompo, simp_all)

lemma cspF_Subst_procfun_comp_Inductive_ext_choice_map :
   "ALL i:set l. ((PXf i) << Pf) << Qf =F[M1,M2] PXg i
    ==> (( [+] map PXf l) << Pf) << Qf =F[M1,M2] ( [+] map PXg l)"
  by (induct l, simp_all, rule cspF_decompo, simp_all)


lemma cspF_Inductive_ext_choice_if_P :                                               
    "\<forall>x\<in> set L. P x \<Longrightarrow> \<forall>x\<in> set L. Q1 x =F[M,M] Q2 x \<Longrightarrow>
    [+] map (\<lambda>x. if (P x) then Q1 x else R) L =F[M,M] [+] map Q2 L"
  apply (rule cspF_Inductive_ext_choice_map_cong, simp)
  by (rule, simp_all)

lemma cspF_Inductive_ext_choice_filtered :
    "[+] l =F[M,M] [+] (filter (\<lambda>x. x \<noteq> STOP) l)"
  apply (induct l, simp_all, rule)
  apply (rule)
    apply (rule cspF_decompo, simp_all)
  apply (rule)
    apply (rule cspF_rw_left, rule cspF_Ext_choice_unit, simp)
  done

lemma cspF_Inductive_ext_choice_filtered_map :
    "\<forall>x. Q x = (Pf x \<noteq> STOP) ==>
    [+] map Pf l =F[M,M] [+] map Pf (filter Q l)"
  apply (rule cspF_rw_left, rule cspF_Inductive_ext_choice_filtered)
  apply (simp add: filter_map comp_def)
  apply (rule cspF_Inductive_ext_choice_map_cong)
  apply (rule_tac f=filter in arg_cong2)
  by (rule, simp, simp_all)

lemma cspF_Inductive_ext_choice_filtered_map_if :
    "\<forall>x. Pf x \<noteq> STOP ==>
    [+] map (\<lambda>x. if Q x then Pf x else STOP) l =F[M,M] [+] map Pf (filter Q l)"
  apply (rule cspF_rw_left, rule cspF_Inductive_ext_choice_filtered)
  apply (simp add: filter_map comp_def)
  apply (rule cspF_rw_left, rule cspF_Inductive_ext_choice_if_P)
  apply (simp)
  apply (rule, rule cspF_reflex)
  by (simp)



lemma cspF_Inductive_ext_choice_idem :
    "l \<noteq> [] \<Longrightarrow> \<forall>x\<in> set l . Pf x =F[M,M] P \<Longrightarrow>
    [+] map Pf l =F[M,M] P"
  apply (induct l, simp_all)
  apply (case_tac l, simp_all)
  apply (rule cspF_rw_left, rule cspF_Ext_choice_unit, simp)
  apply (rule cspF_rw_left, rule cspF_decompo, rule cspF_reflex, simp)
  apply (rule cspF_rw_left, rule cspF_decompo, elim conjE, simp, rule cspF_reflex)
  by (rule cspF_Ext_choice_idem)

lemma cspF_Inductive_ext_choice_idem2 :
    "l \<noteq> [] \<Longrightarrow> [+] map (\<lambda>i. P) l =F[M,M] P"
  by (rule cspF_Inductive_ext_choice_idem, simp_all)



(*------------------------------------------------*
 | Inductive external choice to Ext_prefix_choice |
 *------------------------------------------------*)

theorem cspF_Inductive_ext_choice_to_Ext_pre_choice :
    "[+] map (\<lambda> e . e -> PXf e) l =F[M,M] ? :set l -> PXf"
  apply (simp add: cspF_cspT_eqF_semantics failures_Inductive_ext_choice_to_Ext_pre_choice)
  by (rule cspT_Inductive_ext_choice_to_Ext_pre_choice)



subsection \<open> Replicated external choice \<close>

lemma Rep_ext_choice_Nil [simp]:
    "[+] :[] .. P = STOP"
  by (simp add: Rep_ext_choice_def)

lemma cspF_Rep_ext_choice_cong :
    "X = Y ==> ALL i:set X. PXf i =F[M1,M2] PXg i ==>
    [+] :X .. PXf =F[M1,M2] [+] :Y .. PXg"
  apply (simp add: Rep_ext_choice_def)
  by (rule cspF_Inductive_ext_choice_map_cong, simp)

lemma cspF_Rep_ext_choice_append :
    "[+] :(l @ l2) .. Pf =F[M,M] ( [+] :l .. Pf) [+] ( [+] :l2 .. Pf)"
  apply (induct l arbitrary: l2)
  apply (simp add: Rep_ext_choice_def)
  apply (rule cspF_rw_right, rule cspF_Ext_choice_unit, simp)
  apply (simp add: Rep_ext_choice_def)
  apply (rule cspF_rw_right, rule cspF_Ext_choice_assoc[THEN cspF_sym])
  by (rule cspF_decompo, simp_all)

lemma cspF_Rep_ext_choice_append_to_Ext_choice :
    "\<forall>i \<in> set l2 \<inter> set l . Pf1 i =F[M,M] Pf2 i \<Longrightarrow>
     [+] :(l @ l2) .. (\<lambda>x. if (x \<in> set l) then Pf1 x else Pf2 x) =F[M,M] ( [+] :l .. Pf1) [+] ( [+] :l2 .. Pf2)"
  apply (rule cspF_rw_left, rule cspF_Rep_ext_choice_append)
  apply (rule cspF_decompo)
  apply (rule cspF_Rep_ext_choice_cong, simp, rule, simp)
  apply (rule cspF_Rep_ext_choice_cong, simp, rule, simp)
  done

lemma cspF_Rep_ext_choice_Nil [simp]:
    "[+] :[] .. P =F[M,M] STOP"
  by (simp add: Rep_ext_choice_def)

lemma cspF_Rep_ext_choice_one [simp]:
    "[+] :[x] .. P =F[M,M] P x"
  apply (simp add: Rep_ext_choice_def)
  by (rule cspF_Ext_choice_unit)

lemma cspF_Rep_ext_choice_singleton [simp]:
    "[+] :asList {x} .. Pf =F[M,M] Pf x"
  by (simp add: asList_def)

lemma cspF_Rep_ext_choice_Cons_step [simp]:
    "[+] :(x#l) .. Pf =F[M,M] Pf x [+] ( [+] :l .. Pf)"
  by (simp add: Rep_ext_choice_def)

lemmas cspF_Rep_ext_choice_step = cspF_Rep_ext_choice_Nil
                                  cspF_Rep_ext_choice_one
                                  cspF_Rep_ext_choice_singleton
                                  cspF_Rep_ext_choice_Cons_step


lemma cspF_Subst_procfun_Rep_ext_choice :
   "ALL i:set l. (PXf i) << Pf =F[M1,M2] PXg i ==>
    ( [+] :l .. PXf) << Pf =F[M1,M2] ( [+] :l .. PXg)"
  apply (simp add: Rep_ext_choice_def)
  by (rule cspF_Subst_procfun_Inductive_ext_choice_map, simp_all)


lemma cspF_Subst_procfun_comp_Rep_ext_choice :
   "ALL i:set l. ((PXf i) << Pf) << Qf =F[M1,M2] PXg i ==>
    (( [+] :l .. PXf) << Pf) << Qf =F[M1,M2] ( [+] :l .. PXg)"
  apply (simp add: Rep_ext_choice_def)
  by (rule cspF_Subst_procfun_comp_Inductive_ext_choice_map, simp_all)



lemma cspF_Rep_ext_choice_if_P :
    "\<forall>x\<in> set L. P x \<Longrightarrow> \<forall>x\<in> set L. Q1 x =F[M,M] Q2 x \<Longrightarrow>
    [+] :L .. (\<lambda>x. if (P x) then Q1 x else R) =F[M,M] [+] x:L .. Q2 x"
  apply (rule cspF_Rep_ext_choice_cong)
  by (rule, simp_all)

lemma cspF_Rep_ext_choice_filtered :
    "\<forall>x. Q x = (Pf x \<noteq> STOP) ==>
    [+] :l .. Pf =F[M,M] [+] :(filter Q l) ..  Pf"
  apply (simp only: Rep_ext_choice_def)
  by (rule cspF_Inductive_ext_choice_filtered_map, simp)


lemma cspF_Rep_ext_choice_filtered_if :
    "\<forall>x. Pf x \<noteq> STOP ==>
    [+] :l .. (\<lambda>x. if Q x then Pf x else STOP) =F[M,M] [+] :(filter Q l) ..  Pf"
  apply (simp only: Rep_ext_choice_def)
  by (rule cspF_Inductive_ext_choice_filtered_map_if, simp)


lemma cspF_Rep_ext_choice_idem :
    "l \<noteq> [] \<Longrightarrow> \<forall>x\<in> set l . Pf x =F[M,M] P \<Longrightarrow> [+] :l .. Pf  =F[M,M] P"
  apply (simp add: Rep_ext_choice_def)
  apply (rule cspF_rw_left, rule cspF_Inductive_ext_choice_idem, simp_all)
  by (rule cspF_reflex)

lemma cspF_Rep_ext_choice_idem2 :
    "l \<noteq> [] \<Longrightarrow> [+] x:l .. P  =F[M,M] P"
  apply (simp add: Rep_ext_choice_def)
  by (rule cspF_Inductive_ext_choice_idem2)


(*-----------------------------------------------*
 |    Rep external choice to Ext_prefix_choice    |
 *------------------------------------------------*)

theorem cspF_Rep_ext_choice_to_Ext_pre_choice :
    "[+]X .. (\<lambda>x . x -> PXf x) =F[M,M] ? :set X -> (\<lambda>x . PXf x)"
  apply (simp add: Rep_ext_choice_def)
  apply (rule cspF_rw_left, rule cspF_Inductive_ext_choice_to_Ext_pre_choice)
  by (simp)


end