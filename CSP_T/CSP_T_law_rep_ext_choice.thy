           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2020         |
            |                  March 2021               |
            |                                           |
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021  (modified)   |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory CSP_T_law_rep_ext_choice
imports CSP_T_law_basic CSP_T_surj
begin

subsection \<open> Inductive external choice \<close>

lemma cspT_Inductive_ext_choice_cong :
    "x = y ==> [+] x =T[M,M] [+] y"
  by (simp)

lemma cspT_Inductive_ext_choice_One [simp]:
    "[+] [P] =T[M,M] P"
by (simp, rule cspT_Ext_choice_unit)

lemma cspT_Inductive_ext_choice_Cons_cong :
    "[| P =T[M1,M2] Q; [+] Ps =T[M1,M2] [+] Qs |] ==> [+] (P#Ps) =T[M1,M2] [+] (Q#Qs)"
by (simp, rule cspT_decompo, simp, simp)

lemma cspT_Inductive_ext_choice_map_cong :
    "ALL a : set x. PXf a =T[M1,M2] PXg a ==> ( [+] map PXf x) =T[M1,M2] ( [+] map PXg x)"
by (induct x, simp_all, rule cspT_decompo, simp, simp)


lemma cspT_Inductive_ext_choice_append :
    "[+] (l @ l2) =T[M,M] ( [+] l) [+] ( [+] l2)"
  apply (induct_tac l)
  apply (simp, rule cspT_rw_right, rule cspT_Ext_choice_unit, simp)
  apply (simp, rule cspT_rw_right, rule cspT_Ext_choice_assoc[THEN cspT_sym])
  by (rule cspT_decompo, simp_all)


lemma cspT_Subst_procfun_Inductive_ext_choice_map :
   "ALL i : set l. (PXf i) << Pf =T[M1,M2] PXg i
    ==> ( [+] map PXf l) << Pf =T[M1,M2] ( [+] map PXg l)"
by (induct l, simp_all, rule cspT_decompo, simp_all)

lemma cspT_Subst_procfun_comp_Inductive_ext_choice_map :
   "ALL i : set l. ((PXf i) << Pf) << Qf =T[M1,M2] PXg i
    ==> (( [+] map PXf l) << Pf) << Qf =T[M1,M2] ( [+] map PXg l)"
by (induct l, simp_all, rule cspT_decompo, simp_all)


lemma cspT_Inductive_ext_choice_if_P :
    "\<forall>x\<in> set L. P x \<Longrightarrow> \<forall>x\<in> set L. Q1 x =T[M,M] Q2 x \<Longrightarrow>
    [+] map (\<lambda>x. if (P x) then Q x else R) L =T[M,M] [+] map Q L"
  apply (rule cspT_Inductive_ext_choice_map_cong)
  by (rule, simp_all)



(*------------------------------------------------*
 | Inductive external choice to Ext_prefix_choice |
 *------------------------------------------------*)

theorem cspT_Inductive_ext_choice_to_Ext_pre_choice :
    "[+] map (\<lambda> e . e -> PXf e) l =T[M,M] ? :set l -> PXf"
by (simp add: cspT_eqT_semantics traces_Inductive_ext_choice_to_Ext_pre_choice)



subsection \<open> Replicated external choice \<close>

lemma cspT_Rep_ext_choice_cong :
    "X = Y ==> ALL i:set X. PXf i =T[M1,M2] PXg i ==>
    [+] :X .. PXf =T[M1,M2] [+] :Y .. PXg"
  apply (simp add: Rep_ext_choice_def)
  by (rule cspT_Inductive_ext_choice_map_cong, simp)


lemma cspT_Rep_ext_choice_one [simp]:
    "[+] :[x] .. Pf =T[M,M] Pf x"
  by (simp add: Rep_ext_choice_def, rule cspT_Ext_choice_unit)

lemma cspT_Rep_ext_choice_singleton [simp]:
    "[+] :asList {x} .. Pf =T[M,M] Pf x"
  by (simp add: asList_def)


lemma cspT_Subst_procfun_Rep_ext_choice :
   "ALL i:set l. (PXf i) << Pf =T[M1,M2] PXf i ==>
    ( [+] :l .. PXf) << Pf =T[M1,M2] ( [+] :l .. PXf)"
  apply (simp add: Rep_ext_choice_def)
  by (rule cspT_Subst_procfun_Inductive_ext_choice_map, simp_all)


lemma cspT_Rep_ext_choice_if_P :
    "\<forall>x\<in> set L. P x \<Longrightarrow> \<forall>x\<in> set L. Q1 x =T[M,M] Q2 x \<Longrightarrow> [+] :L .. (\<lambda>x. if (P x) then Q x else R) =T[M,M] [+] x:L .. Q x"
  apply (rule cspT_Rep_ext_choice_cong)
  by (rule, simp_all)


lemma cspT_decompo_Rep_ext_choice:
    "[| I = J ; !! i. i: set I ==> Pf i <=T[M1,M2] Qf i |] ==> [+] i:I .. Pf i <=T[M1,M2] [+] i:I .. Qf i" 
  apply (simp add: cspT_semantics)
  apply (rule subdomTI)
  apply (simp add: subdomT_iff)
  apply (simp add: in_traces_Rep_ext_choice)
  by (auto)


(*------------------------------------------------*
 |    Rep external choice to Ext_prefix_choice    |
 *------------------------------------------------*)

theorem cspT_Rep_ext_choice_to_Ext_pre_choice :
    "[+]X .. (\<lambda>x . x -> PXf x) =T[M,M] ? :set X -> (\<lambda>x . PXf x)"
  apply (simp add: Rep_ext_choice_def)
  apply (rule cspT_rw_left)
  apply (rule cspT_Inductive_ext_choice_to_Ext_pre_choice)
  by (simp)




(* Rep_ext_choice using Proc_T - Code extracted from CSPIO *)

(*definition
   Rep_ext_choice :: "'i set => ('i => ('p,'a) proc) => ('p,'a) proc" ("(1[+] :_ .. /_)" [900,74] 74)

where "[+] :I .. Pf == (Proc_T (Rep_ext_choice_domT I (%i. (traces (Pf i) MT))))"

syntax
  "@Rep_ext_choice":: 
      "pttrn => 'i set => ('p,'a) proc => ('p,'a) proc"  
                               ("(1[+] _:_ .. /_)" [900,900,74] 74)
translations
  "[+] i:I .. P"    == "[+] :I .. (%i. P)"*)

definition
   Rep_ext_choice_set :: "'i set => ('i => 'a domT) => 'a trace set"
where "Rep_ext_choice_set == (%I Tf. {u. u = <> | (EX i:I. u :t Tf i)})"
      (* also see Rep_int_choice_domT in CSP_T/CSP_T_traces *)

definition
   Rep_ext_choice_domT :: "'i set => ('i => 'a domT) => 'a domT"
where "Rep_ext_choice_domT == (%I Tf. Abs_domT (Rep_ext_choice_set I Tf))"


lemma traces_Inductive_ext_choice_to_traces_Proc_T_lm :
    "I = set x --> traces ([+] map Pf x) M = traces (Proc_T (Rep_ext_choice_domT I (\<lambda>i. traces (Pf i) M))) M"
  apply (simp add: traces_Proc_T)
  apply (simp add: Rep_ext_choice_domT_def)
  apply (simp add: Rep_ext_choice_set_def)
  apply (induct_tac x)
   apply (simp add: traces.simps Inductive_ext_choice_traces)
   apply (simp add: traces.simps Inductive_ext_choice_traces)
    apply (simp add: S_UnT_T set_CollectT_commute_left)
    apply (rule)
    apply (rule CollectT_eq, rule disj_cong, simp)
    apply (rule CollectT_open_memT)
    by (simp add: Inductive_external_choice_domT)


lemma traces_Inductive_ext_choice_to_traces_Proc_T :
    "I = set x ==> traces ([+] map Pf x) M = traces (Proc_T (Rep_ext_choice_domT I (\<lambda>i. traces (Pf i) M))) M"
  by (simp add: traces_Inductive_ext_choice_to_traces_Proc_T_lm)


lemma traces_Rep_ext_choice_to_traces_Proc_T :
    "traces ([+] :I ..Pf) M = traces (Proc_T (Rep_ext_choice_domT (set I) (\<lambda>i. traces (Pf i) M))) M"
  apply (simp add: traces_Proc_T)
  apply (simp add: Rep_ext_choice_domT_def)
  apply (simp add: Rep_ext_choice_set_def)
  by (simp add: traces.simps Rep_ext_choice_traces)

lemma in_traces_Inductive_ext_choice_to_in_traces_Proc_T:
    "(u :t traces([+] map Pf I) M) = (u :t traces(Proc_T (Rep_ext_choice_domT (set I) (\<lambda>i. traces (Pf i) M))) M)"
  by (simp add: traces_Inductive_ext_choice_to_traces_Proc_T)

lemma in_traces_Rep_ext_choice_to_in_traces_Proc_T:
    "(u :t traces([+] :I .. Pf) M) = (u :t traces(Proc_T (Rep_ext_choice_domT (set I) (\<lambda>i. traces (Pf i) M))) M)"
  by (simp add: traces_Rep_ext_choice_to_traces_Proc_T)

lemma cspT_Rep_ext_choice_to_Proc_T :
    "[+] :I .. Pf =T[M,M] (Proc_T (Rep_ext_choice_domT (set I) (%i. (traces (Pf i) M))))"
  apply (simp add: Rep_ext_choice_def)
  apply (simp add: cspT_semantics)
  apply (simp add: traces_Proc_T)
  apply (simp add: Rep_ext_choice_domT_def)
  apply (simp add: Rep_ext_choice_set_def)
  apply (case_tac "I=[]")
    apply (simp add: traces_def)
    apply (simp add: Inductive_ext_choice_traces)
  done


end