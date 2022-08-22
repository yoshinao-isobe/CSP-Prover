           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021               |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory CSP_F_law_rep_interleaving
imports CSP_T.CSP_T_law_rep_interleaving CSP_F_law_basic CSP_F_law_SKIP CSP_F_law_step
begin

subsection \<open> Inductive interleave \<close>

lemma cspF_Inductive_interleave_cong :
    "x = y ==> ||| x =F[M,M] ||| y"
  by (simp)

lemma cspF_Inductive_interleave_One [simp]:
    "||| [P] =F[M,M] P"
  by (simp, rule cspF_Interleave_unit)

lemma cspF_Inductive_interleaving_Cons_cong :
    "[| P =F[M1,M2] Q; ||| Ps =F[M1,M2] ||| Qs |] ==> ||| (P#Ps) =F[M1,M2] ||| (Q#Qs)"
  by (simp, rule cspF_decompo, simp)

lemma cspF_Inductive_interleave_map_cong :
    "ALL a:set x. PXf a =F[M1,M2] PXg a ==> ( ||| map PXf x) =F[M1,M2] ( ||| map PXg x)"
  apply (induct x, simp_all)
  by (rule cspF_decompo, simp_all)

(*lemma cspF_Inductive_interleave_map_to_List :
    "map PXf x = l ==> ( ||| map PXf x) =F ( ||| l)"
  by (simp)

lemma cspF_Inductive_interleave_map_to_List_Cons :
    "l \<noteq> [] ==> ||| map PXf l =F ||| ( (PXf (hd l)) # map PXf (tl l) )"
  apply (rule cspF_Inductive_interleave_map_to_List)
  by (induct l, simp, simp add: map_def)*)

lemma cspF_Inductive_interleave_append :
    "||| (l @ l2) =F[M,M] ( ||| l) ||| ( ||| l2)"
  apply (induct_tac l)
  apply (simp, rule cspF_rw_right, rule cspF_Interleave_unit, simp)
  apply (simp, rule cspF_rw_right, rule cspF_Interleave_assoc[THEN cspF_sym])
  by (rule cspF_decompo, simp_all)


lemma cspF_Subst_procfun_Inductive_interleave_map :
   "ALL i:set l. (PXf i) << Pf =F[M1,M2] PXf i
    ==> ( ||| map PXf l) << Pf =F[M1,M2] ( ||| map PXf l)"
  apply (induct l, simp_all)
  by (rule cspF_decompo, simp_all)+




lemma cspF_Inductive_interleave_filter_map :
    "Q = (\<lambda>P. P \<noteq> SKIP) ==>
    ||| filter Q (map Pf l) =F[M,M] ||| map Pf l"
  apply (induct l, simp_all, rule, rule)
  apply (rule cspF_decompo, simp_all)
  by (rule, rule cspF_rw_right, rule cspF_Interleave_unit, simp)


lemma cspF_Inductive_interleave_map_filtered :
    "\<And>n. \<forall>i Tin b. Pf(i,Tin,b) = SKIP \<longleftrightarrow> \<not> Q(i,Tin,b) ==>
    ||| map Pf l =F[M,M] ||| map Pf (filter Q l)"
  apply (rule cspF_rw_right)
  apply (rule cspF_Inductive_interleave_cong)
  apply (rule_tac P="(\<lambda>P. (P \<noteq> SKIP))" in map_filter_2)
  apply (rule)
  apply (simp add: comp_def)
  apply (force)
  apply (rule cspF_Inductive_interleave_filter_map[THEN cspF_sym])
  by (force)

(*lemma cspF_Inductive_interleave_map_enumerate_filtered :
    "\<And>n. \<forall>i Tin b. Pf(i,Tin,b) = SKIP \<longleftrightarrow> \<not> Q(i,Tin,b) ==>
    ||| map Pf (enumerate n T\<^sub>i\<^sub>n\<^sub>s) =F[M,M] ||| map Pf (filter Q (enumerate n T\<^sub>i\<^sub>n\<^sub>s))"
  apply (rule cspF_rw_right)
  apply (rule cspF_Inductive_interleave_cong)
  apply (rule_tac P="(\<lambda>P. (P \<noteq> SKIP))" in map_filter_2)
  apply (rule)
  apply (simp add: comp_def)
  apply (force)
  apply (rule cspF_Inductive_interleave_filter_map[THEN cspF_sym])
  by (force)*)




lemma cspF_Inductive_interleave_remove1_step_lm :
    "a \<in> set (list) \<longrightarrow> distinct list \<longrightarrow>
    ||| map PXf list =F[M,M] PXf a ||| ||| map PXf (remove1 a list)"
  apply (induct list rule: length_induct)
  apply (case_tac xs)
  apply (simp)
  apply (rule, rule)
  apply (simp)
  apply (rule, simp)
    apply (rule cspF_rw_right, rule cspF_Interleave_left_commute)
    apply (rule cspF_decompo, simp, simp)
  by (erule_tac x="list" in allE, simp)


lemma cspF_Inductive_interleave_remove1_step :
    "a \<in> set (list) \<Longrightarrow> distinct list \<Longrightarrow>
    ||| map PXf list =F[M,M] PXf a ||| ||| map PXf (remove1 a list)"
  by (simp add: cspF_Inductive_interleave_remove1_step_lm)



lemma cspF_Inductive_interleave_map_cong_asList_set_lm :
    "distinct L \<longrightarrow>
    ||| map PXf L =F[M,M] ||| map PXf (asList (set L))"

  apply (simp only: asList_def)

  apply (rule someI2_ex, rule isListOf_EX, simp)
  apply (frule isListOf_distinct)
  apply (drule isListOf_set_eq)


  apply (induct L rule: length_induct)

  apply (rule)

  apply (case_tac xs)
    apply (simp)
    apply (simp)
  apply (erule_tac x="list" in allE, simp)
  apply (elim conjE)

  apply (erule_tac x="remove1 a x" in allE, simp)

  apply (case_tac x)
    apply (simp)

    apply (simp only: insert_def Un_def)
    apply (rule cspF_rw_left, rule cspF_decompo, simp, rule cspF_reflex, simp)

    apply (case_tac "a=aa", simp, simp)

    apply (simp add: set_eq_iff)
    apply (erule_tac x="a" in allE, simp)

    apply (rule cspF_rw_left, rule cspF_Interleave_left_commute)
    apply (rule cspF_decompo, simp, simp)

    apply (clarify)

    by (rule cspF_sym, rule cspF_Inductive_interleave_remove1_step, simp_all)


lemma cspF_Inductive_interleave_map_cong_asList_set :
    "distinct L \<Longrightarrow>
    ||| map PXf L =F[M,M] ||| map PXf (asList (set L))"
  by (simp add: cspF_Inductive_interleave_map_cong_asList_set_lm)




subsection \<open> Replicated interleaving \<close>

lemma cspF_Rep_interleaving_cong :
    "ALL i:set X. PXf i =F[M1,M2] PXg i ==> X = Y ==> ||| :X .. PXf =F[M1,M2] ||| :Y .. PXg"
  apply (simp add: Rep_interleaving_def)
  by (rule cspF_Inductive_interleave_map_cong, simp)


lemma Rep_interleaving_nil [simp]:
    "||| :[] .. Pfx = SKIP"
  by (simp add: Rep_interleaving_def)

lemma cspF_Rep_interleaving_one [simp]:
    "||| :[x] .. Pf =F[M,M] Pf x"
  by (simp add: Rep_interleaving_def, rule cspF_Interleave_unit)

lemma cspF_Rep_interleaving_singleton [simp]:
    "||| :asList {x} .. Pf =F[M,M] Pf x"
  by (simp add: asList_def)

lemma cspF_Rep_interleaving_Cons :
    "( ||| :(a # list) .. PXf) =F[M,M] (PXf a ||| ( ||| :list .. PXf))"
  by (simp add: Rep_interleaving_def)


lemma cspF_Subst_procfun_Rep_interleaving :
   "ALL i:set l. (PXf i) << Pf =F[M1,M2] PXf i ==>
    ( ||| :l .. PXf) << Pf =F[M1,M2] ( ||| :l .. PXf)"
  apply (simp add: Rep_interleaving_def)
  by (rule cspF_Subst_procfun_Inductive_interleave_map, simp_all)



lemma cspF_Rep_interleaving_append :
    "( ||| :(list @ l2) .. PXf) =F[M,M] (( ||| :list .. PXf) ||| ( ||| :l2 .. PXf))"
  apply (simp add: Rep_interleaving_def)
  by (simp add: cspF_Inductive_interleave_append)




subsection  \<open> Inductive_interleave to Ext_pre_choice \<close>

abbreviation disjnt_image_on
where "disjnt_image_on f S == (ALL x : S . ALL y : S. x \<noteq> y \<longrightarrow> disjnt (f x) (f y))"

abbreviation disjnt_image
where "disjnt_image f == disjnt_image_on f UNIV"


lemma disjnt_domain2 :
    "a \<notin> S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> f x \<Longrightarrow> \<forall>y\<in>S. a \<noteq> y \<longrightarrow> disjnt (f a) (f y) \<Longrightarrow> \<not> (y \<in> f a)"
  by (simp add: disjnt_def Int_def, fast)

lemma disjnt_domain3 :
    "disjnt Y S \<Longrightarrow> x \<in> S \<Longrightarrow> \<not> (x \<in> Y)"
  by (simp add: disjnt_def Int_def, fast)







definition branchSrc_on :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> ('b \<Rightarrow> 'a)"
where "branchSrc_on f S == (\<lambda>y. (THE x. x \<in> S \<and> y \<in> f x))"

abbreviation branchSrc
where "branchSrc f == branchSrc_on f UNIV"





lemma branchSrc_on_iff :
    "inj_on f S \<Longrightarrow> disjnt_image_on f S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> f x \<Longrightarrow>
     branchSrc_on f S y = x"
  apply (auto simp add: branchSrc_on_def)
  apply (rule the_equality, simp)
  apply (case_tac "x = xa", simp, simp add: disjnt_iff Ball_def)
  by (erule_tac x="x" in allE, simp, erule_tac x="xa" in allE, simp)

lemma branchSrc_on_E :
    "inj_on f S \<Longrightarrow> disjnt_image_on f S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> f x \<Longrightarrow> P x \<Longrightarrow>
     P (branchSrc_on f S y)"
  apply (subst cong[of P], simp)
  by (rule branchSrc_on_iff, simp_all)

lemma branchSrc_on_singleton_iff :
    "inj_on f {a} \<Longrightarrow> y \<in> f a \<Longrightarrow> disjnt_image_on f {a} \<Longrightarrow>
     branchSrc_on f {a} y = a"
  by (rule branchSrc_on_iff, simp_all)

lemma branchSrc_on_insert_iff :
    "inj_on f (insert a S) \<Longrightarrow> y \<in> f a \<Longrightarrow> disjnt_image_on f (insert a S) \<Longrightarrow>
     branchSrc_on f (insert a S) y = a"
  by (rule branchSrc_on_iff, simp_all)




lemma branchSrc_iff :
    "inj f \<Longrightarrow> y \<in> f x \<Longrightarrow> disjnt_image f \<Longrightarrow>
     branchSrc f y = x"
  apply (auto simp add: branchSrc_on_def)
  apply (rule the_equality, simp)
  apply (case_tac "x = xa", simp, simp)
  apply (erule_tac x="x" in allE, erule_tac x="xa" in allE)
  by (simp add: disjnt_iff)




definition isBranchSrc_on
where "isBranchSrc_on g f S == (ALL x : S. ALL y : (f x) . g y = x)"

abbreviation isBranchSrc
where "isBranchSrc g f == isBranchSrc_on g f UNIV"

lemma isBranchSrc_on_iff :
    "inj_on f S \<Longrightarrow> x : S \<Longrightarrow> y \<in> f x \<Longrightarrow> isBranchSrc_on g f S \<Longrightarrow>
     g y = a \<longleftrightarrow> x = a"
  by (auto simp add: isBranchSrc_on_def)

lemma isBranchSrc_branchSrc :
    "inj (f::('a \<Rightarrow> 'b set)) \<Longrightarrow> disjnt_image f \<Longrightarrow>
    isBranchSrc (branchSrc f) f"
  apply (simp add: branchSrc_on_def isBranchSrc_on_def)
  apply (rule, rule, rule the_equality, simp)
  apply (simp add: inj_def disjnt_iff)
  apply (erule_tac x="x" in allE, erule_tac x="x" in allE)
  apply (erule_tac x="xa" in allE, erule_tac x="xa" in allE)
  by (auto)

lemma isBranchSrc_on_branchSrc_on :
    "inj_on (f::('a \<Rightarrow> 'b set)) S \<Longrightarrow> disjnt_image_on f S \<Longrightarrow>
    isBranchSrc_on (branchSrc_on f S) f S"
  apply (simp add: branchSrc_on_def isBranchSrc_on_def)
  apply (rule, rule, rule the_equality, simp)
  apply (elim conjE)
  apply (simp add: inj_on_def disjnt_iff)
  by (force)






(*lemma cspF_Inductive_interleave_f_g_to_Ext_pre_choice_lm :
    "inj f ==> isBranchSrc g f ==>
     l \<noteq> [] \<longrightarrow> distinct l \<longrightarrow> disjnt_image_on f (set l) \<longrightarrow>
    ||| map (\<lambda>x. ? :(f x) -> PXf) l =F[M,M]
    ? x:\<Union> (f ` set l) -> (PXf x ||| ( ||| map (\<lambda>w. ? :(f w) -> PXf) (remove1 (g x) l) ) )"
  apply (induct_tac l)
  apply (rule, simp)
  apply (rule, simp, rule)
  apply (elim conjE)

  apply (case_tac "list = []")

  apply (simp)
  apply (rule cspF_rw_left, rule cspF_Interleave_unit)
  apply (rule cspF_decompo, simp)
  apply (simp add: isBranchSrc_on_iff)
  apply (rule cspF_sym, rule cspF_Interleave_unit)

  apply (simp, rule+)
  apply (rule cspF_rw_left, rule cspF_decompo, simp, rule cspF_reflex, simp)
  apply (rule cspF_rw_left, rule cspF_Interleave_step)
  apply (rule cspF_decompo, simp)
  apply (simp)
  apply (elim disjE)
    apply (simp add: isBranchSrc_on_iff disjnt_domain)
      apply (rule cspF_rw_left, rule cspF_IF)+
      apply (rule cspF_decompo, simp, simp)
      apply (rule cspF_rw_right, assumption)
    apply (simp add: isBranchSrc_on_iff)
    apply (erule bexE)
      apply (simp add: isBranchSrc_on_iff non_member_imp_noteq disjnt_domain2)
      apply (rule cspF_rw_left, rule cspF_IF)+
      apply (rule cspF_Interleave_left_commute)
  done



lemma cspF_Inductive_interleave_f_g_to_Ext_pre_choice :
    "inj f ==> isBranchSrc g f ==>
     l \<noteq> [] ==> distinct l ==> disjnt_image_on f (set l) ==>
    ||| map (\<lambda>x. ? :(f x) -> PXf) l =F[M,M]
    ? x:\<Union> (f ` set l) -> (PXf x ||| ||| map (\<lambda>w. ? :(f w) -> PXf) (remove1 (g x) l) )"
  by (simp add: cspF_Inductive_interleave_f_g_to_Ext_pre_choice_lm)*)



lemma cspF_Inductive_interleave_f_g_to_Ext_pre_choice_lm :
    "inj_on f (set l) \<longrightarrow>
     l \<noteq> [] \<longrightarrow> distinct l \<longrightarrow> disjnt_image_on f (set l) \<longrightarrow>
    ||| map (\<lambda>x. ? :(f x) -> PXf) l =F[M,M]
    ? x:\<Union> (f ` set l) -> (PXf x ||| ( ||| map (\<lambda>w. ? :(f w) -> PXf) (remove1 (branchSrc_on f (set l) x) l) ) )"
  apply (induct_tac l)
  apply (rule, simp)
  apply (rule, rule, rule, rule)

  apply (case_tac "list = []")

  apply (simp)
  apply (rule cspF_rw_left, rule cspF_Interleave_unit)
  apply (rule cspF_decompo, simp)
  apply (simp add: branchSrc_on_singleton_iff)
  apply (rule cspF_sym, rule cspF_Interleave_unit)

  apply (rule cspF_rw_left, simp (no_asm))
    apply (rule cspF_decompo, simp, rule cspF_reflex, simp)
    apply (rule cspF_rw_left, rule cspF_Interleave_step)

  apply (rule cspF_decompo, simp)

  apply (simp only: UN_iff set_simps, elim bexE)
  apply (simp add: disjnt_domain branchSrc_on_iff)
  apply (elim disjE conjE, simp add: disjnt_domain)
      apply (rule cspF_rw_left, rule cspF_IF)+
      apply (rule cspF_decompo, simp, simp)
      apply (rule cspF_rw_right, assumption)
      apply (simp)
  apply (simp add: disjnt_domain2)
  apply (rule, rule, force)
      apply (simp add: branchSrc_on_iff disjnt_domain2)
      apply (simp add: isBranchSrc_on_iff non_member_imp_noteq disjnt_domain2)
      apply (rule cspF_rw_left, rule cspF_IF)+
      apply (rule cspF_Interleave_left_commute)
  done

lemma cspF_Inductive_interleave_f_g_to_Ext_pre_choice :
    "inj_on f (set l) ==>
     l \<noteq> [] ==> distinct l ==> disjnt_image_on f (set l) ==>
    ||| map (\<lambda>x. ? :(f x) -> PXf) l =F[M,M]
    ? x:\<Union> (f ` set l) -> (PXf x ||| ||| map (\<lambda>w. ? :(f w) -> PXf) (remove1 (branchSrc_on f (set l) x) l) )"
  by (simp add: cspF_Inductive_interleave_f_g_to_Ext_pre_choice_lm)


(*
lemma cspF_Rep_interleaving_f_g_to_Ext_pre_choice :
    "inj f ==> isBranchSrc g f ==>
     l \<noteq> [] ==> distinct l ==> disjnt_image_on f (set l) ==>
    ||| :l .. (\<lambda>x. ? :(f x) -> PXf) =F[M,M]
    ? x:\<Union> (f ` set l) -> (PXf x ||| ( ||| w:(remove1 (g x) l) .. ? :(f w) -> PXf ) )"
  by (simp add: Rep_interleaving_def cspF_Inductive_interleave_f_g_to_Ext_pre_choice)

lemma cspF_Rep_interleaving_fpair_g_to_Ext_pre_choice :
    "inj f ==> isBranchSrc g f ==>
     l \<noteq> [] ==> distinct l ==> disjnt_image_on f (set l) ==>
    ||| (x,y):l .. ? :(f (x,y)) -> PXf =F[M,M]
    ? x:\<Union> (f ` set l) -> (PXf x ||| ( ||| w:(remove1 (g x) l) .. ? :(f w) -> PXf) )"
  by (simp add: Rep_interleaving_def cspF_Inductive_interleave_f_g_to_Ext_pre_choice)
*)
lemma cspF_Rep_interleaving_f_g_to_Ext_pre_choice :
    "inj_on f (set l) ==>
     l \<noteq> [] ==> distinct l ==> disjnt_image_on f (set l) ==>
    ||| :l .. (\<lambda>x. ? :(f x) -> PXf) =F[M,M]
    ? x:\<Union> (f ` set l) -> (PXf x ||| ( ||| w:(remove1 (branchSrc_on f (set l) x) l) .. ? :(f w) -> PXf ) )"
  apply (simp only: Rep_interleaving_def)
  by (rule cspF_Inductive_interleave_f_g_to_Ext_pre_choice, simp_all)

lemma cspF_Rep_interleaving_fpair_g_to_Ext_pre_choice :
    "inj_on f (set l) ==>
     l \<noteq> [] ==> distinct l ==> disjnt_image_on f (set l) ==>
    ||| (x,y):l .. ? :(f (x,y)) -> PXf =F[M,M]
    ? x:\<Union> (f ` set l) -> (PXf x ||| ( ||| w:(remove1 (branchSrc_on f (set l) x) l) .. ? :(f w) -> PXf) )"
  apply (simp only: Rep_interleaving_def case_prod_unfold)
  apply (rule cspF_rw_left, rule cspF_Inductive_interleave_f_g_to_Ext_pre_choice)
  by (simp_all)


(*lemma cspF_Inductive_interleave_f_to_Ext_pre_choice :
    "inj f ==> l \<noteq> [] ==> distinct l ==>
    ||| map (\<lambda>x. ? :{f x} -> PXf) l =F[M,M]
    ? x:(f ` set l) -> (PXf x ||| ||| map (\<lambda>w. ? :{f w} -> PXf) (remove1 (inv f x) l) )"
  apply (rule cspF_rw_left)
  apply (rule cspF_Inductive_interleave_f_g_to_Ext_pre_choice[of _ "inv f"], simp_all add: inj_def)
  apply (simp add: isBranchSrc_on_def inv_def, force)
  apply (force)
  apply (rule cspF_decompo, simp_all add: image_def Union_eq)
  by (force)

lemma cspF_Rep_interleaving_f_to_Ext_pre_choice :
    "inj f ==> l \<noteq> [] ==> distinct l ==>
    ||| :l .. ( \<lambda>x. ? :{f x} -> PXf) =F[M,M]
    ? x:(f ` set l) -> (PXf x ||| ( ||| w:(remove1 (inv f x) l) .. ? :{f w} -> PXf ))"
  by (simp add: Rep_interleaving_def cspF_Inductive_interleave_f_to_Ext_pre_choice)*)

lemma cspF_Inductive_interleave_f_to_Ext_pre_choice :
    "inj_on f (set l) ==> l \<noteq> [] ==> distinct l ==>
    ||| map (\<lambda>x. ? :{f x} -> PXf) l =F[M,M]
    ? x:(f ` set l) -> (PXf x ||| ||| map (\<lambda>w. ? :{f w} -> PXf) (remove1 (inv_into (set l) f x) l) )"
  apply (rule cspF_rw_left)
  apply (rule cspF_Inductive_interleave_f_g_to_Ext_pre_choice)
  apply (rule inj_onI, simp add: inj_onD)
  apply (simp)
  apply (simp)
  apply (simp add: disjnt_iff inj_on_def, rule, rule, rule, force)

  apply (rule cspF_decompo, simp_all add: image_def Union_eq, force)
  apply (rule cspF_decompo, simp, simp)
  apply (simp add: branchSrc_on_def)

  apply (rule cspF_Inductive_interleave_cong)
  apply (rule map_cong)
  apply (rule_tac f=remove1 in arg_cong2)
  apply (rule the_equality, rule, elim bexE)

  apply (simp, elim bexE)
  apply (simp)
  apply (simp)
  apply (simp)
  by (simp)


lemma cspF_Rep_interleaving_f_to_Ext_pre_choice :
    "inj_on f (set l) ==> l \<noteq> [] ==> distinct l ==>
    ||| :l .. ( \<lambda>x. ? :{f x} -> PXf) =F[M,M]
    ? x:(f ` set l) -> (PXf x ||| ( ||| w:(remove1 (inv_into (set l) f x) l) .. ? :{f w} -> PXf ))"
  by (simp add: Rep_interleaving_def cspF_Inductive_interleave_f_to_Ext_pre_choice)



lemma cspF_Inductive_interleave_to_Ext_pre_choice :
    "l \<noteq> [] ==> distinct l ==>
    ||| map (\<lambda>x. ? a:{x} -> PXf a) l =F[M,M]
    ? x:(set l) -> (PXf x ||| ||| map (\<lambda>w. ? a:{w} -> PXf a) (remove1 x l) )"
  apply (rule cspF_rw_left, rule cspF_Inductive_interleave_f_to_Ext_pre_choice, simp_all)
  apply (rule cspF_decompo, simp)
  apply (rule cspF_decompo, simp, simp)

  apply (rule cspF_Inductive_interleave_cong)
  apply (rule map_cong)
  apply (rule_tac f=remove1 in arg_cong2)
  apply (simp add: inv_into_def)
  apply (rule someI2_ex, simp, simp)
  by (simp, simp)


lemma cspF_Rep_interleaving_to_Ext_pre_choice :
    "l \<noteq> [] ==> distinct l ==>
    ||| :l .. ( \<lambda>x. ? a:{x} -> PXf a) =F[M,M]
    ? x:(set l) -> (PXf x ||| ( ||| w:(remove1 x l) .. ? v:{w} -> PXf v ))"
  by (simp add: Rep_interleaving_def cspF_Inductive_interleave_to_Ext_pre_choice)



subsection \<open> Synchro SKIP Inductive interleave \<close>


lemma cspF_Synchro_Inductive_interleave_SKIP_lm :
     "(ALL P : set l . P =F[M,M] SKIP || P) -->
     SKIP || ( ||| l ) =F[M,M] ||| l"
  apply (induct_tac l)
   apply (simp)
    apply (rule cspF_Parallel_term)
   apply (simp)
    apply (rule)
    apply (elim conjE, simp)
    apply (rule cspF_rw_left, rule cspF_Synchro_SKIP_Interleave_dist)
    apply (rule cspF_decompo, simp)
    by (simp_all add: cspF_sym)

lemma cspF_Synchro_Inductive_interleave_SKIP_l :
     "ALL P : set l . P =F[M,M] SKIP || P ==>
     SKIP || ( ||| l ) =F[M,M] ||| l"
  by (simp add: cspF_Synchro_Inductive_interleave_SKIP_lm)


lemma cspF_Synchro_Inductive_interleave_SKIP_r :
     "ALL P : set l . P =F[M,M] SKIP || P ==>
     ( ||| l ) || SKIP =F[M,M] ||| l"
  apply (rule cspF_rw_left, rule cspF_Parallel_commut)
  by (rule cspF_Synchro_Inductive_interleave_SKIP_l)


lemmas cspF_Synchro_Inductive_interleave_SKIP = cspF_Synchro_Inductive_interleave_SKIP_l
                                                cspF_Synchro_Inductive_interleave_SKIP_r


end