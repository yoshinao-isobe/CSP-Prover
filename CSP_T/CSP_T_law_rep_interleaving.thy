           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2020         |
            |                  March 2021               |
            |                                           |
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021  (modified)   |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory CSP_T_law_rep_interleaving
imports CSP_T_law_basic CSP_T_law_SKIP CSP_T_law_step
begin

subsection \<open> Inductive interleave \<close>

lemma cspT_Inductive_interleave_cong :
    "x = y ==> ||| x =T[M,M] ||| y"
  by (simp)

lemma cspT_Inductive_interleave_One [simp]:
    "||| [P] =T[M,M] P"
  by (simp, rule cspT_Interleave_unit)

lemma cspT_Inductive_interleaving_Cons_cong :
    "[| P =T[M1,M2] Q; ||| Ps =T[M1,M2] ||| Qs |] ==> ||| (P#Ps) =T[M1,M2] ||| (Q#Qs)"
  by (simp, rule cspT_decompo, simp)

lemma cspT_Inductive_interleave_map_cong :
    "ALL a:set x. PXf a =T[M1,M2] PXg a ==> ( ||| map PXf x) =T[M1,M2] ( ||| map PXg x)"
  apply (induct x, simp_all)
  by (rule cspT_decompo, simp_all)+

(*lemma cspT_Inductive_interleave_map_to_List :
    "map PXf x = l ==> ( ||| map PXf x) =T ( ||| l)"
  by (simp)

lemma cspT_Inductive_interleave_map_to_List_Cons :
    "l \<noteq> [] ==> ||| map PXf l =T ||| ( (PXf (hd l)) # map PXf (tl l) )"
  apply (rule cspT_Inductive_interleave_map_to_List)
  by (induct l, simp, simp add: map_def)*)

lemma cspT_Inductive_interleave_append :
    "||| (l @ l2) =T[M,M] ( ||| l) ||| ( ||| l2)"
  apply (induct_tac l)
  apply (simp, rule cspT_rw_right, rule cspT_Interleave_unit, simp)
  apply (simp, rule cspT_rw_right, rule cspT_Interleave_assoc[THEN cspT_sym])
  by (rule cspT_decompo, simp_all)


lemma cspT_Subst_procfun_Inductive_interleave_map :
   "ALL i:set l. (PXf i) << Pf =T[M1,M2] PXf i
    ==> ( ||| map PXf l) << Pf =T[M1,M2] ( ||| map PXf l)"
  apply (induct l, simp_all)
  by (rule cspT_decompo, simp_all)+



lemma cspT_Inductive_interleave_filter_map :
    "Q = (\<lambda>P. P \<noteq> SKIP) ==> ||| filter Q (map Pf l) =T[M,M] ||| map Pf l"
  apply (induct l, simp_all, rule, rule)
  apply (rule cspT_decompo, simp_all)
  by (rule, rule cspT_rw_right, rule cspT_Interleave_unit, simp)

lemma map_filter_2: "\<forall>x. Q x = (P \<circ> f) x ==> map f (filter (Q) xs) = filter P (map f xs)"
  by (induct xs) simp_all

lemma cspT_Inductive_interleave_map_enumerate_filtered :
    "!!n. ALL i Tin b. Pf(i,Tin,b) = SKIP \<longleftrightarrow> \<not> Q(i,Tin,b) ==>
    ||| map Pf (enumerate n T\<^sub>i\<^sub>n\<^sub>s) =T[M,M] ||| map Pf (filter Q (enumerate n T\<^sub>i\<^sub>n\<^sub>s))"
  apply (rule cspT_rw_right)
  apply (rule cspT_Inductive_interleave_cong)
  apply (rule_tac P="(\<lambda>P. (P \<noteq> SKIP))" in map_filter_2)
  apply (rule)
  apply (simp add: comp_def)
  apply (force)
  apply (rule cspT_Inductive_interleave_filter_map[THEN cspT_sym])
  by (force)


subsection \<open> Replicated interleaving \<close>

lemma cspT_Rep_interleaving_cong :
    "ALL x. PXf x =T[M1,M2] PXg x & X = Y ==> ||| :X .. PXf =T[M1,M2] ||| :Y .. PXg"
  by (simp add: Rep_interleaving_def cspT_Inductive_interleave_map_cong)

lemma cspT_Rep_interleaving_pair_cong :
    "ALL a b. PXf (a,b) =T[M1,M2] PXg (a,b) & X = Y ==> ||| :X .. PXf =T[M1,M2] ||| :Y .. PXg"
  by (simp add: cspT_Rep_interleaving_cong)


lemma cspT_Rep_interleaving_one [simp]:
    "||| :[x] .. Pf =T[M,M] Pf x"
  by (simp add: Rep_interleaving_def, rule cspT_Interleave_unit)

lemma cspT_Rep_interleaving_singleton [simp]:
    "||| :asList {x} .. Pf =T[M,M] Pf x"
  by (simp add: asList_def)

lemma cspT_Rep_interleaving_Cons :
    "( ||| :(a # list) .. PXf) =T[M,M] (PXf a ||| ( ||| :list .. PXf))"
  by (simp add: Rep_interleaving_def)


lemma cspT_Subst_procfun_Rep_interleaving :
   "ALL i:set l. (PXf i) << Pf =T[M1,M2] PXf i ==>
    ( ||| :l .. PXf) << Pf =T[M1,M2] ( ||| :l .. PXf)"
  apply (simp add: Rep_interleaving_def)
  by (rule cspT_Subst_procfun_Inductive_interleave_map, simp_all)



lemma cspT_Rep_interleaving_append :
    "( ||| :(list @ l2) .. PXf) =T[M,M] (( ||| :list .. PXf) ||| ( ||| :l2 .. PXf))"
  apply (simp add: Rep_interleaving_def)
  by (simp add: cspT_Inductive_interleave_append)




subsection \<open> Inductive_interleave to Ext_pre_choice \<close>



lemma non_member_imp_noteq : "a \<notin> S ==> x \<in> S ==> x \<noteq> a"
  by (fast)

lemma disjnt_domain :
    "a \<notin> S ==> y \<in> f a ==> \<forall>y\<in>S. a \<noteq> y --> disjnt (f a) (f y) ==> \<not> (\<exists>x\<in>S. y \<in> f x)"
  by (rule, simp add: disjnt_def Int_def, fast)


lemma cspT_Inductive_interleave_to_Ext_pre_choice_lm :
    "l \<noteq> [] --> distinct l -->
    ||| map (\<lambda>x. ? a:{x} -> PXf a) l =T[M,M]
    ? x:(set l) -> (PXf x ||| ||| map (\<lambda>x. ? a:{x} -> PXf a) (remove1 x l) )"
  apply (induct_tac l)
  apply (rule, simp)
  apply (rule, simp, rule)
  apply (elim conjE)

  apply (case_tac "list=[]")

  apply (simp)
  apply (rule cspT_rw_left, rule cspT_Interleave_unit)
  apply (rule cspT_decompo, simp)
  apply (simp)
  apply (rule cspT_sym, rule cspT_Interleave_unit)

  apply (simp)
  apply (rule cspT_rw_left, rule cspT_decompo, simp, rule cspT_reflex, simp)
  apply (rule cspT_rw_left, rule cspT_Parallel_step)
  apply (rule cspT_decompo, simp)
  apply (simp)
  apply (elim disjE)
    apply (simp)
      apply (rule cspT_rw_left, rule cspT_IF)+
      apply (rule cspT_decompo, simp, simp)
      apply (rule cspT_rw_right, assumption)
      apply (simp)
    apply (simp add: non_member_imp_noteq)
      apply (rule cspT_rw_left, rule cspT_IF)+
      apply (rule cspT_Interleave_left_commute)
  done



lemma cspT_Inductive_interleave_to_Ext_pre_choice :
    "l \<noteq> [] ==> distinct l ==>
    ||| map (\<lambda>x. ? a:{x} -> PXf a) l =T[M,M]
    ? x:(set l) -> (PXf x ||| ||| map (\<lambda>x. ? a:{x} -> PXf a) (remove1 x l) )"
  by (simp add: cspT_Inductive_interleave_to_Ext_pre_choice_lm)






subsection \<open> Synchro SKIP Inductive interleave \<close>


lemma cspT_Synchro_Inductive_interleave_SKIP_lm :
     "(ALL P : set l . P =T[M,M] SKIP || P) -->
     SKIP || ( ||| l ) =T[M,M] ||| l"
  apply (induct_tac l)
   apply (simp)
    apply (rule cspT_Parallel_term)
   apply (simp)
    apply (rule)
    apply (elim conjE, simp)
    apply (rule cspT_rw_left, rule cspT_Synchro_SKIP_Interleave_dist)
    apply (rule cspT_decompo, simp)
    by (simp add: cspT_sym)+

lemma cspT_Synchro_Inductive_interleave_SKIP_l :
     "ALL P : set l . P =T[M,M] SKIP || P ==>
     SKIP || ( ||| l ) =T[M,M] ||| l"
  by (simp add: cspT_Synchro_Inductive_interleave_SKIP_lm)


lemma cspT_Synchro_Inductive_interleave_SKIP_r :
     "ALL P : set l . P =T[M,M] SKIP || P ==>
     ( ||| l ) || SKIP =T[M,M] ||| l"
  apply (rule cspT_rw_left, rule cspT_Parallel_commut)
  apply (rule cspT_Synchro_Inductive_interleave_SKIP_l)
  by (simp)


lemmas cspT_Synchro_Inductive_interleave_SKIP = cspT_Synchro_Inductive_interleave_SKIP_l
                                                cspT_Synchro_Inductive_interleave_SKIP_r

end