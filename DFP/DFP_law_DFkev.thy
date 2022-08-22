           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021               |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_law_DFkev
imports DFP_DFkev DFP_law_DFnonTick
begin





subsection \<open> kev \<close>


lemma cspF_kev_0_eqF_SKIP : "$kev 0 =F SKIP"
  by (cspF_auto)

lemma cspF_kev_k_unwind : "k > 0 \<Longrightarrow> $kev k =F ! x -> $kev (k-1)"
  apply (cspF_auto, induct k, simp)
  by (cspF_step)

lemmas cspF_kev_unwind = cspF_kev_0_eqF_SKIP cspF_kev_k_unwind


lemma cspF_kev_0_refF_SKIP : "$kev 0 <=F SKIP"
  by (cspF_auto)


lemma cspF_kev_0_Seq_compo : "$kev 0 ;; P =F P"
  by (cspF_auto)

lemma cspF_kev_0_Seq_compo_iff : "k = 0 \<Longrightarrow> $kev k ;; P =F P"
  by (cspF_auto)

lemma cspF_kev_Suc_k_Seq_compo : "$kev (Suc k) ;; P =F ! x -> ($kev (k) ;; P)"
  apply (rule cspF_rw_left, rule cspF_decompo)
    apply (rule cspF_kev_unwind, simp)
    apply (rule cspF_reflex)
  by (cspF_auto)+

lemma cspF_kev_Suc_0_Seq_compo : "$kev (Suc 0) ;; P =F ! x -> P"
  apply (rule cspF_rw_left, rule cspF_kev_Suc_k_Seq_compo)
  apply (rule cspF_Int_pre_choice_cong, simp)
  by (rule cspF_kev_0_Seq_compo)


lemma cspF_kev_k_Seq_compo : "k > 0 \<Longrightarrow> $kev k ;; P =F ! x -> ($kev (k-1) ;; P)"
  apply (rule cspF_rw_left, rule cspF_decompo)
    apply (rule cspF_kev_unwind, simp)
    apply (rule cspF_reflex)
  by (cspF_auto)+

lemmas cspF_kev_Seq_compo = cspF_kev_0_Seq_compo
                            cspF_kev_0_Seq_compo_iff
                            cspF_kev_Suc_0_Seq_compo
                            cspF_kev_Suc_k_Seq_compo
                            cspF_kev_k_Seq_compo



lemma cspF_kev_kev : "$kev i ;; $kev j =F $kev (i+j)"
  apply (induct i, simp)
  by (cspF_auto)+

lemma cspF_kev_kev_P : "$kev i ;; $kev j ;; P =F $kev (i+j) ;; P"
  apply (induct i, simp)
  by (cspF_auto)+



lemma cspF_kev_k_Seq_compo_Int_pre_choice : "$kev k ;; ! x -> P =F $kev (k+1) ;; P"
  apply (induct k, simp)
  apply (cspF_auto)+
  apply (rule cspF_decompo, simp)
  apply (rule cspF_decompo, simp)
  apply (cspF_auto)+
  done





subsection \<open> Inductive_ext_choice and Rep_ext_choice \<close>

lemma kev_1_Seq_compo_ref_Inductive_ext_choice_lm :
    "FPmode \<noteq> CPOmode \<Longrightarrow> l \<noteq> [] \<longrightarrow> (\<forall>a\<in> set l. ! x:UNIV -> D <=F PXf a) \<longrightarrow>
     $kev (Suc 0);; D <=F [+] map PXf l"
  apply (induct_tac l)
  apply (simp)
  apply (rule, rule)
  apply (cspF_simp)
  apply (case_tac list, simp)
  apply (rule cspF_rw_left, rule cspF_kev_Suc_0_Seq_compo)
  apply (rule cspF_rw_right, rule cspF_Ext_choice_unit, simp)

  apply (rule cspF_rw_left, rule cspF_kev_Suc_0_Seq_compo)
  apply (rule cspF_Ext_choice_right)
  apply (simp)
  apply (simp)
  apply (erule cspF_rw_left_refE_MF, rule cspF_kev_Suc_0_Seq_compo)
  apply (simp)
done


lemma kev_1_Seq_compo_ref_Inductive_ext_choice :
    "FPmode \<noteq> CPOmode \<Longrightarrow> l \<noteq> [] \<Longrightarrow> (\<forall>a\<in> set l. ! x:UNIV -> D <=F PXf a) \<Longrightarrow>
     $kev (Suc 0);; D <=F [+] map PXf l"
  by (simp add: kev_1_Seq_compo_ref_Inductive_ext_choice_lm)


lemma kev_1_Seq_compo_ref_Rep_ext_choice :
    "FPmode \<noteq> CPOmode \<Longrightarrow> L \<noteq> [] \<Longrightarrow> \<forall>a\<in> set L. ! x:UNIV -> D <=F PXf a \<Longrightarrow>
     $kev (Suc 0);; D <=F [+] :L .. PXf"
  apply (simp add: Rep_ext_choice_def)
  by (rule kev_1_Seq_compo_ref_Inductive_ext_choice, simp_all)


lemma nat_eq_1_add_nat_minus_1 : "(n::nat) > 0 \<Longrightarrow> n = 1 + (n - 1)"
  by (induct n, simp_all)


lemma kev_Rep_ext_choice :
    "FPmode \<noteq> CPOmode \<Longrightarrow> n > 0 \<Longrightarrow>
     L \<noteq> [] \<Longrightarrow> \<forall>a\<in> set L. ! x:UNIV -> $kev (n-1) <=F PXf a \<Longrightarrow>
     $kev (n) <=F [+] :L .. PXf"
  apply (induct n, simp)
  apply (subst nat_eq_1_add_nat_minus_1, simp)
    apply (rule cspF_rw_left, rule cspF_kev_kev[THEN cspF_sym])
  apply (simp)
  by (rule kev_1_Seq_compo_ref_Rep_ext_choice, simp_all)


lemma kev_n_Seq_compo_ref_Rep_ext_choice :
    "FPmode \<noteq> CPOmode \<Longrightarrow> n > 0 \<Longrightarrow>
     L \<noteq> [] \<Longrightarrow> \<forall>a\<in> set L. ! x:UNIV -> ($kev (n-1) ;; D) <=F PXf a \<Longrightarrow>
     $kev (n) ;; D <=F [+] :L .. PXf"
  apply (induct n, simp)
  apply (subst nat_eq_1_add_nat_minus_1, simp)
  apply (rule cspF_rw_left, rule cspF_decompo)
    apply (rule cspF_kev_kev[THEN cspF_sym])
    apply (rule cspF_reflex)
  apply (rule cspF_rw_left, rule cspF_Seq_compo_assoc)
  apply (simp)
  by (rule kev_1_Seq_compo_ref_Rep_ext_choice, simp_all)





subsection \<open> DFkev \<close>

lemma cspF_DFkev_0_i_eqF_DIV : "$DFkev 0 i =F DIV"
  by (cspF_auto)

lemma cspF_DFkev_k_0_eqF_DIV : "$DFkev k 0 =F DIV"
  by (cspF_auto, induct k, simp_all)

lemma cspF_DFkev_k_less_i_eqF_DIV : "i > k \<Longrightarrow> $DFkev k i =F DIV"
  apply (cspF_auto, induct k, simp)
  by (induct i, simp_all)

lemma cspF_DFkev_k_i_unwind : "k \<ge> i \<Longrightarrow> i > 1 \<Longrightarrow> $DFkev k i =F ! x -> $DFkev k (i-1)"
  apply (cspF_auto_left, induct k)
   apply (simp)
   apply (case_tac i)
   by (simp_all)

lemma cspF_DFkev_k_1_restarts : "k > 0 \<Longrightarrow> $DFkev k (Suc 0) =F ! x -> $DFkev k k"
  by (cspF_auto_left, induct k, simp_all)

lemmas cspF_DFkev_DIV = cspF_DFkev_0_i_eqF_DIV
                        cspF_DFkev_k_0_eqF_DIV
                        cspF_DFkev_k_less_i_eqF_DIV

lemmas cspF_DFkev_unwind = cspF_DFkev_k_1_restarts
                           cspF_DFkev_k_i_unwind
                           cspF_DFkev_DIV


subsection \<open> DFkev k k simplifications \<close>

lemma DFkev_0_0_unwind : "$DFkev 0 0 =F DIV"
  by (rule cspF_DFkev_unwind)

lemma DFkev_1_1_unwind : "$DFkev (Suc 0) (Suc 0) =F ! x -> $DFkev (Suc 0) (Suc 0)"
  by (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)

lemma DFkev_2_2_unwind : "$DFkev 2 2 =F ! x -> ! x -> $DFkev 2 2"
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  by (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)

lemma DFkev_3_3_unwind : "$DFkev 3 3 =F ! x -> ! x -> ! x -> $DFkev 3 3"
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  by (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)

lemma DFkev_4_4_unwind : "$DFkev 4 4 =F ! x -> ! x -> ! x -> ! x -> $DFkev 4 4"
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  by (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)

lemma DFkev_5_5_unwind : "$DFkev 5 5 =F ! x -> ! x -> ! x -> ! x -> ! x -> $DFkev 5 5"
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  by (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)







(* TESTING...
lemma test_DFkev_5_5_eqF_DFkev_4_4 : "$DFkev 5 5 =F $DFkev 4 4"
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all) (* 4 restarts *)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all) (* 5 restarts *)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all) (* 4 restarts *)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all) (* 5 restarts *)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all) (* 4 restarts *)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all) (* 5 restarts *)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all) (* 4 restarts *)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all) (* 5 restarts *)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all) (* 4 restarts *)
  apply (cspF_step, rule cspF_decompo, simp)+
  oops*)
  (* OOPS - THIS IS ONLY A TEST! *)




subsection \<open> kevT \<close>

lemma cspF_kevT_0_eqF_SKIP : "$kevT 0 =F SKIP"
  by (cspF_auto)

lemma cspF_kevT_k_unwind : "k > 0 \<Longrightarrow> $kevT k =F ! x -> $kevT (k-1)"
  apply (cspF_auto, induct k, simp)
  by (cspF_step)

lemmas cspF_kevT_unwind = cspF_kevT_0_eqF_SKIP cspF_kevT_k_unwind


lemma cspF_kevT_0_Seq_compo : "$kevT 0 ;; P =F P"
  by (cspF_auto)

lemma cspF_kevT_k_Seq_compo : "k > 0 \<Longrightarrow> $kevT k ;; P =F ! x -> ($kevT (k-1) ;; P)"
  apply (rule cspF_rw_left, rule cspF_decompo)
    apply (rule cspF_kevT_unwind, simp)
    apply (rule cspF_reflex)
  by (cspF_auto)+

lemma cspF_kevT_Suc_0_Seq_compo : "$kevT (Suc 0) ;; P =F ! x -> P"
  apply (rule cspF_rw_left, rule cspF_kevT_k_Seq_compo, simp_all)
  apply (cspF_auto)+
  apply (rule cspF_decompo, simp)+
  by (rule cspF_kevT_0_Seq_compo)

lemmas cspF_kevT_Seq_compo = cspF_kevT_0_Seq_compo cspF_kevT_Suc_0_Seq_compo cspF_kevT_k_Seq_compo



lemma cspF_kevT_kevT : "$kevT i ;; $kevT j =F $kevT (i+j)"
  apply (induct i, simp)
  by (cspF_auto)+

lemma cspF_kevT_kevT_P : "$kevT i ;; $kevT j ;; P =F $kevT (i+j) ;; P"
  apply (induct i, simp)
  by (cspF_auto)+



lemma cspF_kevT_k_Seq_compo_Int_pre_choice : "$kevT k ;; ! x -> P =F $kevT (k+1) ;; P"
  apply (induct k, simp)
  apply (cspF_auto)+
  apply (rule cspF_decompo, simp)
  apply (rule cspF_decompo, simp)
  apply (cspF_auto)+
  done



subsection \<open> kevR \<close>

lemma cspF_kevR_0_i_eqF_DIV : "$kevR 0 i =F DIV"
  by (cspF_auto)

lemma cspF_kevR_k_0_eqF_DIV : "$kevR k 0 =F DIV"
  by (cspF_auto, induct k, simp_all)

lemma cspF_kevR_k_less_i_eqF_DIV : "i > k \<Longrightarrow> $kevR k i =F DIV"
  apply (cspF_auto, induct k, simp)
  by (induct i, simp_all)

lemma cspF_kevR_k_i_unwind : "k \<ge> i \<Longrightarrow> i > 1 \<Longrightarrow> $kevR k i =F ! x -> $kevR k (i-1)"
  apply (cspF_auto_left, induct k)
   apply (simp)
   apply (case_tac i)
   by (simp_all)

lemma cspF_kevR_k_1_restarts : "k > 0 \<Longrightarrow> $kevR k (Suc 0) =F ! x -> $kevR k k"
  by (cspF_auto_left, induct k, simp_all)

lemmas cspF_kevR_DIV = cspF_kevR_0_i_eqF_DIV
                        cspF_kevR_k_0_eqF_DIV
                        cspF_kevR_k_less_i_eqF_DIV

lemmas cspF_kevR_unwind = cspF_kevR_k_1_restarts
                           cspF_kevR_k_i_unwind
                           cspF_kevR_DIV


lemma kevR_k_i_lm :
    "k > i \<Longrightarrow> k > 0 \<and> 0 < i \<longrightarrow>
     $kevR (k) (i) =F $kevT (i) ;; $kevR (k) (k)"
  apply (induction i arbitrary: k)

  (* i = 0 *)
  apply (rule)
    apply (rule cspF_rw_right, rule cspF_kevT_Seq_compo, simp)

  (* i > 0 *)
  apply (rule)

   apply (case_tac "Suc i \<le> k", simp)

   apply (case_tac "i > 0")
    apply (rule cspF_rw_left, rule cspF_kevR_unwind, simp, simp)
    apply (rule cspF_rw_right, rule cspF_kevT_Seq_compo, simp, simp)
    apply (cspF_step)
    apply (rule cspF_rw_left, rule cspF_kevR_unwind, simp)
    apply (rule cspF_rw_right, rule cspF_kevT_Seq_compo, simp)
  done

lemma kevR_k_i :
    "k > i \<Longrightarrow> k > 0 \<and> 0 < i \<Longrightarrow>
     $kevR (k) (i) =F $kevT (i) ;; $kevR (k) (k)"
  by (simp add: kevR_k_i_lm)

lemma kevR_k_add_i_i :
    "0 < k \<Longrightarrow> 0 < i \<Longrightarrow>
     $kevR (k + i) (i) =F $kevT (i) ;; $kevR (k + i) (k + i)"
  by (rule kevR_k_i, simp, simp)




end