           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021               |
            |                  2022 / 2023 (modified)   |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_law_DFkev
imports DFP_DFkev
begin



subsection \<open> DFkEvTick \<close>


lemma cspF_kev_0_eqF_SKIP : "$DFkEvTick 0 =F SKIP"
  by (cspF_auto)

lemma cspF_kev_k_unwind : "k > 0 \<Longrightarrow> $DFkEvTick k =F ! x -> $DFkEvTick (k-1)"
  apply (cspF_auto, induct k, simp)
  by (cspF_step)

lemmas cspF_kev_unwind = cspF_kev_0_eqF_SKIP cspF_kev_k_unwind


lemma cspF_kev_0_refF_SKIP : "$DFkEvTick 0 <=F SKIP"
  by (cspF_auto)


lemma cspF_kev_0_Seq_compo : "$DFkEvTick 0 ;; P =F P"
  by (cspF_auto)

lemma cspF_kev_0_Seq_compo_iff : "k = 0 \<Longrightarrow> $DFkEvTick k ;; P =F P"
  by (cspF_auto)

lemma cspF_kev_Suc_k_Seq_compo : "$DFkEvTick (Suc k) ;; P =F ! x -> ($DFkEvTick (k) ;; P)"
  apply (rule cspF_rw_left, rule cspF_decompo)
    apply (rule cspF_kev_unwind, simp)
    apply (rule cspF_reflex)
  by (cspF_auto)+

lemma cspF_kev_Suc_0_Seq_compo : "$DFkEvTick (Suc 0) ;; P =F ! x -> P"
  apply (rule cspF_rw_left, rule cspF_kev_Suc_k_Seq_compo)
  apply (rule cspF_Int_pre_choice_cong, simp)
  by (rule cspF_kev_0_Seq_compo)


lemma cspF_kev_k_Seq_compo : "k > 0 \<Longrightarrow> $DFkEvTick k ;; P =F ! x -> ($DFkEvTick (k-1) ;; P)"
  apply (rule cspF_rw_left, rule cspF_decompo)
    apply (rule cspF_kev_unwind, simp)
    apply (rule cspF_reflex)
  by (cspF_auto)+

lemmas cspF_kev_Seq_compo = cspF_kev_0_Seq_compo
                            cspF_kev_0_Seq_compo_iff
                            cspF_kev_Suc_0_Seq_compo
                            cspF_kev_Suc_k_Seq_compo
                            cspF_kev_k_Seq_compo



lemma cspF_kev_kev : "$DFkEvTick i ;; $DFkEvTick j =F $DFkEvTick (i+j)"
  apply (induct i, simp)
  by (cspF_auto)+

lemma cspF_kev_kev_P : "$DFkEvTick i ;; $DFkEvTick j ;; P =F $DFkEvTick (i+j) ;; P"
  apply (induct i, simp)
  by (cspF_auto)+



lemma cspF_kev_k_Seq_compo_Int_pre_choice : "$DFkEvTick k ;; ! x -> P =F $DFkEvTick (k+1) ;; P"
  apply (induct k, simp)
  apply (cspF_auto)+
  apply (rule cspF_decompo, simp)
  apply (rule cspF_decompo, simp)
  apply (cspF_auto)+
  done





subsection \<open> Inductive_ext_choice and Rep_ext_choice \<close>

lemma kev_1_Seq_compo_ref_Inductive_ext_choice_lm :
    "FPmode \<noteq> CPOmode \<Longrightarrow> l \<noteq> [] \<longrightarrow> (\<forall>a\<in> set l. ! x:UNIV -> D <=F PXf a) \<longrightarrow>
     $DFkEvTick (Suc 0);; D <=F [+] map PXf l"
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
     $DFkEvTick (Suc 0);; D <=F [+] map PXf l"
  by (simp add: kev_1_Seq_compo_ref_Inductive_ext_choice_lm)


lemma kev_1_Seq_compo_ref_Rep_ext_choice :
    "FPmode \<noteq> CPOmode \<Longrightarrow> L \<noteq> [] \<Longrightarrow> \<forall>a\<in> set L. ! x:UNIV -> D <=F PXf a \<Longrightarrow>
     $DFkEvTick (Suc 0);; D <=F [+] :L .. PXf"
  apply (simp add: Rep_ext_choice_def)
  by (rule kev_1_Seq_compo_ref_Inductive_ext_choice, simp_all)


lemma nat_eq_1_add_nat_minus_1 : "(n::nat) > 0 \<Longrightarrow> n = 1 + (n - 1)"
  by (induct n, simp_all)


lemma kev_Rep_ext_choice :
    "FPmode \<noteq> CPOmode \<Longrightarrow> n > 0 \<Longrightarrow>
     L \<noteq> [] \<Longrightarrow> \<forall>a\<in> set L. ! x:UNIV -> $DFkEvTick (n-1) <=F PXf a \<Longrightarrow>
     $DFkEvTick (n) <=F [+] :L .. PXf"
  apply (induct n, simp)
  apply (subst nat_eq_1_add_nat_minus_1, simp)
    apply (rule cspF_rw_left, rule cspF_kev_kev[THEN cspF_sym])
  apply (simp)
  by (rule kev_1_Seq_compo_ref_Rep_ext_choice, simp_all)


lemma kev_n_Seq_compo_ref_Rep_ext_choice :
    "FPmode \<noteq> CPOmode \<Longrightarrow> n > 0 \<Longrightarrow>
     L \<noteq> [] \<Longrightarrow> \<forall>a\<in> set L. ! x:UNIV -> ($DFkEvTick (n-1) ;; D) <=F PXf a \<Longrightarrow>
     $DFkEvTick (n) ;; D <=F [+] :L .. PXf"
  apply (induct n, simp)
  apply (subst nat_eq_1_add_nat_minus_1, simp)
  apply (rule cspF_rw_left, rule cspF_decompo)
    apply (rule cspF_kev_kev[THEN cspF_sym])
    apply (rule cspF_reflex)
  apply (rule cspF_rw_left, rule cspF_Seq_compo_assoc)
  apply (simp)
  by (rule kev_1_Seq_compo_ref_Rep_ext_choice, simp_all)





subsection \<open> DFkEv \<close>

lemma cspF_DFkev_0_i_eqF_DIV : "$DFkEv 0 i =F DIV"
  by (cspF_auto)

lemma cspF_DFkev_k_0_eqF_DIV : "$DFkEv k 0 =F DIV"
  by (cspF_auto, induct k, simp_all)

lemma cspF_DFkev_k_less_i_eqF_DIV : "i > k \<Longrightarrow> $DFkEv k i =F DIV"
  apply (cspF_auto, induct k, simp)
  by (induct i, simp_all)

lemma cspF_DFkev_k_i_unwind : "k \<ge> i \<Longrightarrow> i > 1 \<Longrightarrow> $DFkEv k i =F ! x -> $DFkEv k (i-1)"
  apply (cspF_auto_left, induct k)
   apply (simp)
   apply (case_tac i)
   by (simp_all)

lemma cspF_DFkev_k_1_restarts : "k > 0 \<Longrightarrow> $DFkEv k (Suc 0) =F ! x -> $DFkEv k k"
  by (cspF_auto_left, induct k, simp_all)

lemmas cspF_DFkev_DIV = cspF_DFkev_0_i_eqF_DIV
                        cspF_DFkev_k_0_eqF_DIV
                        cspF_DFkev_k_less_i_eqF_DIV

lemmas cspF_DFkev_unwind = cspF_DFkev_k_1_restarts
                           cspF_DFkev_k_i_unwind
                           cspF_DFkev_DIV


subsection \<open> DFkEv k k simplifications \<close>

lemma DFkev_0_0_unwind : "$DFkEv 0 0 =F DIV"
  by (rule cspF_DFkev_unwind)

lemma DFkev_1_1_unwind : "$DFkEv (Suc 0) (Suc 0) =F ! x -> $DFkEv (Suc 0) (Suc 0)"
  by (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)

lemma DFkev_2_2_unwind : "$DFkEv 2 2 =F ! x -> ! x -> $DFkEv 2 2"
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  by (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)

lemma DFkev_3_3_unwind : "$DFkEv 3 3 =F ! x -> ! x -> ! x -> $DFkEv 3 3"
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  by (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)

lemma DFkev_4_4_unwind : "$DFkEv 4 4 =F ! x -> ! x -> ! x -> ! x -> $DFkEv 4 4"
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  by (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)

lemma DFkev_5_5_unwind : "$DFkEv 5 5 =F ! x -> ! x -> ! x -> ! x -> ! x -> $DFkEv 5 5"
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
lemma test_DFkev_5_5_eqF_DFkev_4_4 : "$DFkEv 5 5 =F $DFkEv 4 4"
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




subsection \<open> kEvTick \<close>

lemma cspF_kEvTick_0_eqF_SKIP : "$kEvTick 0 =F SKIP"
  by (cspF_auto)

lemma cspF_kEvTick_k_unwind : "k > 0 \<Longrightarrow> $kEvTick k =F ! x -> $kEvTick (k-1)"
  apply (cspF_auto, induct k, simp)
  by (cspF_step)

lemmas cspF_kEvTick_unwind = cspF_kEvTick_0_eqF_SKIP cspF_kEvTick_k_unwind


lemma cspF_kEvTick_0_Seq_compo : "$kEvTick 0 ;; P =F P"
  by (cspF_auto)

lemma cspF_kEvTick_k_Seq_compo : "k > 0 \<Longrightarrow> $kEvTick k ;; P =F ! x -> ($kEvTick (k-1) ;; P)"
  apply (rule cspF_rw_left, rule cspF_decompo)
    apply (rule cspF_kEvTick_unwind, simp)
    apply (rule cspF_reflex)
  by (cspF_auto)+

lemma cspF_kEvTick_Suc_0_Seq_compo : "$kEvTick (Suc 0) ;; P =F ! x -> P"
  apply (rule cspF_rw_left, rule cspF_kEvTick_k_Seq_compo, simp_all)
  apply (cspF_auto)+
  apply (rule cspF_decompo, simp)+
  by (rule cspF_kEvTick_0_Seq_compo)

lemmas cspF_kEvTick_Seq_compo = cspF_kEvTick_0_Seq_compo cspF_kEvTick_Suc_0_Seq_compo cspF_kEvTick_k_Seq_compo



lemma cspF_kEvTick_kEvTick : "$kEvTick i ;; $kEvTick j =F $kEvTick (i+j)"
  apply (induct i, simp)
  by (cspF_auto)+

lemma cspF_kEvTick_kEvTick_P : "$kEvTick i ;; $kEvTick j ;; P =F $kEvTick (i+j) ;; P"
  apply (induct i, simp)
  by (cspF_auto)+



lemma cspF_kEvTick_k_Seq_compo_Int_pre_choice : "$kEvTick k ;; ! x -> P =F $kEvTick (k+1) ;; P"
  apply (induct k, simp)
  apply (cspF_auto)+
  apply (rule cspF_decompo, simp)
  apply (rule cspF_decompo, simp)
  apply (cspF_auto)+
  done



subsection \<open> kEvRec \<close>

lemma cspF_kEvRec_0_i_eqF_DIV : "$kEvRec 0 i =F DIV"
  by (cspF_auto)

lemma cspF_kEvRec_k_0_eqF_DIV : "$kEvRec k 0 =F DIV"
  by (cspF_auto, induct k, simp_all)

lemma cspF_kEvRec_k_less_i_eqF_DIV : "i > k \<Longrightarrow> $kEvRec k i =F DIV"
  apply (cspF_auto, induct k, simp)
  by (induct i, simp_all)

lemma cspF_kEvRec_k_i_unwind : "k \<ge> i \<Longrightarrow> i > 1 \<Longrightarrow> $kEvRec k i =F ! x -> $kEvRec k (i-1)"
  apply (cspF_auto_left, induct k)
   apply (simp)
   apply (case_tac i)
   by (simp_all)

lemma cspF_kEvRec_k_1_restarts : "k > 0 \<Longrightarrow> $kEvRec k (Suc 0) =F ! x -> $kEvRec k k"
  by (cspF_auto_left, induct k, simp_all)

lemmas cspF_kEvRec_DIV = cspF_kEvRec_0_i_eqF_DIV
                        cspF_kEvRec_k_0_eqF_DIV
                        cspF_kEvRec_k_less_i_eqF_DIV

lemmas cspF_kEvRec_unwind = cspF_kEvRec_k_1_restarts
                           cspF_kEvRec_k_i_unwind
                           cspF_kEvRec_DIV


lemma kEvRec_k_i_lm :
    "k > i \<Longrightarrow> k > 0 \<and> 0 < i \<longrightarrow>
     $kEvRec (k) (i) =F $kEvTick (i) ;; $kEvRec (k) (k)"
  apply (induction i arbitrary: k)

  (* i = 0 *)
  apply (rule)
    apply (rule cspF_rw_right, rule cspF_kEvTick_Seq_compo, simp)

  (* i > 0 *)
  apply (rule)

   apply (case_tac "Suc i \<le> k", simp)

   apply (case_tac "i > 0")
    apply (rule cspF_rw_left, rule cspF_kEvRec_unwind, simp, simp)
    apply (rule cspF_rw_right, rule cspF_kEvTick_Seq_compo, simp, simp)
    apply (cspF_step)
    apply (rule cspF_rw_left, rule cspF_kEvRec_unwind, simp)
    apply (rule cspF_rw_right, rule cspF_kEvTick_Seq_compo, simp)
  done

lemma kEvRec_k_i :
    "k > i \<Longrightarrow> k > 0 \<and> 0 < i \<Longrightarrow>
     $kEvRec (k) (i) =F $kEvTick (i) ;; $kEvRec (k) (k)"
  by (simp add: kEvRec_k_i_lm)

lemma kEvRec_k_add_i_i :
    "0 < k \<Longrightarrow> 0 < i \<Longrightarrow>
     $kEvRec (k + i) (i) =F $kEvTick (i) ;; $kEvRec (k + i) (k + i)"
  by (rule kEvRec_k_i, simp, simp)




end