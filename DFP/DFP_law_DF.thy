           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021               |
            |                  2022 / 2023 (modified)   |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_law_DF
imports DFP_DF
        DFP_DFtick
begin


section \<open> deadlock-free \<close>

fun DF_induct_Hypotheses :: "DFPN \<Rightarrow> (DFtickName, 'e) proc"
where
    "DF_induct_Hypotheses (DF') = $DFtick"

lemma Lemma_DFPN_To_DFtick :
    "DF_induct_Hypotheses p <=F (DFfun p) << DF_induct_Hypotheses"
by (induct_tac p, simp, cspF_unwind, rule cspF_Int_choice_left1, cspF_auto)

lemma dfp_DF': "($DFtick::(DFtickName, 'e) proc) <=F $DF'"
  apply (rule_tac Pf="DFfun" and f="DF_induct_Hypotheses" in cspF_fp_induct_ref_right)
  apply (simp, case_tac FPmode, simp_all)
  apply (rule Lemma_DFPN_To_DFtick)
done

lemma dfp_DF: "(($DFtick)::(DFtickName, 'e) proc) <=F (DF::(DFPN,'e) proc)"
by (simp add: DF_def dfp_DF')


lemma DF'_isDeadlockFree: "($DF':: (DFPN, 'e) proc) isDeadlockFree"
by (simp only: DeadlockFree_DFtick_ref, rule dfp_DF')

lemma DF_isDeadlockFree: "(DF:: (DFPN, 'e) proc) isDeadlockFree"
by (simp only: DF_def DF'_isDeadlockFree)


lemma DF'_DeadlockFree:
    "($DF':: (DFPN, 'e) proc) <=F P ==> P isDeadlockFree"
  apply (insert DF'_isDeadlockFree)
  apply (simp add: DeadlockFree_def)
  apply (simp add: cspF_refF_semantics)
  apply (auto)
done

lemma DF_DeadlockFree:
    "(DF:: (DFPN, 'e) proc) <=F P ==> P isDeadlockFree"
by (simp add: DF_def DF'_DeadlockFree)





section \<open> deadlock-free non-terminating (dfnt) \<close>


subsection \<open> STOP \<close>


lemma not_isNonTickDeadlockFree_STOP : "\<not> STOP isNonTickDeadlockFree"
  apply (simp add: NonTickDeadlockFree_def)
  by (simp add: in_failures)


lemma not_dfpnt_STOP : "\<not> $DF'<=F STOP"
  apply (rule)
  by (simp only: NonTickDeadlockFree_DF'_ref[THEN sym] not_isNonTickDeadlockFree_STOP)




subsection \<open> DIV \<close>

lemma dfpnt_DIV : "$DF' <=F DIV"
  by (rule cspF_DIV_top)




subsection \<open> SKIP \<close>


lemma not_isNonTickDeadlockFree_SKIP : "\<not> SKIP isNonTickDeadlockFree"
  apply (simp add: NonTickDeadlockFree_def)
  apply (simp add: in_failures)
  apply (fast)
done

lemma not_dfpnt_SKIP : "\<not> $DF'<=F SKIP"
  apply (rule)
  by (simp only: NonTickDeadlockFree_DF'_ref[THEN sym] not_isNonTickDeadlockFree_SKIP)




subsection \<open> Ext_pre_choice \<close>

lemma dfpnt_Ext_pre_choice : "X \<noteq> {} \<Longrightarrow> \<lbrakk> \<And>a. a \<in> X \<Longrightarrow> $DF' <=F P a \<rbrakk> \<Longrightarrow> $DF' <=F ? :X -> P"
  apply (cspF_auto_left)
  apply (simp only: Int_pre_choice_def)
  by (rule cspF_Int_Ext_pre_choice_subset, simp_all)


lemma dfpnt_Ext_pre_choice2 : "X \<noteq> {} \<Longrightarrow> \<lbrakk> \<And>a. a \<in> X \<Longrightarrow> $DF' <=F P a \<rbrakk> \<Longrightarrow> $DF' <=F ? x:X -> P x"
  by (rule dfpnt_Ext_pre_choice, simp, simp)


lemma dfpnt_Ext_pre_choice_DIV : "X \<noteq> {} \<Longrightarrow> $DF' <=F ? x:X -> DIV"
  by (rule dfpnt_Ext_pre_choice, simp, simp)




subsection \<open> Act_prefix, Send_prefix and Rec_prefix \<close>


lemma dfpnt_Act_prefix : "$DF' <=F P \<Longrightarrow> $DF' <=F x -> P"
  apply (cspF_auto_right)
  by (rule dfpnt_Ext_pre_choice, rule, simp)

lemma dfpnt_Send_prefix : "$DF' <=F P \<Longrightarrow> $DF' <=F x ! y -> P"
  by (simp add: Send_prefix_def, rule dfpnt_Act_prefix)


lemma dfpnt_Rec_prefix : "\<forall>x \<in> range f. $DF' <=F P ((inv f) x) \<Longrightarrow> inj f \<Longrightarrow> $DF' <=F f ? x -> P x"
  apply (simp add: Rec_prefix_def)
  by (rule dfpnt_Ext_pre_choice, simp add: image_def, force, clarsimp)

lemma dfpnt_Rec_prefix2 : "X \<noteq> {} \<Longrightarrow> \<forall>x \<in> (f ` X). $DF' <=F P ((inv f) x) \<Longrightarrow> inj f \<Longrightarrow> $DF' <=F f ? x:X -> P x"
  apply (simp add: Rec_prefix_def)
  by (rule dfpnt_Ext_pre_choice2, simp, clarsimp)




subsection \<open> Int_choice \<close>

lemma dfpnt_Int_choice : "$DF' <=F P \<Longrightarrow> $DF' <=F Q \<Longrightarrow>  $DF' <=F P |~| Q"
  by (rule cspF_Int_choice_right, simp)




subsection \<open> Ext_choice \<close>


lemma dfpnt_Ext_choice_STOP_l : "P =F ? x:X -> Pf \<Longrightarrow> X \<noteq> {} \<Longrightarrow> $DF'<=F Pf \<Longrightarrow> $DF' <=F STOP [+] P"
  apply (rule cspF_rw_right, rule cspF_decompo, rule cspF_reflex, simp)
  by (cspF_auto_right, rule dfpnt_Ext_pre_choice, simp_all)

lemma dfpnt_Ext_choice_STOP_r : "P =F ? x:X -> Pf \<Longrightarrow> X \<noteq> {} \<Longrightarrow> $DF'<=F Pf \<Longrightarrow> $DF' <=F P [+] STOP"
  apply (rule cspF_rw_right, rule cspF_commut)
  by (rule dfpnt_Ext_choice_STOP_l)

lemma dfpnt_Ext_choice : "$DF' <=F P \<Longrightarrow> $DF' <=F Q \<Longrightarrow>  $DF' <=F P [+] Q"
  by (rule cspF_Ext_choice_right, simp)



lemma dfpnt_Send_Rec_choice : "$DF' <=F f ! a -> $DF'
                                             [+] g ? x -> $DF'"
  apply (simp add: Rec_prefix_def Send_prefix_def)
  apply (rule cspF_Ext_choice_right)
  apply (rule cspF_rw_right,rule cspF_Act_prefix_step)
    apply (rule dfpnt_Ext_pre_choice, simp, simp)
  apply (rule dfpnt_Ext_pre_choice, simp, simp)
done




subsection \<open> IF \<close>

lemma dfpnt_IF : "(b \<Longrightarrow> $DF' <=F P) \<Longrightarrow> (\<not>b \<Longrightarrow> $DF' <=F Q) \<Longrightarrow>  $DF' <=F IF b THEN P ELSE Q"
  by (case_tac b, cspF_simp+)




subsection \<open> Seq_compo \<close>

fun Seq_compo_DFnonTick :: "DFPN \<Rightarrow> (DFPN, 'e) proc"
where
  "Seq_compo_DFnonTick (DF') = (($DF') << (\<lambda>n. ($DF') |~| SKIP)) ;; $DF'"


lemma dfpnt_Seq_compo :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
     $DF' |~| SKIP <=F P \<Longrightarrow> $DF' <=F Q \<Longrightarrow> $DF' <=F P ;; Q"
  apply (rule cspF_fp_induct_ref_left[of "DFfun" "Seq_compo_DFnonTick"])
  apply (simp_all)
  apply (induct_tac p, simp_all)
  apply (rule cspF_rw_right)
  apply (rule cspF_decompo)
  apply (cspF_unwind)
  apply (cspF_auto_right)
  apply (rule cspF_Int_choice_right)
     apply (cspF_step_left)
     apply (cspF_hsf_right)
     apply (cspF_hsf_right)
     apply (rule cspF_decompo, simp)
     apply (cspF_hsf)
     apply (cspF_hsf_right)
     apply (rule cspF_decompo, simp)
     apply (cspF_hsf)
     apply (cspF_hsf_left)
     apply (rule cspF_Int_choice_left1)
     apply (rule cspF_decompo, simp)
     apply (cspF_auto)
   apply (cspF_hsf_right)
     apply (cspF_step_left)
     apply (rule cspF_decompo, simp)
     apply (cspF_auto)
     apply (rule cspF_decompo, simp)
     apply (cspF_auto_left)
     apply (rule cspF_Int_choice_left2)
     apply (cspF_auto_left)
  done



subsection \<open> Timeout \<close>

lemma dfpnt_Timeout1 :
    "$DF'<=F P \<Longrightarrow> $DF'<=F Qf \<Longrightarrow> $DF'<=F P [> x -> Qf"
  apply (cspF_auto_right)
  apply (rule dfpnt_Int_choice)
  apply (rule dfpnt_Ext_choice, simp_all)
  apply (rule dfpnt_Act_prefix, simp)
  apply (cspF_auto_right, rule dfpnt_Act_prefix, simp)
  done

lemma dfpnt_Timeout2 :
    "$DF'<=F P \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<forall>x\<in>X . $DF'<=F Qf x \<Longrightarrow> $DF'<=F P [> ? :X -> Qf"
  apply (cspF_auto_right)
  apply (rule dfpnt_Int_choice)
  apply (rule dfpnt_Ext_choice, simp_all)
  apply (rule dfpnt_Ext_pre_choice, simp, simp)
  apply (cspF_auto_right, rule dfpnt_Ext_pre_choice, simp, simp)
  done

lemma dfpnt_Timeout3 :
    "$DF'<=F P \<Longrightarrow> Q =F ? x:X -> Qf \<Longrightarrow> X \<noteq> {} \<Longrightarrow> $DF'<=F Qf \<Longrightarrow> $DF'<=F P [> Q"
  apply (cspF_auto_right)
  apply (rule dfpnt_Int_choice)
  apply (rule dfpnt_Ext_choice, simp_all)
  apply (rule cspF_rw_right, simp, rule dfpnt_Ext_pre_choice, simp, simp)
  apply (rule cspF_rw_right, rule cspF_decompo, rule cspF_reflex, simp)
  apply (cspF_auto_right, rule dfpnt_Ext_pre_choice, simp, simp)
  done


lemmas dfpnt_Timeout = dfpnt_Timeout1 dfpnt_Timeout2 dfpnt_Timeout3




subsection \<open> Hiding \<close>


lemma isNonTickDeadlockFree_Hiding :
    "P isNonTickDeadlockFree \<Longrightarrow> (P -- R) isNonTickDeadlockFree"
  apply (simp add: NonTickDeadlockFree_def)
  by (simp add: in_failures in_traces)


lemma dfpnt_Hiding : "$DF'<=F P \<Longrightarrow> $DF'<=F P -- R"
  apply (insert NonTickDeadlockFree_DF_ref[of P])
  apply (insert NonTickDeadlockFree_DF_ref[of "P -- R"])
  apply (insert isNonTickDeadlockFree_Hiding[of P R])
  apply (simp)
done



subsection \<open> Renamming \<close>


fun Renaming_DF':: "('e \<times> 'e) set \<Rightarrow> 'pn \<Rightarrow> (DFPN, 'e) proc"
where
  "Renaming_DF' R (_)      = $DF'[[ R ]]"


lemma dfpnt_Renaming :
    "FPmode = CMSmode \<or> FPmode = MIXmode \<Longrightarrow>
     \<forall> x y. f x \<noteq> g y \<Longrightarrow>
     inj f \<Longrightarrow>
     $DF' <=F P \<Longrightarrow>
     $DF' <=F P [[ f <== g ]]"
  apply (rule cspF_fp_induct_ref_left[of "DFfun" "Renaming_DF' (f <== g)"])
  apply (simp_all)
  apply (induct_tac p)
  apply (simp_all)
  apply (rule cspF_rw_right, rule cspF_decompo, simp)
    apply (rule cspF_unwind, simp, simp)
    apply (simp)
    apply (cspF_step)
    apply (cspF_step_left)
    apply (cspF_ren)

    apply (rule cspF_Rep_int_choice_right)
    apply (case_tac "\<forall> xa. a\<noteq>f xa")
      apply (rule cspF_Rep_int_choice_left)
        apply (simp add: image_def Image_def)
        apply (rule_tac x="a" in exI)
        apply (cspF_hsf)
        apply (cspF_hsf)
      apply (rule cspF_Rep_int_choice_left)
        apply (erule exE, simp)
        apply (rule_tac x="g xa" in exI)
        apply (cspF_hsf)
        apply (cspF_hsf)
done



subsection \<open> Rep_int_choice \<close>

lemma dfpnt_Rep_int_choice_f :
    "\<lbrakk> inj f ; !!a. a:X \<Longrightarrow> $DF'<=F Pf a \<rbrakk> \<Longrightarrow> $DF'<=F !<f> :X .. Pf"
  by (rule cspF_Rep_int_choice_right, simp, simp)


lemma dfpnt_Rep_int_choice_nat :
    "$DF'<=F P \<Longrightarrow> $DF'<=F !nat n:X .. P"
  by (rule cspF_Rep_int_choice_right, simp)






subsection \<open> Inductive_ext_choice and Rep_ext_choice \<close>

lemma dfpnt_Inductive_ext_choice_lm :
    "FPmode \<noteq> CPOmode \<Longrightarrow> l \<noteq> [] \<longrightarrow> (\<forall>a\<in> set l. $DF'<=F PXf a) \<longrightarrow>
     $DF'<=F [+] map PXf l"
  apply (induct_tac l)
  apply (simp)
  apply (rule, rule)
  apply (case_tac list, simp)
  apply (cspF_simp)
  by (rule dfpnt_Ext_choice, simp_all)

lemma dfpnt_Inductive_ext_choice :
    "FPmode \<noteq> CPOmode \<Longrightarrow> l \<noteq> [] \<Longrightarrow> \<forall>a\<in> set l. $DF'<=F PXf a \<Longrightarrow>
     $DF'<=F [+] map PXf l"
  by (simp add: dfpnt_Inductive_ext_choice_lm)


lemma dfpnt_Rep_ext_choice :
    "FPmode \<noteq> CPOmode \<Longrightarrow> L \<noteq> [] \<Longrightarrow> \<forall>a\<in> set L. $DF'<=F PXf a \<Longrightarrow>
     $DF'<=F [+] :L .. PXf"
  apply (simp add: Rep_ext_choice_def)
  by (rule dfpnt_Inductive_ext_choice, simp_all)





subsection \<open> Interleave \<close>

fun DFnt_Interleave :: "DFPN \<Rightarrow> (DFPN, 'e) proc"
where
    "DFnt_Interleave (DF') = ($DF'||| $DF')"


lemma dfpnt_Interleave :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
     $DF' <=F P \<Longrightarrow> $DF' <=F Q \<Longrightarrow> ($DF'::(DFPN, 'e) proc) <=F P ||| Q"
  apply (rule cspF_fp_induct_ref_left[of "DFfun" "DFnt_Interleave"])
  apply (simp_all)
  apply (induct_tac p, simp_all)
  apply (cspF_auto_right)
  apply (cspF_step_right)
  apply (cspF_step_right)
  apply (cspF_hsf_right)
  apply (cspF_hsf_right)
  apply (rule cspF_Rep_int_choice_right)
  apply (cspF_hsf_right)
  apply (cspF_hsf_right)
  apply (rule cspF_Rep_int_choice_right)
  apply (cspF_hsf_right)
  apply (cspF_step_left)
  apply (rule cspF_decompo_ref, simp, simp)
  apply (cspF_hsf_right)
     apply (erule disjE)
     apply (cspF_hsf_right)
     apply (case_tac "aa = a")
      apply (cspF_hsf_right)
       apply (cspF_hsf_right)
       apply (rule cspF_Int_choice_right)
       apply (rule cspF_decompo, simp, simp)
       apply (rule dfpnt_Ext_pre_choice, simp, simp)
       apply (rule cspF_decompo, simp)
       apply (rule dfpnt_Ext_pre_choice, simp, simp)
       apply (simp)
      apply (cspF_hsf_right)
       apply (cspF_hsf_right)
       apply (rule cspF_decompo, simp)
       apply (rule dfpnt_Ext_pre_choice, simp, simp)
       apply (simp)
     apply (case_tac "aa = a")
      apply (cspF_hsf_right)
       apply (cspF_hsf_right)
       apply (rule cspF_Int_choice_right)
       apply (rule cspF_decompo, simp, simp)
       apply (rule dfpnt_Ext_pre_choice, simp, simp)
       apply (rule cspF_decompo, simp)
       apply (rule dfpnt_Ext_pre_choice, simp, simp)
       apply (simp)
      apply (cspF_hsf_right)
       apply (cspF_hsf_right)
       apply (rule cspF_decompo, simp, simp)
       apply (rule dfpnt_Ext_pre_choice, simp, simp)
  done




subsection \<open> Inductive_interleave and Rep_interleaving \<close>

lemma dfpnt_Inductive_interleave_lm :
    "FPmode \<noteq> CPOmode \<Longrightarrow> l \<noteq> [] \<longrightarrow> (\<forall>a\<in> set l. $DF'<=F PXf a) \<longrightarrow>
     $DF'<=F ||| map PXf l"
  apply (induct_tac l)
  apply (rule, simp)
  apply (rule, simp)
  apply (intro impI, elim conjE)
  apply (case_tac list)
  apply (simp_all)
  apply (rule cspF_rw_right, rule cspF_Interleave_unit)
  apply (assumption)
  by (rule dfpnt_Interleave, simp_all)

lemma dfpnt_Inductive_interleave :
    "FPmode \<noteq> CPOmode \<Longrightarrow> l \<noteq> [] \<Longrightarrow> \<forall>a\<in> set l. $DF'<=F PXf a \<Longrightarrow>
     $DF'<=F ||| map PXf l"
  by (simp add: dfpnt_Inductive_interleave_lm)


lemma dfpnt_Rep_interleaving :
    "FPmode \<noteq> CPOmode \<Longrightarrow> X \<noteq> [] \<Longrightarrow> \<forall>a \<in> (set X). $DF'<=F PXf a \<Longrightarrow>
     $DF'<=F ||| :X .. PXf"
  apply (simp add: Rep_interleaving_def)
  by (rule dfpnt_Inductive_interleave, simp_all)




subsection \<open> Int_pre_choice \<close>

lemma dfpnt_Int_pre_choice :
    "\<forall>x\<in>X . $DF'<=F P x \<Longrightarrow> $DF'<=F ! :X -> P"
  apply (cspF_unwind)
  apply (cspF_step)+
  apply (rule cspF_decompo_ref, simp)
  by (cspF_step)+





subsection \<open> DF \<close>

lemma dfpnt_DF': "$DF' <=F $DF'"
  by (simp)

lemma dfpnt_DF: "$DF' <=F DF"
  by (simp add: DF_def)


lemmas dfpnt = allI
               ballI
               DF_def
               dfpnt_DF'
               not_dfpnt_STOP
               not_dfpnt_SKIP
               dfpnt_DIV
               dfpnt_Timeout
               dfpnt_Ext_pre_choice dfpnt_Send_prefix dfpnt_Rec_prefix dfpnt_Rec_prefix2 dfpnt_Act_prefix
               dfpnt_Ext_choice_STOP_l dfpnt_Ext_choice_STOP_r dfpnt_Ext_choice
               dfpnt_Int_pre_choice
               dfpnt_Int_choice
               dfpnt_IF
               dfpnt_Seq_compo
               dfpnt_Renaming
               dfpnt_Hiding
               dfpnt_Rep_int_choice_nat dfpnt_Rep_int_choice_f
               dfpnt_Interleave
               dfpnt_Inductive_ext_choice
               dfpnt_Rep_ext_choice
               dfpnt_Inductive_interleave
               dfpnt_Rep_interleaving

end