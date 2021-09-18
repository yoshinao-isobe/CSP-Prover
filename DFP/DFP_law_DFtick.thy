           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021               |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_law_DFtick
imports DFP_DFtick CSP_F
begin




lemma not_isDeadlockFree_STOP : "\<not> STOP isDeadlockFree"
  apply (simp add: DeadlockFree_def)
  by (simp add: in_failures)


lemma not_dfp_STOP : "\<not> $DFtick <=F STOP"
  apply (rule)
  by (simp only: DeadlockFree_DFtick_ref[THEN sym] not_isDeadlockFree_STOP)



lemma dfp_DIV : "$DFtick \<sqsubseteq>F DIV"
  by (cspF_auto)

lemma dfp_SKIP : "$DFtick \<sqsubseteq>F SKIP"
  apply (cspF_auto)
  by (rule cspF_Int_choice_left2, simp)


lemma dfp_Ext_pre_choice : "X \<noteq> {} \<Longrightarrow> \<lbrakk> \<And>a. a \<in> X \<Longrightarrow> $DFtick \<sqsubseteq>F P a \<rbrakk> \<Longrightarrow> $DFtick \<sqsubseteq>F ? :X -> P"
  apply (cspF_auto_left)
  apply (rule cspF_Int_choice_left1)
  apply (simp only: Int_pre_choice_def)
  by (rule cspF_Int_Ext_pre_choice_subset, simp_all)


lemma dfp_Ext_pre_choice2 : "X \<noteq> {} \<Longrightarrow> \<lbrakk> \<And>a. a \<in> X \<Longrightarrow> $DFtick \<sqsubseteq>F P a \<rbrakk> \<Longrightarrow> $DFtick \<sqsubseteq>F ? x:X -> P x"
  by (rule dfp_Ext_pre_choice, simp, simp)


lemma dfp_Ext_pre_choice_DIV : "X \<noteq> {} \<Longrightarrow> $DFtick \<sqsubseteq>F ? x:X -> DIV"
  by (rule dfp_Ext_pre_choice, simp, simp)


(*lemma dfp_Ext_pre_choice_DIV_iff : "$DFtick \<sqsubseteq>F ? x:X -> DIV \<longleftrightarrow> X \<noteq> {}"
  apply (case_tac "X={}")
   apply (simp_all add: dfp_Ext_pre_choice)
   apply (rule notI)
   apply (simp add: cspF_cspT_semantics)
   apply (erule conjE)
   apply (simp add: cspT_semantics)
   apply (simp add: traces_iff)
   apply (simp add: failures_iff sndF_def le_less)
   apply (erule disjE)
   apply (simp add: CollectF_def)
   apply (case_tac "FPmode=CMSmode")
   apply (simp)
   apply (simp add: UFP_def hasUFP_def isUFP_def semFfun_def semFf_def)
   apply (simp add: UFP_def LFP_def)*)

lemma dfp_Act_prefix : "$DFtick \<sqsubseteq>F P \<Longrightarrow> $DFtick \<sqsubseteq>F x \<rightarrow> P"
  apply (cspF_auto_right)
  by (rule dfp_Ext_pre_choice, rule, simp)

lemma dfp_Send_prefix : "$DFtick \<sqsubseteq>F P \<Longrightarrow> $DFtick \<sqsubseteq>F x ! y \<rightarrow> P"
  by (simp add: Send_prefix_def, rule dfp_Act_prefix)


lemma dfp_Rec_prefix : "\<forall>x \<in> range f. $DFtick \<sqsubseteq>F P ((inv f) x) \<Longrightarrow> inj f \<Longrightarrow> $DFtick \<sqsubseteq>F f ? x \<rightarrow> P x"
  apply (simp add: Rec_prefix_def)
  by (rule dfp_Ext_pre_choice, simp add: image_def, force, clarsimp)

lemma dfp_Rec_prefix2 : "X \<noteq> {} \<Longrightarrow> \<forall>x \<in> (f ` X). $DFtick \<sqsubseteq>F P ((inv f) x) \<Longrightarrow> inj f \<Longrightarrow> $DFtick \<sqsubseteq>F f ? x:X \<rightarrow> P x"
  apply (simp add: Rec_prefix_def)
  by (rule dfp_Ext_pre_choice2, simp, clarsimp)


(*
lemma dfp_Int_choice_STOP_l : "P =F ? x:X \<rightarrow> Pf \<Longrightarrow> X \<noteq> {} \<Longrightarrow> $DFtick <=F Pf \<Longrightarrow> $DFtick \<sqsubseteq>F STOP |~| P"
  apply (rule cspF_rw_right, rule cspF_decompo, rule cspF_reflex, simp)
  apply (cspF_auto_right)
  by (cspF_auto_right, rule dfp_Ext_pre_choice, simp_all)

lemma dfp_Int_choice_STOP_r : "P =F ? x:X \<rightarrow> Pf \<Longrightarrow> X \<noteq> {} \<Longrightarrow> $DFtick <=F Pf \<Longrightarrow> $DFtick \<sqsubseteq>F P |~| STOP"
  apply (rule cspF_rw_right, rule cspF_commut)
  by (rule dfp_Int_choice_STOP_l)
*)

lemma dfp_Int_choice : "$DFtick \<sqsubseteq>F P \<Longrightarrow> $DFtick \<sqsubseteq>F Q \<Longrightarrow>  $DFtick \<sqsubseteq>F P |~| Q"
  by (rule cspF_Int_choice_right, simp)


lemma dfp_Int_choice_SKIP_l : "$DFtick \<sqsubseteq>F P \<Longrightarrow> $DFtick \<sqsubseteq>F SKIP |~| P"
  by (rule dfp_Int_choice, rule dfp_SKIP, simp)


lemma dfp_Int_choice_SKIP_r : "$DFtick \<sqsubseteq>F P \<Longrightarrow> $DFtick \<sqsubseteq>F P |~| SKIP"
  by (rule dfp_Int_choice, simp, rule dfp_SKIP)


lemma dfp_Ext_choice_STOP_l : "P =F ? x:X \<rightarrow> Pf \<Longrightarrow> X \<noteq> {} \<Longrightarrow> $DFtick <=F Pf \<Longrightarrow> $DFtick \<sqsubseteq>F STOP [+] P"
  apply (rule cspF_rw_right, rule cspF_decompo, rule cspF_reflex, simp)
  by (cspF_auto_right, rule dfp_Ext_pre_choice, simp_all)

lemma dfp_Ext_choice_STOP_r : "P =F ? x:X \<rightarrow> Pf \<Longrightarrow> X \<noteq> {} \<Longrightarrow> $DFtick <=F Pf \<Longrightarrow> $DFtick \<sqsubseteq>F P [+] STOP"
  apply (rule cspF_rw_right, rule cspF_commut)
  by (rule dfp_Ext_choice_STOP_l)

lemma dfp_Ext_choice : "$DFtick \<sqsubseteq>F P \<Longrightarrow> $DFtick \<sqsubseteq>F Q \<Longrightarrow>  $DFtick \<sqsubseteq>F P [+] Q"
  by (rule cspF_Ext_choice_right, simp)


lemma dfp_Ext_choice_SKIP_l : "$DFtick \<sqsubseteq>F P \<Longrightarrow> $DFtick \<sqsubseteq>F SKIP [+] P"
  by (rule dfp_Ext_choice, rule dfp_SKIP, simp)


lemma dfp_Ext_choice_SKIP_r : "$DFtick \<sqsubseteq>F P \<Longrightarrow> $DFtick \<sqsubseteq>F P [+] SKIP"
  by (rule dfp_Ext_choice, simp, rule dfp_SKIP)



lemma dfp_Send_Rec_choice : "$DFtick \<sqsubseteq>F f ! a -> $DFtick 
                                            [+] g ? x -> $DFtick"
  apply (simp add: Rec_prefix_def Send_prefix_def)
  apply (rule cspF_Ext_choice_right)
  apply (rule cspF_rw_right,rule cspF_Act_prefix_step)
    apply (rule dfp_Ext_pre_choice, simp, simp)
  apply (rule dfp_Ext_pre_choice, simp, simp)
done




lemma dfp_IF : "(b \<Longrightarrow> $DFtick \<sqsubseteq>F P) \<Longrightarrow> (\<not>b \<Longrightarrow> $DFtick \<sqsubseteq>F Q) \<Longrightarrow>  $DFtick \<sqsubseteq>F IF b THEN P ELSE Q"
  by (case_tac b, cspF_simp+)





fun Seq_compo_DFtick :: "DFtickName \<Rightarrow> (DFtickName, 'e) proc"
where
  "Seq_compo_DFtick DFtick = $DFtick ;; $DFtick"


lemma dfp_Seq_compo :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
     $DFtick <=F P \<Longrightarrow> $DFtick <=F Q \<Longrightarrow> $DFtick <=F P ;; Q"
  apply (rule cspF_fp_induct_ref_left[of "DFtickfun" "Seq_compo_DFtick"])
  apply (simp_all)
  apply (induct_tac p, simp_all)
  apply (cspF_auto_right)
  apply (cspF_step_right)
  apply (cspF_hsf_right)
  apply (rule cspF_Int_choice_right)
   apply (rule cspF_Int_choice_left1)
     apply (cspF_step_left)
     apply (cspF_hsf_right)
     apply (rule cspF_decompo, simp)
     apply (cspF_hsf)
     apply (cspF_hsf_right)
   apply (cspF_hsf_right)
     apply (cspF_auto_right)
     apply (cspF_auto_right)
     apply (rule cspF_Int_choice_right)
     apply (cspF_step_left)
     apply (rule cspF_Int_choice_left1)
     apply (rule cspF_decompo, simp)
     apply (rule cspF_decompo, simp)
     apply (cspF_auto_right)
     apply (cspF_auto)
     apply (cspF_auto_left)
     apply (rule cspF_Int_choice_left2)
     apply (cspF_auto_left)
     apply (cspF_auto_left)
     apply (cspF_step_left)
     apply (rule cspF_Int_choice_left2, simp)
  done

lemma dfp_Timeout1 :
    "$DFtick <=F P \<Longrightarrow> $DFtick <=F Qf \<Longrightarrow> $DFtick <=F P [> x \<rightarrow> Qf"
  apply (cspF_auto_right)
  apply (rule dfp_Int_choice)
  apply (rule dfp_Ext_choice, simp_all)
  apply (rule dfp_Act_prefix, simp)
  apply (cspF_auto_right, rule dfp_Act_prefix, simp)
  done

lemma dfp_Timeout2 :
    "$DFtick <=F P \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<forall>x\<in>X . $DFtick <=F Qf x \<Longrightarrow> $DFtick <=F P [> ? :X -> Qf"
  apply (cspF_auto_right)
  apply (rule dfp_Int_choice)
  apply (rule dfp_Ext_choice, simp_all)
  apply (rule dfp_Ext_pre_choice, simp, simp)
  apply (cspF_auto_right, rule dfp_Ext_pre_choice, simp, simp)
  done

lemma dfp_Timeout3 :
    "$DFtick <=F P \<Longrightarrow> Q =F ? x:X \<rightarrow> Qf \<Longrightarrow> X \<noteq> {} \<Longrightarrow> $DFtick <=F Qf \<Longrightarrow> $DFtick <=F P [> Q"
  apply (cspF_auto_right)
  apply (rule dfp_Int_choice)
  apply (rule dfp_Ext_choice, simp_all)
  apply (rule cspF_rw_right, simp, rule dfp_Ext_pre_choice, simp, simp)
  apply (rule cspF_rw_right, rule cspF_decompo, rule cspF_reflex, simp)
  apply (cspF_auto_right, rule dfp_Ext_pre_choice, simp, simp)
  done


lemmas dfp_Timeout = dfp_Timeout1 dfp_Timeout2 dfp_Timeout3



(*TODO dfp_Hiding*)
lemma isDeadlockFree_Hiding : "P isDeadlockFree \<Longrightarrow> (P -- R) isDeadlockFree"
  apply (simp add: DeadlockFree_def)
  apply (simp add: in_failures in_traces)
  apply (rule allI, rule impI, erule_tac x="s" in allE, simp)
  apply (rule allI, rule impI)
  apply (induct_tac sa rule: induct_trace)
  sorry

lemma dfp_Hiding : "$DFtick <=F P \<Longrightarrow> $DFtick <=F P -- R"
  by (simp only: DeadlockFree_DFtick_ref[THEN sym] isDeadlockFree_Hiding)



fun Hiding_DFtick :: "('e) set \<Rightarrow> 'pn \<Rightarrow> (DFtickName, 'e) proc"
where
  "Hiding_DFtick R (_)      = $DFtick -- R"


lemma dfp_Hiding_lm :
    "FPmode \<noteq> CPOmode \<Longrightarrow> $DFtick <=F P \<longrightarrow> $DFtick <=F P -- R"
  apply (induct P)
  apply (simp add: not_dfp_STOP)
  apply (rule, cspF_hsf_right)
  apply (cspF_hsf_right)
  apply (rule, cspF_hsf_right)

  apply (cspF_unwind)
  apply (cspF_step_left)
   apply (cspF_hsf_right)
   apply (rule cspF_rw_right, rule cspF_IF_split, simp, rule)
   apply (rule)
   apply (rule cspF_Int_choice_left1)
   apply (rule cspF_decompo_ref, simp, simp, simp)
   apply (subgoal_tac " $DFtick <=F x1 -> P \<longrightarrow> $DFtick <=F P", simp, simp)

oops

lemma dfp_Hiding2 :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
     $DFtick \<sqsubseteq>F P \<Longrightarrow>
     $DFtick \<sqsubseteq>F P -- R"

  apply (rule cspF_fp_induct_ref_left[of "DFtickfun" "Hiding_DFtick R"], simp_all)

  apply (induct_tac p, simp)

  apply (cspF_step_left)
  apply (cspF_unwind_right)

   apply (cspF_hsf_right)
   apply (cspF_hsf_right)
   apply (cspF_hsf_right)
   apply (rule cspF_Int_choice_right)

   apply (rule cspF_Int_choice_left1)
   apply (rule cspF_Rep_int_choice_right)
   apply (rule cspF_Rep_int_choice_left, rule_tac x="a" in exI, simp)

   apply (case_tac "a \<in> R")
   (* a \<in> R *)
   apply (cspF_hsf_right, cspF_hsf_right, cspF_hsf_right)
   apply (rule cspF_rw_right, rule cspF_Timeout_cong, rule cspF_STOP_step[THEN cspF_sym], rule cspF_reflex)
   apply (rule cspF_rw_right, rule cspF_STOP_Timeout)
   apply (cspF_hsf)
defer
   apply (cspF_hsf_right)
   apply (cspF_hsf_right)
   apply (cspF_hsf_right)
   apply (cspF_step)

   (* SKIP *)
   apply (rule cspF_Int_choice_left2)
   apply (cspF_simp)


   apply (cspF_unwind_right, cspF_hsf_right, cspF_step_right)
   apply (cspF_hsf_right)
sorry




fun Renaming_DFtick :: "('e \<times> 'e) set \<Rightarrow> 'pn \<Rightarrow> (DFtickName, 'e) proc"
where
  "Renaming_DFtick R (_)      = $DFtick [[ R ]]"


lemma dfp_Renaming :
    "FPmode = CMSmode \<or> FPmode = MIXmode \<Longrightarrow>
     \<forall> x y. f x \<noteq> g y \<Longrightarrow>
     inj f \<Longrightarrow>
     $DFtick \<sqsubseteq>F P \<Longrightarrow>
     $DFtick \<sqsubseteq>F P [[ f <== g ]]"
  apply (rule cspF_fp_induct_ref_left[of "DFtickfun" "Renaming_DFtick (f <== g)"])
  apply (simp_all)
  apply (induct_tac p)
  apply (simp_all)
  apply (rule cspF_rw_right, rule cspF_decompo, simp)
    apply (rule cspF_unwind, simp, simp)
    apply (simp)
    apply (cspF_step, cspF_ren, cspF_hsf)
    apply (rule cspF_decompo)
    apply (cspF_simp)
    apply (rule cspF_Rep_int_choice_right)
    apply (case_tac "\<forall> xa. a\<noteq>f xa")
      apply (cspF_hsf)
        apply (rule cspF_Rep_int_choice_left)
        apply (simp add: image_def)
        apply (rule_tac x="a" in exI)
        apply (cspF_hsf)
      apply (erule exE, simp)
        apply (cspF_hsf)
        apply (rule cspF_Rep_int_choice_left)
        apply (rule_tac x="g xa" in exI, simp)
        apply (cspF_hsf)
done


lemma dfp_Rep_int_choice_f :
    "\<lbrakk> inj f ; !!a. a:X \<Longrightarrow> $DFtick <=F Pf a \<rbrakk> \<Longrightarrow> $DFtick <=F !<f> :X .. Pf"
  by (rule cspF_Rep_int_choice_right, simp, simp)


lemma dfp_Rep_int_choice_nat :
    "$DFtick <=F P \<Longrightarrow> $DFtick <=F !nat n:X .. P"
  by (rule cspF_Rep_int_choice_right, simp)



fun DF_Interleave :: "DFtickName \<Rightarrow> (DFtickName, 'e) proc"
where
    "DF_Interleave DFtick = $DFtick ||| $DFtick"


lemma dfp_Interleave :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
     $DFtick <=F P \<Longrightarrow> $DFtick <=F Q \<Longrightarrow> $DFtick <=F P ||| Q"
  apply (rule cspF_fp_induct_ref_left[of "DFtickfun" "DF_Interleave"])
  apply (simp_all)
  apply (induct_tac p, simp_all)
  apply (cspF_auto_right)
  apply (cspF_step_right)
  apply (cspF_hsf_right)
  apply (rule cspF_Int_choice_right)
   apply (rule cspF_Int_choice_left1)
     apply (cspF_step_left)
     apply (cspF_hsf_right)
     apply (rule cspF_Int_choice_right)
     apply (cspF_hsf_right)+
     apply (rule cspF_Rep_int_choice_right)
     apply (rule cspF_Rep_int_choice_right)
     apply (rule cspF_decompo_ref, simp, simp)
     apply (cspF_hsf_right)
     apply (erule disjE)
     apply (cspF_hsf_right)
     apply (case_tac "aa = a")
      apply (cspF_hsf_right)
       apply (cspF_hsf_right)
       apply (rule cspF_Int_choice_right)
       apply (rule cspF_decompo, simp, simp)
       apply (rule dfp_Ext_pre_choice, simp, simp)
       apply (rule cspF_decompo, simp)
       apply (rule dfp_Ext_pre_choice, simp, simp)
       apply (simp)
      apply (cspF_hsf_right)
       apply (cspF_hsf_right)
       apply (rule cspF_decompo, simp)
       apply (rule dfp_Ext_pre_choice, simp, simp)
       apply (simp)
     apply (case_tac "aa = a")
      apply (cspF_hsf_right)
       apply (cspF_hsf_right)
       apply (rule cspF_Int_choice_right)
       apply (rule cspF_decompo, simp, simp)
       apply (rule dfp_Ext_pre_choice, simp, simp)
       apply (rule cspF_decompo, simp)
       apply (rule dfp_Ext_pre_choice, simp, simp)
       apply (simp)
      apply (cspF_hsf_right)
       apply (cspF_hsf_right)
       apply (rule cspF_decompo, simp, simp)
       apply (rule dfp_Ext_pre_choice, simp, simp)
     apply (cspF_hsf_right)
     apply (rule cspF_decompo, simp)
     apply (rule cspF_decompo, simp)
     apply (cspF_auto)
     apply (cspF_auto_left)
      apply (rule cspF_Int_choice_left2)
      apply (cspF_auto_left)
     apply (cspF_auto)
     apply (rule cspF_Int_choice_right)
     apply (rule cspF_Int_choice_left1)
     apply (rule cspF_decompo, simp)
     apply (rule cspF_decompo, simp)
     apply (cspF_auto_left)
     apply (cspF_auto_left)
      apply (rule cspF_Int_choice_left2)
      apply (cspF_auto_left)
     apply (cspF_step_left)
     apply (cspF_auto_right)
     apply (cspF_step_right)
     apply (rule cspF_Int_choice_left2)
     apply (cspF_simp)
  done


lemmas dfp = ballI cspF_reflex (* $DFtick <=F $DFtick *)
             not_dfp_STOP
             dfp_SKIP dfp_DIV
             dfp_Timeout
             dfp_Ext_pre_choice dfp_Send_prefix dfp_Rec_prefix dfp_Rec_prefix2 dfp_Act_prefix
             dfp_Ext_choice_STOP_l dfp_Ext_choice_STOP_r dfp_Ext_choice
             dfp_Int_choice
             dfp_IF
             dfp_Seq_compo
             dfp_Renaming
             dfp_Hiding
             dfp_Rep_int_choice_nat dfp_Rep_int_choice_f
             dfp_Interleave
end