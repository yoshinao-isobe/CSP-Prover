           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021               |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_DFnonTick
imports DFP_law_DFtick
begin


section \<open> The Non-Terminating Deadlock-free (DFnonTick) Processes \<close>

subsection \<open> DFnonTick \<close>

datatype DFnonTickPN = DFnonTick

primrec
  DFnonTickfun ::  "(DFnonTickPN, 'event) pnfun"
where
  "DFnonTickfun (DFnonTick) = (! x ->  $(DFnonTick)) "

overloading Set_DFnonTickfun == 
  "PNfun :: (DFnonTickPN, 'event) pnfun"
begin
  definition "PNfun :: (DFnonTickPN, 'event) pnfun == DFnonTickfun"
end
  
declare Set_DFnonTickfun_def [simp]



lemma guardedfun_DFnonTickfun [simp]: "guardedfun DFnonTickfun"
  apply (simp add: guardedfun_def)
by (rule allI, induct_tac p, simp)



fun DF_induct_Hypotheses :: "DFnonTickPN \<Rightarrow> (DFtickName, 'e) proc"
where
    "DF_induct_Hypotheses (DFnonTick) = $DFtick"

lemma Lemma_DFnonTickPN_To_DFtick :
    "DF_induct_Hypotheses p \<sqsubseteq>F (DFnonTickfun p) << DF_induct_Hypotheses"
by (induct_tac p, simp, cspF_unwind, rule cspF_Int_choice_left1, cspF_auto)


lemma dfp_DFnonTick: "$DFtick <=F $DFnonTick"
  apply (rule_tac Pf="DFnonTickfun" and f="DF_induct_Hypotheses" in cspF_fp_induct_ref_right)
  apply (simp, case_tac FPmode, simp_all)
  apply (rule Lemma_DFnonTickPN_To_DFtick)
done


lemma DFnonTick_is_DeadlockFree:
  "(($DFnonTick) :: (DFnonTickPN, 'e) proc) isDeadlockFree"
by (simp only: DeadlockFree_DFtick_ref, rule dfp_DFnonTick)




subsection \<open> DFalphaNonTick \<close>



datatype ('e) DFalphaNonTickPN = DFalphaNonTick "'e neset"

primrec
  DFalphaNonTickfun ::  "('e DFalphaNonTickPN, 'e) pnfun"
where
  "DFalphaNonTickfun (DFalphaNonTick X) = (! x:(to_set X) -> $(DFalphaNonTick X)) "

overloading Set_DFalphaNonTickfun == 
  "PNfun :: ('e DFalphaNonTickPN, 'e) pnfun"
begin
  definition "PNfun :: ('e DFalphaNonTickPN, 'e) pnfun == DFalphaNonTickfun"
end
  
declare Set_DFalphaNonTickfun_def [simp]



lemma guardedfun_DFalphaNonTickfun [simp]: "guardedfun DFalphaNonTickfun"
  apply (simp add: guardedfun_def)
by (rule allI, induct_tac p, auto)


fun DFalpha_induct_Hypotheses :: "'e DFalphaNonTickPN \<Rightarrow> (DFnonTickPN, 'e) proc"
where
    "DFalpha_induct_Hypotheses (DFalphaNonTick X) = $DFnonTick"

lemma Lemma_DFalphaNonTick_To_DFtick :
    "DFalpha_induct_Hypotheses p \<sqsubseteq>F (DFalphaNonTickfun p) << DFalpha_induct_Hypotheses"
  apply (induct_tac p, simp, cspF_unwind)
  apply (cspF_hsf)
  apply (induct_tac xa)
  apply (simp add: to_neset_inverse)
by (rule cspF_Rep_int_choice_subset, simp, simp)




lemma dfnt_DFalphaNonTick: "($DFnonTick::((DFnonTickPN, 'e) proc)) <=F $DFalphaNonTick (X::'e neset)"
  apply (rule_tac Pf="DFalphaNonTickfun" and f="DFalpha_induct_Hypotheses" in cspF_fp_induct_ref_right)
  apply (simp, case_tac FPmode, simp_all)
  apply (rule Lemma_DFalphaNonTick_To_DFtick)
done


lemma DFalphaNonTick_is_DeadlockFree:
  "(($DFalphaNonTick X) :: ('e DFalphaNonTickPN, 'e) proc) isDeadlockFree"
  apply (simp only: DeadlockFree_DFtick_ref)
  apply (rule cspF_trans)
  apply (rule dfp_DFnonTick)
by (rule dfnt_DFalphaNonTick)





subsection \<open> DFchoiceNonTick \<close>



datatype ('e) DFchoiceNonTickPN = DFchoiceNonTick "'e neset" "'e neset"

primrec
  DFchoiceNonTickfun ::  "('e DFchoiceNonTickPN, 'e) pnfun"
where
  "DFchoiceNonTickfun (DFchoiceNonTick X Y) = (! x:(to_set X) -> $(DFchoiceNonTick X Y)
                                               [+] ! y:(to_set Y) -> $(DFchoiceNonTick X Y))"

overloading Set_DFchoiceNonTickfun == 
  "PNfun :: ('e DFchoiceNonTickPN, 'e) pnfun"
begin
  definition "PNfun :: ('e DFchoiceNonTickPN, 'e) pnfun == DFchoiceNonTickfun"
end
  
declare Set_DFchoiceNonTickfun_def [simp]



lemma guardedfun_DFchoiceNonTickfun [simp]: "guardedfun DFchoiceNonTickfun"
  apply (simp add: guardedfun_def)
by (rule allI, induct_tac p, auto)


fun DFchoice_induct_Hypotheses :: "'e DFchoiceNonTickPN \<Rightarrow> ('e DFalphaNonTickPN, 'e) proc"
where
    "DFchoice_induct_Hypotheses (DFchoiceNonTick X Y) = $DFalphaNonTick (to_set X \<union> to_set Y)"

lemma Lemma_DFchoiceNonTick_To_DFtick :
    "DFchoice_induct_Hypotheses p \<sqsubseteq>F (DFchoiceNonTickfun p) << DFchoice_induct_Hypotheses"
  apply (induct_tac p, simp, cspF_unwind)
  apply (cspF_hsf)
  apply (induct_tac x1a)
  apply (induct_tac x2a)
  apply (simp add: to_neset_inverse)
  apply (rule cspF_Ext_choice_right)
  apply (rule cspF_Rep_int_choice_subset, simp, simp)
  apply (rule cspF_Rep_int_choice_subset, simp, simp)
done



lemma dfant_DFchoiceNonTick:
    "X \<noteq> {} \<and> Y \<noteq> {} \<Longrightarrow>
    (($DFalphaNonTick (to_neset (to_set X \<union> to_set Y)))::(('e DFalphaNonTickPN, 'e) proc)) <=F $DFchoiceNonTick (X::'e neset) (Y::'e neset)"
  apply (rule_tac Pf="DFchoiceNonTickfun" and f="DFchoice_induct_Hypotheses" in cspF_fp_induct_ref_right)
  apply (simp, case_tac FPmode, simp_all (no_asm_simp))
  apply (rule Lemma_DFchoiceNonTick_To_DFtick)
done


lemma DFchoiceNonTick_is_DeadlockFree:
  "X \<noteq> {} \<and> Y \<noteq> {} \<Longrightarrow> (($DFchoiceNonTick X Y) :: ('e DFchoiceNonTickPN, 'e) proc) isDeadlockFree"
  apply (simp only: DeadlockFree_DFtick_ref)
  apply (rule cspF_trans)
  apply (rule dfp_DFnonTick)
  apply (rule cspF_trans)
  apply (rule_tac X="to_set X \<union> to_set Y" in dfnt_DFalphaNonTick)
  apply (rule dfant_DFchoiceNonTick, simp)
done




subsection \<open> DFintChoiceNonTick \<close>


datatype ('e) DFintChoiceNonTickPN = DFintChoiceNonTick "'e neset" "'e neset"

primrec
  DFintChoiceNonTickfun ::  "('e DFintChoiceNonTickPN, 'e) pnfun"
where
  "DFintChoiceNonTickfun (DFintChoiceNonTick X Y) = (! x:(to_set X) -> $(DFintChoiceNonTick X Y)
                                               |~| ! y:(to_set Y) -> $(DFintChoiceNonTick X Y))"

overloading Set_DFintChoiceNonTickfun == 
  "PNfun :: ('e DFintChoiceNonTickPN, 'e) pnfun"
begin
  definition "PNfun :: ('e DFintChoiceNonTickPN, 'e) pnfun == DFintChoiceNonTickfun"
end
  
declare Set_DFintChoiceNonTickfun_def [simp]



lemma guardedfun_DFintChoiceNonTickfun [simp]: "guardedfun DFintChoiceNonTickfun"
  apply (simp add: guardedfun_def)
by (rule allI, induct_tac p, auto)


fun DFintChoice_induct_Hypotheses :: "'e DFintChoiceNonTickPN \<Rightarrow> ('e DFalphaNonTickPN, 'e) proc"
where
    "DFintChoice_induct_Hypotheses (DFintChoiceNonTick X Y) = $DFalphaNonTick (to_set X \<union> to_set Y)"

lemma Lemma_DFintChoiceNonTick_To_DFtick :
    "DFintChoice_induct_Hypotheses p \<sqsubseteq>F (DFintChoiceNonTickfun p) << DFintChoice_induct_Hypotheses"
  apply (induct_tac p, simp, cspF_unwind)
  apply (cspF_hsf)
  apply (induct_tac x1a)
  apply (induct_tac x2a)
  apply (simp add: to_neset_inverse)
  apply (cspF_auto)
done



lemma dfant_DFintChoiceNonTick:
    "X \<noteq> {} \<and> Y \<noteq> {} \<Longrightarrow>
    (($DFalphaNonTick (to_neset (to_set X \<union> to_set Y)))::(('e DFalphaNonTickPN, 'e) proc)) <=F $DFintChoiceNonTick (X::'e neset) (Y::'e neset)"
  apply (rule_tac Pf="DFintChoiceNonTickfun" and f="DFintChoice_induct_Hypotheses" in cspF_fp_induct_ref_right)
  apply (simp, case_tac FPmode, simp_all (no_asm_simp))
  apply (rule Lemma_DFintChoiceNonTick_To_DFtick)
done


lemma DFintChoiceNonTick_is_DeadlockFree:
  "X \<noteq> {} \<and> Y \<noteq> {} \<Longrightarrow> (($DFintChoiceNonTick X Y) :: ('e DFintChoiceNonTickPN, 'e) proc) isDeadlockFree"
  apply (simp only: DeadlockFree_DFtick_ref)
  apply (rule cspF_trans)
  apply (rule dfp_DFnonTick)
  apply (rule cspF_trans)
  apply (rule_tac X="to_set X \<union> to_set Y" in dfnt_DFalphaNonTick)
  apply (rule dfant_DFintChoiceNonTick, simp)
done



end