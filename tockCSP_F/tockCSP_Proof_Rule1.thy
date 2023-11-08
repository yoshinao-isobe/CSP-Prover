           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 2022 / 2023               |
            |                                           |
            |          Lemmas and Theorems from         |
            |    Jesus and Sampaio's SBMF 2022 paper    |
            |                     and                   |
            |    Jesus and Sampaio's SCP 2023 paper     |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory tockCSP_Proof_Rule1
imports tockCSP_F
begin



subsection \<open> Roscoe Rule to check timestops using stable-failures model \<close>

text \<open> WARNING: Well Timedness (Zeno Behaviour) IS NOT checked using this
                rule because we are NOT using failures-divergences model. \<close>

theorem Rule_check_timestops_Roscoe :
    "FPmode \<noteq> CPOmode \<Longrightarrow> X \<noteq> {} \<Longrightarrow>
    P =F ? x:X \<rightarrow> Pfx x \<Longrightarrow>
    \<forall>x\<in>X. $TOCKS <=F (Pfx x -- (UNIV - {tock})) \<Longrightarrow>
    $TOCKS <=F (P -- (UNIV - {tock}))"

  apply (rule cspF_rw_right, rule cspF_decompo, simp, simp)
  apply (cspF_step_right)

  apply (case_tac "{tock} \<subset> X")

  apply (rule cspF_rw_right, rule cspF_IF_split, simp)
  apply (rule)
  apply (rule, force)
  apply (rule, simp add: Diff_eq)
    apply (rule cspF_Timeout_right)
      apply (cspF_unwind_left)
      apply (cspF_step_left)
      apply (rule cspF_decompo, force, simp)
      apply (rule cspF_Rep_int_choice_right, simp)

  apply (simp add: psubset_eq Int_def)
  apply (case_tac "tock \<in> X")
    apply (simp, drule sym, simp)
    apply (cspF_simp_right)
    apply (cspF_unwind_left)
    apply (cspF_step_left)
    apply (rule cspF_decompo, simp, simp)

    apply (rule cspF_rw_right, rule cspF_IF_split, simp)
    apply (rule, force)
    apply (rule, simp add: Diff_eq)
      apply (cspF_step_right)
      apply (cspF_step_right)
      apply (cspF_step_right)
      apply (rule cspF_Rep_int_choice_right, simp)
done


(* previous (and more restrictive) proof assumes X always has tock
lemma Rule_tock_proc_Roscoe :
    "FPmode \<noteq> CPOmode \<Longrightarrow> {tock} \<subset> X \<Longrightarrow>
    P =F ? x:X \<rightarrow> Pfx x \<Longrightarrow>
    \<forall>x\<in>X. $TOCKS <=F (Pfx x -- (UNIV - {tock})) \<Longrightarrow>
    $TOCKS <=F (P -- (UNIV - {tock}))"

  apply (rule cspF_rw_right, rule cspF_decompo, simp, simp)
  apply (cspF_step_right)

  apply (rule cspF_rw_right, rule cspF_IF_split, simp)
  apply (rule)
  apply (rule)
  apply (force)
  apply (rule)

  apply (rule cspF_Timeout_right)
    apply (cspF_unwind_left)
    apply (cspF_step_left)
  apply (rule cspF_decompo, force, simp)

  apply (rule cspF_Rep_int_choice_right, simp)
done*)

lemma Rule_check_timestops_Roscoe_TOCKSTick :
    "FPmode \<noteq> CPOmode \<Longrightarrow> X \<noteq> {} \<Longrightarrow>
    P =F ? x:X \<rightarrow> Pfx x \<Longrightarrow>
    \<forall>x\<in>X. $TOCKSTick <=F (Pfx x -- (UNIV - {tock})) \<Longrightarrow>
    $TOCKSTick <=F (P -- (UNIV - {tock}))"

  apply (rule cspF_rw_right, rule cspF_decompo, simp, simp)
  apply (cspF_step_right)

  apply (case_tac "{tock} \<subset> X")

  apply (rule cspF_rw_right, rule cspF_IF_split, simp)
  apply (rule)
  apply (rule, force)
  apply (rule, simp add: Diff_eq)
    apply (rule cspF_Timeout_right)
      apply (cspF_unwind_left)
      apply (cspF_step_left)
      apply (rule cspF_Int_choice_left1)
      apply (rule cspF_decompo, force, simp)
      apply (rule cspF_Rep_int_choice_right, simp)

  apply (simp add: psubset_eq Int_def)
  apply (case_tac "tock \<in> X")
    apply (simp, drule sym, simp)
    apply (cspF_simp_right)
    apply (cspF_unwind_left)
    apply (cspF_step_left)
    apply (rule cspF_Int_choice_left1)
    apply (rule cspF_decompo, simp, simp)

    apply (rule cspF_rw_right, rule cspF_IF_split, simp)
    apply (rule, force)
    apply (rule, simp add: Diff_eq)
      apply (cspF_step_right)
      apply (cspF_step_right)
      apply (cspF_step_right)
      apply (rule cspF_Rep_int_choice_right, simp)
done



subsection \<open> STOP is NOT a valid tockCSP Process \<close>


theorem not_check_timestops_STOP :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    \<not> $TOCKS <=F (STOP -- (UNIV - {tock}))"
  apply (rule)
  apply (simp add: cspF_semantics)
  apply (simp add: traces_iff)
  apply (simp add: failures_TOCKS)
  apply (simp add: failures_iff)
  apply (auto)
  apply (erule_tac x="<>" in allE)
  apply (erule_tac x="{Tock}" in allE)
  apply (simp add: CollectF_open_memF STOP_setF)
  apply (simp add: CollectF_open_memF Act_prefix_setF)
  done

lemmas not_tockCSP_STOP = not_check_timestops_STOP




subsection \<open> SKIP is a valid tockCSP Process \<close>


theorem check_timestops_SKIP :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    $TOCKSTick <=F ((SKIP:: (TOCKSTickPN,'e::tockCSP) proc) -- (UNIV - {tock}))"
  apply (cspF_step)
  apply (cspF_unwind)
  apply (rule cspF_Int_choice_left2, simp)
  done

lemmas tockCSP_SKIP = check_timestops_SKIP





subsection \<open> DIV is a valid tockCSP Process \<close>


theorem check_timestops_DIV :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    $TOCKSTick <=F ((DIV:: (TOCKSTickPN,'e::tockCSP) proc) -- (UNIV - {tock}))"
  apply (cspF_step)
  done

lemmas tockCSP_DIV = check_timestops_DIV


end