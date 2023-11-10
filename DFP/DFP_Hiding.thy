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

theory DFP_Hiding
imports DFP_law
begin


text \<open> P isDeadlockFree = (P -- X) isDeadlockFree \<close>

text \<open> Theorem 1 in Jesus and Sampaio's SCP 2023 paper:
       see Theorem1_Jesus_Sampaio_2023 at the end of this file. \<close>

lemma DeadlockFree_only_if_Hiding :
    "Ev ` X \<subseteq> S \<Longrightarrow>
     [S]-DeadlockFree (P -- X) \<Longrightarrow> [S]-DeadlockFree P"
  apply (erule contrapos_pp)
  apply (erule contrapos_pp)
  apply (simp add: DeadlockFree_def)
  apply (simp add: in_failures)
  apply (elim exE conjE)
  apply (rule_tac x="s --tr X" in exI)
  apply (simp)
  apply (rule_tac x="s" in exI)
  apply (simp)
  apply (rule memF_F2, simp, fast)
done


lemma isDeadlockFree_only_if_Hiding :
    "(P -- X) isDeadlockFree \<Longrightarrow> P isDeadlockFree"
by (simp add: DeadlockFree_only_if_Hiding[of X])


theorem DeadlockFree_Hiding_iff :
    "Ev ` A \<subseteq> X \<Longrightarrow> Tick \<in> X \<Longrightarrow>
     [X]-DeadlockFree P = [X]-DeadlockFree (P -- A)"
  apply (intro iffI)
    apply (simp add: DeadlockFree_Hiding)
    apply (simp add: DeadlockFree_only_if_Hiding)
done

lemmas Theorem1_Jesus_Sampaio_2023 = DeadlockFree_Hiding_iff


theorem isDeadlockFree_Hiding_iff :
    "P isDeadlockFree = (P -- X) isDeadlockFree"
  by (rule DeadlockFree_Hiding_iff, simp_all)


end