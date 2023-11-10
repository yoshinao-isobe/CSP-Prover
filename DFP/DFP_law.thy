           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 2022 / 2023               |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_law
imports DFP_law_DF
        DFP_law_DFtickA
        DFP_law_DFnonTick
        DFP_law_DFkev
begin


lemma Tick_DeadlockFree_if_DeadlockFree :
    "[X]-DeadlockFree P \<Longrightarrow> [X \<union> {Tick}]-DeadlockFree P"
  apply (simp add: DeadlockFree_def)
  apply (rule, rule)
    apply (drule_tac x=s in spec, simp)
    apply (rotate_tac 1)
    apply (erule contrapos_nn)
    apply (erule memF_F2, force)
    done

end