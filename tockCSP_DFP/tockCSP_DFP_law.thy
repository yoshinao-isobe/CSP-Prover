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

theory tockCSP_DFP_law
imports tockCSP_Infra_DFP
begin

subsection \<open> DF and Hiding \<close>

lemma Tock_DeadlockFree_Hiding_if_Tock_DeadlockFree :
    "[{Tock} \<union> X]-DeadlockFree P ==>
     [{Tock} \<union> X]-DeadlockFree (P -- Nontock)"
  by (rule DeadlockFree_Hiding)


lemma DF_UNIV_if_DF_hiding :
    "[X]-DeadlockFree P -- S ==>
     [UNIV]-DeadlockFree P"
  apply (simp add: DeadlockFree_def)
  apply (intro allI impI)
  apply (simp add: in_failures)
  apply (drule_tac x="s --tr S" in spec, simp)
  apply (drule_tac x="s" in spec, simp)
  apply (erule non_memF_F2, simp add: EvsetTick_def)
  done


lemma DF_EvsetTick_if_DF_hiding :
    "[X]-DeadlockFree P -- S ==>
     [EvsetTick]-DeadlockFree P"
  by (simp add: EvsetTick_def DF_UNIV_if_DF_hiding)


lemma insert_Ev_Ev_image_Compl :
    "- {e} ~= {} ==> insert (Ev e) (Ev ` (- {e})) = Evset"
  apply (simp add: Evset_def)
  apply (simp add: image_def)
  apply (rule, force)
  apply (rule, simp)
  by (auto simp only: not_Tick_to_Ev)


lemma DF_Evset_hiding_exception :
    "- {e} ~= {} ==>
     [{Ev e}]-DeadlockFree (P -- (- {e})) \<Longrightarrow>
     [Evset]-DeadlockFree (P)"
  apply (simp add: DeadlockFree_def)
  apply (intro allI impI)
  apply (simp add: in_failures)
  apply (drule_tac x="s --tr (- {e})" in spec, simp)
  apply (drule_tac x="s" in spec, simp)
  apply (simp add: insert_Ev_Ev_image_Compl)
  done


lemma DF_EvsetTick_hiding_exception :
    "- {e} ~= {} ==>
     [{Ev e}]-DeadlockFree (P -- (- {e})) \<Longrightarrow>
     [EvsetTick]-DeadlockFree (P)"
  apply (simp add: DeadlockFree_def)
  apply (intro allI impI)
  apply (simp add: in_failures)
  apply (drule_tac x="s --tr (- {e})" in spec, simp)
  apply (drule_tac x="s" in spec, simp)
  apply (erule non_memF_F2, simp add: EvsetTick_def)
  done


lemma DF_EvsetTick_Tick_hiding_exception :
    "- {e} ~= {} ==>
     [{Ev e,Tick}]-DeadlockFree (P -- (- {e})) \<Longrightarrow>
     [EvsetTick]-DeadlockFree (P)"
  apply (simp add: DeadlockFree_def)
  apply (intro allI impI)
  apply (simp add: in_failures)
  apply (drule_tac x="s --tr (- {e})" in spec, simp)
  apply (drule_tac x="s" in spec, simp)
  apply (erule non_memF_F2, simp add: EvsetTick_def)
  done




lemma tockCSP_DF_Evset_hiding_exception :
    "[{Tock}]-DeadlockFree (P -- Nontock) \<Longrightarrow>
     [Evset]-DeadlockFree (P)"
  by (rule_tac e=tock in DF_Evset_hiding_exception, simp_all)

lemma tockCSP_DF_EvsetTick_hiding_exception :
    "[{Tock}]-DeadlockFree (P -- Nontock) \<Longrightarrow>
     [EvsetTick]-DeadlockFree (P)"
  by (rule_tac e=tock in DF_EvsetTick_hiding_exception, simp_all)
  

lemma Tock_DeadlockFree_if_Tock_DeadlockFree_Hiding1 :
    "[{Tock} \<union> X]-DeadlockFree (P -- Nontock) ==>
     ALL s. (s, {Tock}) :f failures P MF --> (ALL Y. (s, {Tock} \<union> Y) :f failures P MF) ==>
     [{Tock} \<union> X]-DeadlockFree P"
  apply (simp add: DeadlockFree_def)
  apply (simp add: in_failures)
  apply (intro allI impI)

  apply (intro notI)
  apply (frule_tac Y="{Tock}" in memF_F2, simp)

  apply (drule_tac x="s --tr (- {tock})" in spec)
    apply (drule mp, simp)

  apply (drule_tac x="s" in spec)
    apply (drule mp, simp)

  apply (drule_tac x="s" in spec, simp)

  apply (drule_tac x="Evset \<union> X" in spec)

  apply (simp add: insert_absorb)
  done

lemma Tock_DF_DIV :
    "[{Tock} \<union> X]-DeadlockFree DIV"
  apply (rule Tock_DeadlockFree_if_Tock_DeadlockFree_Hiding1)
  apply (simp add: DeadlockFree_def)
  apply (simp add: in_failures)
  apply (simp add: in_failures)
  done


lemma tockCSP_DF_EvsetTick_Tick_hiding_exception :
    "[{Tick,Tock}]-DeadlockFree (P -- Nontock) \<Longrightarrow>
     [EvsetTick]-DeadlockFree (P)"
  by (simp add: DF_EvsetTick_if_DF_hiding)



end