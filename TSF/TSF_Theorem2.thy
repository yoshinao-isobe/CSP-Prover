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

theory TSF_Theorem2
imports TSF_TimeStop
begin


section \<open> Lifting Deadlock-free Analysis to tock-CSP \<close>

text \<open> For Theorem 2 in Jesus and Sampaio's SBMF 2022 paper
       see Theorem2_Jesus_Sampaio_2022.
       For Theorem 2 in Jesus and Sampaio's SCP 2023 paper
       see Theorem2_Jesus_Sampaio_2023 that depends on \<^theory>\<open>DFP.DFP_Hiding\<close> \<close>



subsection \<open> Jesus Sampaio's SBMF 2022 paper: TSF & DF -- {tock} --> DF \<close>

theorem DeadlockFree_if_TimeStopFree_DeadlockFree_hiding_tock :
    "S \<subseteq> {Tick} \<Longrightarrow> Tock \<in> X \<Longrightarrow>
     ( ([S]-TimeStopFree P) & ([X]-DeadlockFree (P -- {tock})) )
     ==> ( [X]-DeadlockFree P )"
  apply (elim conjE)
  apply (simp only: TimeStopFree_def)
  apply (simp only: DeadlockFree_def)
  apply (simp add: in_failures hide_tr_sym)
  apply (intro allI impI)

  apply (case_tac "\<exists>t. t =tocks(s)", elim exE, simp_all)
  apply (drule_tac x=t in spec)
  apply (drule mp, simp add: Tick_notin_hide_tr_trans2)

  apply (case_tac "\<exists>nt. nt =nontocks(s)", elim exE, simp_all)
  apply (drule_tac x=nt in spec)
  apply (drule mp, simp add: Tick_notin_hide_tr_trans2)

  apply (drule_tac x=s in spec, simp)
  apply (drule_tac x=s in spec, simp)

  by (simp add: insert_absorb)


lemmas Theorem2_Jesus_Sampaio_2022 = DeadlockFree_if_TimeStopFree_DeadlockFree_hiding_tock



subsection \<open> Jesus Sampaio's SCP 2023 paper: TSF <--> DF \<close>


lemma DeadlockFree_TimeStopFree_only_if :
    "( [X]-DeadlockFree P ) ==> ( [X]-TimeStopFree P )"
  apply (simp only: TimeStopFree_def)
  apply (rule DeadlockFree_Hiding)
  apply (rule DeadlockFree_subset[of _ _ "{Tock}"], simp)
  done


lemma DeadlockFree_TimeStopFree_if :
    "X = EvsetTick \<Longrightarrow>
     ( ([X]-TimeStopFree P) ) ==> ( [X]-DeadlockFree P )"
  apply (simp only: TimeStopFree_def)
  apply (subst Theorem1_Jesus_Sampaio_2023[of Nontock])
  apply (simp add: EvsetTick_def)
  apply (simp add: EvsetTick_def insert_absorb)
  apply (simp add: EvsetTick_def insert_absorb)
  done


theorem TimeStopFree_DeadlockFree_iff :
    "X = EvsetTick \<Longrightarrow>
     ( [X]-DeadlockFree P ) = ( ([X]-TimeStopFree P) )"
  apply (rule)
    apply (simp add: DeadlockFree_TimeStopFree_only_if)
    apply (simp add: DeadlockFree_TimeStopFree_if)
  done

lemmas Theorem2_Jesus_Sampaio_2023 = TimeStopFree_DeadlockFree_iff


corollary Corollary2_Jesus_Sampaio_2023 :
    "(  P isDeadlockFree ) = ( P isTimeStopFree )"
  apply (subst Theorem2_Jesus_Sampaio_2023)
  apply (simp add: EvsetTick_def)
  apply (simp add: TimeStopFree_def)
  apply (simp add: DeadlockFree_def)
  apply (simp add: EvsetTick_def insert_absorb)
  apply (simp add: in_failures EvsetTick_def)
  done



end