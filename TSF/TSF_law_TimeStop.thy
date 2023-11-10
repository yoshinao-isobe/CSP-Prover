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

theory TSF_law_TimeStop
imports TSF_TimeStop
begin


lemma TimeStopFree_subset :
    "[X]-TimeStopFree P \<Longrightarrow> [X \<union> Y]-TimeStopFree P"
  apply (simp only: TimeStopFree_def)
  apply (subst Un_commute)
  apply (subst Un_assoc)
  apply (subst Un_commute)
  apply (rule DeadlockFree_subset, simp)
  done

lemma TimeStopFree_minimal :
    "[{}]-TimeStopFree P \<Longrightarrow> [X]-TimeStopFree P"
by (frule_tac X="{}" in TimeStopFree_subset, simp)



subsection \<open> checking BASIC untimed CSP Processes \<close>



lemma not_STOP_TimeStopFree_maximal :
    "~ [X]-TimeStopFree STOP"
  apply (simp only: TimeStopFree_def)
  apply (simp only: DeadlockFree_def)
  apply (simp add: in_failures)
  done

lemma not_STOP_isTimeStopFree:
    "\<not> STOP isTimeStopFree"
  by (simp add: not_STOP_TimeStopFree_maximal)



lemma SKIP_TimeStopFree_maximal :
    "Tick \<in> X \<Longrightarrow>
     [X]-TimeStopFree SKIP"
  apply (simp only: TimeStopFree_def)
  apply (simp only: DeadlockFree_def)
  apply (simp add: in_failures)
  apply (force)
  done

lemma SKIP_isTimeStopFree:
    "SKIP isTimeStopFree"
  by (simp add: SKIP_TimeStopFree_maximal)



lemma DIV_TimeStopFree_maximal :
    "[X]-TimeStopFree DIV"
  apply (simp only: TimeStopFree_def)
  apply (simp only: DeadlockFree_def)
  apply (simp add: in_failures)
  done

lemma DIV_isTimeStopFree:
    "DIV isTimeStopFree"
  by (simp add: DIV_TimeStopFree_maximal)




subsection \<open> checking TOCKS and TOCKSTick Processes \<close>


lemma TOCKS_isTimeStopFree:
    "(($TOCKS) :: (TOCKSPN, 'event::tockCSP) proc) isTimeStopFree"
  apply (simp add: TimeStopFree_def DeadlockFree_def)

  apply (rule allI)
  apply (induct_tac s rule: induct_trace)
  
  (* <> *)
  apply (simp add: in_failures_Hiding)
  apply (simp add: in_failures_TOCKS)
  apply (force)

  (* <Tick> *)
  apply (simp)

  (* <Ev a> ^^^ sa *)
  apply (intro impI, simp)
  apply (simp add: in_failures_Hiding)
  apply (subst failures_TOCKS_to_TOCKSfun, simp)
  apply (simp add: in_failures)

  apply (clarsimp)
  done



lemma TOCKSTick_isTimeStopFree:
    "(($TOCKSTick) :: (TOCKSTickPN, 'event::tockCSP) proc) isTimeStopFree"
  apply (simp add: TimeStopFree_def DeadlockFree_def)

  apply (rule allI)
  apply (induct_tac s rule: induct_trace)
  
  (* <> *)
  apply (simp add: in_failures_Hiding)
  apply (simp add: in_failures_TOCKSTick)
  apply (force)

  (* <Tick> *)
  apply (simp)

  (* <Ev a> ^^^ sa *)
  apply (intro impI, simp)
  apply (simp add: in_failures_Hiding)
  apply (subst failures_TOCKSTick_to_TOCKSTickfun, simp)
  apply (simp add: in_failures)

  apply (clarsimp)
  apply (rule)
  apply (clarsimp)

  apply (force)
  done





end