theory TSF_law_TimeStop
imports TSF_TimeStop
begin



subsection \<open> checking BASIC untimed CSP Processes \<close>


lemma not_STOP_isTimeStopFree:
    "\<not> STOP isTimeStopFree"
  apply (simp add: TimeStopFree_def DeadlockFree_def)
  apply (simp add: in_failures)
  done


lemma SKIP_isTimeStopFree:
    "SKIP isTimeStopFree"
  apply (simp add: TimeStopFree_def DeadlockFree_def)
  apply (simp add: in_failures)
    apply (force)
  done


lemma DIV_isTimeStopFree:
    "DIV isTimeStopFree"
  apply (simp add: TimeStopFree_def DeadlockFree_def)
  apply (simp add: in_failures)
  done





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