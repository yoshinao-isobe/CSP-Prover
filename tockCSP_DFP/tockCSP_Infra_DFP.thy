theory tockCSP_Infra_DFP
imports tockCSP_F.tockCSP_Infra_CSP_F
        DFP
begin


subsection \<open> DFP \<close>


lemma DeadlockFree_Hiding :
    "[X]-DeadlockFree P \<Longrightarrow> [X]-DeadlockFree (P -- R)"
  apply (simp add: DeadlockFree_def)
  apply (simp add: in_failures in_traces)
  apply (rule allI, rule impI)
  apply (rule allI)
  apply (erule_tac x="sa" in allE)
  apply (rule, simp)
  by (erule non_memF_F2, simp)


lemma Tick_DeadlockFree_if_DeadlockFree :
    "[X]-DeadlockFree P \<Longrightarrow> [X \<union> {Tick}]-DeadlockFree P"
  apply (simp add: DeadlockFree_def)
  apply (rule, rule)
    apply (drule_tac x=s in spec, simp)
    apply (rotate_tac 1)
    apply (erule contrapos_nn)
    apply (erule memF_F2, force)
    done



lemma isStateOf_if_isDeadlockStateOf :
    "(t, Yf) isDeadlockStateOf (I,FXf) \<Longrightarrow>
    (t, Yf) isStateOf (I, FXf)"
  by (simp add: isDeadlockStateOf_def)




subsection \<open> unfolded lemmas for DeadlockFreeNetwork \<close>


lemma unfolded_DeadlockFreeNetwork_notDeadlockState:
  "[| I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) |]
   ==> [Ev ` ALP (I, PXf)]-DeadlockFree PAR (I, PXf) = 
       (ALL sigma. ~(sigma isDeadlockStateOf (I,FXf)))"
  apply (insert DeadlockFree_notDeadlockState[of I FXf PXf])
  by (simp add: DeadlockFreeNetwork_def)


lemma unfolded_DeadlockFree_PAR_notDeadlockState:
  "[| I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) |]
   ==> (\<forall>s. Tick \<notin> sett s \<longrightarrow> (s, Ev ` ALP (I, PXf)) ~:f failures (PAR (I, PXf)) MF) = 
       (ALL sigma. ~(sigma isDeadlockStateOf (I,FXf)))"
  apply (insert DeadlockFree_notDeadlockState[of I FXf PXf])
  apply (simp add: DeadlockFreeNetwork_def)
  by (simp add: DeadlockFree_def)


end