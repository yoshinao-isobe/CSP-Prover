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




subsection \<open> DFP Network \<close>

subsubsection \<open> unfolded lemmas for DeadlockFreeNetwork \<close>


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





subsubsection \<open> hide_tr isStateOf \<close>
(* TODO?: move these lemmas to DFP_Network *)


lemma hide_tr_Compl_isStateOf_subset: 
    "[| (t,Yf) isStateOf (I,FXf) ; J <= I ; 
        X = {sY. EX i:J. sY : snd (FXf i)} |]
    ==> (t --tr (- X), Yf) isStateOf (J, FXf)"
  apply (simp add: isStateOf_def ALP_def)
  apply (rule conjI)
  apply (insert rest_tr_subset_event[of t "X"])
  apply (subgoal_tac "Tick ~: sett (t --tr (- X))")
  apply (force)
  apply (force)
  
  apply (rule ballI)
  apply (elim conjE)
  apply (drule_tac x="i" in bspec, fast)
  
  apply (simp add: rest_tr_def)
  
  apply (subgoal_tac "snd (FXf i) <= {sY. EX i:J. sY : snd (FXf i)}")
  apply (simp add: hide_tr_of_hide_tr_subset)
  by (auto)


lemma hide_tr_Compl_isStateOf_subsetI:
    "[| (t,Yf) isStateOf (I,FXf) ; 
        J <= I ; X = Union {(snd (FXf i))|i. i:J} |]
    ==> (t --tr (- X), Yf) isStateOf (J, FXf)"
  apply (subgoal_tac "Union {(snd (FXf i))|i. i:J} = {sY. EX i:J. sY : snd (FXf i)}")
  apply (simp add: hide_tr_Compl_isStateOf_subset)
  by (auto)



subsubsection \<open> refusals \<close>
(* TODO: move these lemmas to DFP_Blocked *)


lemma in_refusals_if_isDeadlockStateOf :
    "sigma isDeadlockStateOf VF ==>
     i : fst VF ==> j : fst VF ==> i \<noteq> j ==>
     x : Ev ` snd (snd VF i) Int Ev ` snd (snd VF j) ==>
     x : Union {snd sigma i |i. i : fst VF}"
  apply (simp add: isDeadlockStateOf_def)

  apply (simp add: isStateOf_def)
  apply (simp add: ALP_def)
  apply (simp add: image_iff)
  apply (elim conjE bexE, simp)
  
  apply (rule_tac x="i" in bexI)
  apply (simp, simp)
  done


lemma refusals_are_subsets_if_isStateOf :
    "sigma isStateOf VF ==>
     ALL i: fst VF. snd sigma i <= (Ev ` (snd (snd VF i)))"
  apply (simp add: isStateOf_def)
  done

lemma refusals_are_subsets_if_isDeadlockStateOf :
    "sigma isDeadlockStateOf VF ==>
     ALL i: fst VF. snd sigma i <= (Ev ` (snd (snd VF i)))"
  apply (simp only: isDeadlockStateOf_def, elim conjE)
  apply (rule refusals_are_subsets_if_isStateOf, simp)
  done


lemma Union_refusals_ALP_if_isDeadlockStateOf :
    "sigma isDeadlockStateOf (I, FXf) \<Longrightarrow>
    Union {snd sigma i |i. i : I} = Ev ` ALP (I,FXf)"
  by (simp add: isDeadlockStateOf_def ALP_def)


subsubsection \<open> DFP Blocked \<close>
(* TODO: move these lemmas refactoring DFP_Blocked *)


lemma refusals_neq_ALP_if_not_isDeadlockStateOf :
    "(t, Yf) isStateOf (I, FXf) \<Longrightarrow>
     i : I ==>
     ~ (t rest-tr snd (FXf i), Yf) isDeadlockStateOf ({i}, FXf) \<Longrightarrow>
     Yf i ~= Ev ` snd (FXf i)"
  apply (simp add: isDeadlockStateOf_def)
  apply (drule isStateOf_each_element, simp, simp)
  by (simp add: ALP_def)


(* i is not refusing event a from its synchronisation set *)
lemma ex_non_refused_event_if_isStateOf :
     "(t, Yf) isStateOf (I, FXf) \<Longrightarrow>
      i : I ==> Yf i ~= Ev ` snd (FXf i) ==>
      EX a : Ev ` snd (FXf i). a ~: Yf i"
  apply (frule refusals_are_subsets_if_isStateOf)
  apply (frule isStateOf_each_element, simp, simp)
  by (fast)


lemma ex_target_for_Request :
    "(t, Yf) isStateOf (I, FXf) ==>
     Union {Yf i |i. i : I} = Ev ` {a. EX i:I. a : snd (FXf i)} ==>
     i : I ==> Yf i ~= Ev ` snd (FXf i) ==>
     EX j. (I, FXf) >> i --[(t, Yf)]--> j"
  apply (simp add: isRequestOf_def)

  apply (frule refusals_are_subsets_if_isStateOf)

  (* i is not refusing event a from its synchronisation set *)
  apply (frule ex_non_refused_event_if_isStateOf[of t Yf I FXf i], simp_all, elim bexE)

  apply (subgoal_tac "Ev a : Ev ` {a. EX i:I. a : snd (FXf i)}")
                                                  (* ... sub 1 *)
  apply (rotate_tac 1)
  apply (drule sym)
  apply (simp)
  apply (elim conjE exE)
  apply (simp)
  apply (rule_tac x="ia" in exI)
  apply (case_tac "i = ia", simp)
  apply (simp)
  apply (drule_tac x="ia" in bspec, simp)
  apply (blast)

  (* sub 1 *)
  apply (blast)
  done



lemma ex_Request_if_isDeadlockStateOf_BusyNetwork :
    "(t, Yf) isDeadlockStateOf (I, FXf) ==> BusyNetwork (I, FXf) ==>
     i : I ==>
     EX j. (I, FXf) >> i --[(t, Yf)]--> j"
  apply (frule isStateOf_if_isDeadlockStateOf)

  apply (rule ex_target_for_Request, simp_all)

    (* refusing ALL events *)
    apply (frule Union_refusals_ALP_if_isDeadlockStateOf, simp add: ALP_def)

    (* busy --> i is deadlock-free *)
    apply (simp only: BusyNetwork_def)

    (* State of i *)
    apply (drule_tac x="i" in bspec, simp)
    apply (drule_tac x="(t rest-tr (snd (FXf i)), Yf)" in spec)
    apply (frule refusals_neq_ALP_if_not_isDeadlockStateOf[of t Yf I FXf i], simp_all)
  done

end