theory TSF_Network
imports TSF_Blocked
        TSF_law
begin


subsection \<open> TimeStopFreeNetwork \<close>


definition TimeStopFreeNetwork :: "('i,'p,'e::tockCSP) Network => bool" 
where
  "TimeStopFreeNetwork V == isTockNet V &
                            [Ev ` (ALP V)]-TimeStopFree (PAR V)"


(*definition TimeStopDeadlockFreeNetwork :: "('i,'p,'e::tockCSP) Network => bool" 
where
  "TimeStopDeadlockFreeNetwork V == TimeStopFreeNetwork V &
                                    DeadlockFreeNetwork (V -- {tock})*)


(*
lemma TimeStopFree_PAR_iff_DeadlockFree_PAR_TockNet :
    "[Ev ` (ALP V)]-TimeStopFree (PAR V) =
     [Ev ` (ALP V) \<union> {Tick,Tock}]-DeadlockFree ((PAR V) -- Nontock)"
  by (simp add: TimeStopFree_def)
*)


lemma TimeStopFreeNetwork_iff_DeadlockFree_PAR_Nontock :
    "fst V \<noteq> {} \<Longrightarrow> isTockNet V \<Longrightarrow>
     TimeStopFreeNetwork V = [Ev ` (ALP V) \<union> {Tick}]-DeadlockFree ((PAR V) -- Nontock)"
  apply (subst Tock_in_Ev_ALP_if_isTockNet_V, simp, simp)
  apply (simp add: TimeStopFreeNetwork_def TimeStopFree_def)
  done


lemma not_TimeStopFreeNetwork_iff_DeadlockFreeNetwork :
    "fst V \<noteq> {} \<Longrightarrow> isTockNet V \<Longrightarrow>
     TimeStopFreeNetwork V ~= DeadlockFreeNetwork V"
  apply (simp add: DeadlockFreeNetwork_def)
  apply (subst TimeStopFreeNetwork_iff_DeadlockFree_PAR_Nontock, simp, simp)
  apply (rule)
defer
    apply (rule DeadlockFree_Hiding)
    apply (subst Tick_DeadlockFree_if_DeadlockFree)
  oops



subsection \<open> TimeStopState \<close>


(*********************************************************
           isTimeStopStateOf subset alpha
 *********************************************************)

lemma isTimeStopStateOf_subset_alpha1:
     "[| (I, FXf) isFailureOf (I, PXf) ; 
         (t, Yf) isTimeStopStateOf (I, FXf) ;
         i : I ; e : Yf i|]
      ==> e : (Ev ` (snd (PXf i)))"
  apply (simp only: isTimeStopStateOf_def, elim conjE)
  by (simp add: isStateOf_subset_alpha1)


lemma isTimeStopStateOf_subset_alpha2:
     "[| (I, FXf) isFailureOf (I, PXf) ; 
         (t, Yf) isTimeStopStateOf (I, FXf) ;
         i : I ; e : Yf i|]
      ==> e : (Ev ` (snd (FXf i)))"
  apply (simp only: isTimeStopStateOf_def, elim conjE)
  by (simp add: isStateOf_subset_alpha2)

lemmas isTimeStopStateOf_subset_alpha = isTimeStopStateOf_subset_alpha1
                                        isTimeStopStateOf_subset_alpha2


(*********************************************************
             TimeStop and TimeStop freedom
 *********************************************************)

(*** Existency ***)

lemma TimeStopState_notTimeStopFree_only_if_lmEX:
     "[| isTockNet (I, PXf) ; (I, FXf) isFailureOf (I, PXf) ;
         ALL i:I. (s rest-tr (snd (PXf i)), Yf i) :f failures (fst (PXf i)) MF |]
      ==>
      EX Zf. ALL i:I. (s rest-tr (snd (FXf i)), Zf i) : fst (FXf i) &
                      Yf i Int (Ev ` snd (FXf i) \<union> {Tock}) <= Zf i &
                      Zf i <= (Ev ` snd (FXf i) \<union> {Tock})"
   apply (rule_tac x="(%i. (SOME Z. (s rest-tr (snd (FXf i)), Z) : fst (FXf i) &
                                     Yf i Int (Ev ` snd (FXf i) \<union> {Tock}) <= Z &
                                     Z <= (Ev ` snd (FXf i) \<union> {Tock})))" in exI)
  apply (intro ballI impI)
  apply (simp add: isFailureOf_def)
  apply (drule_tac x="i" in bspec, simp)
  apply (drule_tac x="i" in bspec, simp)
  apply (simp add: subseteqEX_restRefusal_iff)
  apply (elim conjE exE)
  apply (rotate_tac -2)
  
  apply (drule_tac x="s rest-tr snd (FXf i)" in spec)
  apply (drule_tac x="Yf i" in spec)
  apply (simp)
  apply (elim conjE exE)
  apply (rule DeadlockState_notDeadlockFree_only_if_lmEX_lm)
  apply (simp_all)
  apply (force)
  done

(* only if part *)

lemma in_failures_Inductive_parallel_map :
    "finite I \<Longrightarrow> x \<noteq> [] \<Longrightarrow>
     (s, X) :f failures ([||] map PXf x) MF =
     (sett s \<subseteq> insert Tick (Ev ` (\<Union>a\<in>set x. snd (PXf a))) \<and>
      (\<exists>PXYs. map fst PXYs = map PXf x \<and>
              X \<inter> insert Tick (Ev ` (\<Union>a\<in>set x. snd (PXf a))) =
                  \<Union> {Y \<inter> insert Tick (Ev ` X) |X Y. \<exists>P. ((P, X), Y) \<in> set PXYs} \<and>
              (\<forall>P X Y. ((P, X), Y) \<in> set PXYs \<longrightarrow> (s rest-tr X, Y) :f failures P MF)))"
  apply (simp)
  by (subst in_failures_Inductive_parallel, simp_all)




lemma TimeStopState_notTimeStopFree_only_if:
    "[| isTockNet (I,PXf) ; I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) ;
        ~ TimeStopFreeNetwork (I,PXf) |]
     ==> (EX sigma. (sigma isTimeStopStateOf (I,FXf)))"
  apply (frule isTockNet_FXf_if_isTockNet_PXf, simp)

  apply (simp only: isTimeStopStateOf_def Union_iff)
  apply (simp add: TimeStopFreeNetwork_def)
  apply (simp add: TimeStopFree_def)

  apply (simp add: DeadlockFree_def)
  apply (simp add: in_failures (*hide_tr_sym*), elim exE conjE)

  apply (rule_tac x=s in exI)
  apply (rule_tac x="\<lambda>i. {Tock}" in exI)
  apply (rule)
defer
  apply (force)

  apply (simp)
  apply (rule hide_tr_Compl_isStateOf_subsetI[of _ _ I], simp_all)

(*
  apply (simp only: isStateOf_def conj_assoc ex_simps)
  apply (simp)

  apply (frule hide_tr_non_x_sett)
  apply (rule)
    apply (simp add: subset_doubleton_iff, elim disjE, simp_all)
    apply (simp add: Tock_in_Ev_ALP_if_isTockNet)

  apply (rule)

  apply (simp add: PAR_def Rep_parallel_def)
  apply (frule_tac s=sa and X=EvsetTick and PXf=PXf in
         in_failures_Inductive_parallel_map[of I "(SOME Is. Is isListOf I)"])
    apply (rule someI2_ex, rule isListOf_EX, simp)
    apply (frule isListOf_nonemptyset[of I], simp, simp)
    apply (simp)
  apply (elim conjE exE)
  apply (simp add: set_SOME_isListOf)

  apply (frule isFailureOf_same_alpha)
  apply (rotate_tac -1, simp)
  apply (rotate_tac -1)
  apply (drule_tac x="fst (PXf i)" in spec)
  apply (rotate_tac -1)
  apply (drule_tac x="snd (PXf i)" in spec)
  apply (rotate_tac -1)
  apply (drule_tac x="{Tock}" in spec, simp)

  apply (simp add: isFailureOf_def subseteqEX_restRefusal_iff)
  apply (rotate_tac 3)
  apply (drule_tac x="i" in bspec, simp, elim conjE)

  apply (rotate_tac -1)
  apply (drule_tac x="s rest-tr snd (FXf i)" in spec, simp)
  apply (rotate_tac -1)
  apply (drule_tac x="{Tock}" in spec, simp)
  apply (clarify)
*)
  sorry


(*** if part ***)

lemma TimeStopState_notTimeStopFree_if:
    "[| isTockNet (I,FXf) ; I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) ;
        EX sigma. (sigma isTimeStopStateOf (I,FXf)) |]
     ==> ~ TimeStopFreeNetwork (I,PXf)"
  apply (simp only: isTimeStopStateOf_def, simp only: ex_simps)

  apply (erule conjE)
  apply (simp add: isDeadlockStateOf_def)

  apply (frule DeadlockState_notDeadlockFree_if, simp, simp, simp)

  apply (frule isTockNet_PXf_if_isTockNet_FXf, simp)
  apply (subst TimeStopFreeNetwork_iff_DeadlockFree_PAR_Nontock, simp_all)

  apply (rotate_tac 2)
  apply (erule contrapos_nn)

  apply (simp add: DeadlockFreeNetwork_def)
  apply (rule DeadlockFree_Hiding, simp)
  oops


lemma TimeStopState_notTimeStopFree_if:
    "[| isTockNet (I, PXf) ; I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) ;
        EX sigma. (sigma isTimeStopStateOf (I,FXf)) |]
     ==> ~ TimeStopFreeNetwork (I,PXf)"

  apply (simp add: TimeStopFreeNetwork_def)
  apply (simp add: TimeStopFree_def)
  apply (simp add: isTimeStopStateOf_def)

  apply (elim conjE exE)
  apply (simp add: PAR_def)
  
  apply (rule_tac x="a" in exI)
  apply (simp add: in_failures_par)
  apply (simp add: isStateOf_def ALP_def)
  
  apply (elim conjE exE)
  apply (rule conjI)
  apply (fas)
  apply (rule conjI)
  
  apply (rule order_trans)
  apply (simp)
  apply (simp add: isFailureOf_def)
  apply (fas)
  
  apply (rule_tac x="b" in exI)
  apply (rename_tac s Ys)
  apply (drule sym)
  apply (simp)
  apply (subgoal_tac "Union (snd ` PXf ` I) = {a. EX i:I. a : snd (PXf i)}")
  apply (simp add: Int_insert_eq)
  apply (rule conjI)
   apply (rule)
  
   (* <= *)
    apply (rule)
     apply (simp add: image_iff)
     apply (elim conjE exE bexE)
     apply (simp)
     apply (subgoal_tac "x : Ev ` {a. EX i:I. a : snd (FXf i)}")
  
      apply (simp)
      apply (elim conjE exE)
      apply (rule_tac x="Ys ia Int insert Tick (Ev ` snd (PXf ia))" in exI)
      apply (rule conjI)
      apply (fas)
  
      apply (simp)
      apply (drule_tac x="ia" in bspec, simp)
      apply (simp add: isFailureOf_same_alpha)
      apply (blas)
  
     apply (simp (no_asm) add: image_iff)
     apply (rule_tac x="xa" in exI)
     apply (simp add: isFailureOf_def)
     apply (forc)
  
   (* => *)
    apply (rule)
     apply (simp)
     apply (elim conjE exE)
     apply (simp add: image_iff)
     apply (elim disjE conjE exE)
      apply (drule_tac x="i" in bspec, simp)
      apply (forc)
  
      apply (elim conjE bexE)
      apply (rule_tac x="xb" in exI, simp)
      apply (rule_tac x="i" in bexI)
      apply (simp)
      apply (simp)
  
  apply (intro ballI)
  apply (simp add: isFailureOf_def)
  apply (simp add: subseteqEX_restRefusal_iff)
  
  apply (aut)
  done

(*** iff ***)

lemma notTimeStopFreeNetwork_iff_TimeStopState:
    "[| isTockNet (I,PXf) ; I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) |]
     ==> (~ TimeStopFreeNetwork (I,PXf)) =
         (EX sigma. (sigma isTimeStopStateOf (I,FXf)))"
  apply (rule)
  apply (rule TimeStopState_notTimeStopFree_only_if, simp_all)
  apply (simp add: TimeStopState_notTimeStopFree_if)
  done

(*** TimeStopFree ***)

lemma TimeStopFreeNetwork_iff_notTimeStopState:
    "[| isTockNet (I,PXf) ; I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) |]
     ==> TimeStopFreeNetwork (I,PXf) = 
         (ALL sigma. ~(sigma isTimeStopStateOf (I,FXf)))"
  apply (rule iffI)
  apply (rotate_tac -1)
  apply (erule contrapos_pp)
  apply (simp add: notTimeStopFreeNetwork_iff_TimeStopState)
  apply (rotate_tac -1)
  apply (erule contrapos_pp)
  apply (simp add: notTimeStopFreeNetwork_iff_TimeStopState)
  done





subsection \<open> DeadlockFree_notDeadlockState expansions \<close>


lemma TEST_unfolded_DeadlockFree_PAR_Hiding_notDeadlockState:
  "[| isTockNet (I,PXf) ; I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) |]
   ==> (\<forall>s. Tick \<notin> sett s \<longrightarrow> (s, Ev ` ALP (I, PXf)) ~:f failures ((PAR (I, PXf)) -- Nontock) MF) = 
       (ALL sigma. ~(sigma isNonTockDeadlockStateOf (I,FXf)))"

  apply (simp add: in_failures_Hiding hide_tr_sym)
  apply (subst NonTickTockEv_Un_eq_Evset_Un_if)
    apply (simp add: ALP_def image_def)
    apply (insert ex_in_conv[of I], simp)
  apply (subst Evset_Un_image)

  apply (clarsimp)

  apply (simp only: isNonTockDeadlockStateOf_def)

  apply (simp)
  apply (rule)
    apply (rule, rule, rule)

  apply (insert DeadlockState_notDeadlockFree[of I FXf PXf], simp_all)
  apply (erule iffE)
    apply (erule impE, fast)
    apply (erule impE, fast)
  apply (simp add: DeadlockFreeNetwork_def)
  apply (simp add: DeadlockFree_def, elim exE conjE)
  apply (drule_tac x=s in spec, simp)
  apply (drule_tac x=s in spec)
  apply (simp only: imp_conv_disj)

  oops



lemma TEST_unfolded_Tick_DeadlockFree_PAR_Hiding_notDeadlockState:
  "[| isTockNet (I,PXf) ; I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) |]
   ==> (\<forall>s. Tick \<notin> sett s \<longrightarrow> (s, Ev ` ALP (I, PXf) Un {Tick}) ~:f failures ((PAR (I, PXf)) -- Nontock) MF) = 
       (ALL sigma. ~(sigma isNonTockDeadlockStateOf (I,FXf)))"

  apply (simp add: in_failures_Hiding hide_tr_sym)
  apply (simp only: insert_Tick_NonTickTockEv_Un)
  apply (subst NonTockEv_Un_eq_EvsetTick_if)
    apply (simp add: ALP_def image_def)
    apply (insert ex_in_conv[of I], simp)

  apply (clarsimp)
  apply (simp add: isNonTockDeadlockStateOf_def)

  apply (insert DeadlockFree_notDeadlockState[of I FXf PXf], simp_all)
  apply (simp add: DeadlockFreeNetwork_def)
  apply (simp add: DeadlockFree_def)

  apply (simp only: not_ex[THEN sym], simp)

  sorry




lemma unfolded_DeadlockFree_PAR_Hiding_notDeadlockState:
  "[| isTockNet (I,PXf) ; I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) |]
   ==> (\<forall>s. Tick \<notin> sett s \<longrightarrow> (s, Ev ` ALP (I, PXf) Un {Tick}) ~:f failures ((PAR (I, PXf)) -- Nontock) MF) = 
       (ALL sigma. ~(sigma isNonTockDeadlockStateOf (I,FXf)))"

  apply (frule isTockNet_FXf_if_isTockNet_PXf, simp)
  apply (subst ALP_PXf_iff_ALP_FXf_if_isFailureOf, simp)

  apply (rule)

  apply (simp only: isNonTockDeadlockStateOf_def)
  apply (simp add: in_failures_Hiding hide_tr_sym)
  apply (clarsimp)
      apply (simp add: isDeadlockStateOf_def)
      apply (simp add: isTimeStopStateOf_def, elim conjE)
      apply (drule sym)
      apply (simp)
      apply (insert ex_in_conv[of I], simp, elim exE)
      apply ()


      apply (drule_tac x="sa" in spec)
      apply (drule_tac x="\<lambda>i. Evset" in spec)
    apply (frule isTockNetObj_FXf_if_isTockNetObj_PXf, simp)

      apply (drule mp)
      apply (simp add: isDeadlockStateOf_def)
      apply (simp add: Union_constant image_def)
      apply (simp add: isStateOf_def ALP_def)
      apply (insert ex_in_conv[of I], simp, elim exE)
defer
      apply (simp add: isTimeStopStateOf_def, elim conjE exE)
      apply (simp add: isStateOf_def ALP_def, elim conjE)
      apply (drule_tac x="x" in bspec, simp)
      apply (drule_tac x="x" in bspec, simp, elim conjE)
      apply (simp add: Evset_def image_def subset_iff)
      apply (simp add: isFailureOf_def)
      apply (drule_tac x="x" in bspec, simp)

      apply (simp add: PAR_def Rep_parallel_def)
      apply (rule someI2_ex, rule isListOf_EX, simp)
      apply (frule isListOf_nonemptyset[of I], simp)
      apply (simp add: in_failures_Inductive_parallel)
      apply (rule, rule, rule, rule)

      apply (clarsimp)


      apply (insert ex_in_conv[of I], simp, elim exE)
      apply (simp add: isDeadlockStateOf_def isStateOf_def ALP_def)
      apply (simp add: isFailureOf_def)
(*
    apply (rotate_tac 4)
    apply (erule contrapos_pn)
    apply (simp)
    apply (simp only: imp_conv_disj)
      apply (drule_tac x="sa" in spec)
      apply (drule_tac x="\<lambda>i. EvsetTick" in spec)
    apply (simp add: isDeadlockStateOf_def Union_constant)
    apply (simp add: EvsetTick_neq_Ev_image)*)
  sorry
  (*TODO: finish unfolded_DeadlockFree_PAR_Hiding_notDeadlockState *)


end