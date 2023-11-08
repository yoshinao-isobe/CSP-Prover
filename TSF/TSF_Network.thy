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

theory TSF_Network
imports tockCSP_Network
        TSF_law
begin


section \<open> TimeStopFreeNetwork \<close>


definition TimeStopFreeNetwork :: "('i,'p,'e::tockCSP) Network => bool" 
where
  "TimeStopFreeNetwork V == isTPN V &
                            [(EvALP V)]-TimeStopFree (PAR V)"


definition SkipTimeStopFreeNetwork :: "('i,'p,'e::tockCSP) Network => bool" 
where
  "SkipTimeStopFreeNetwork V == isTPN V &
                                [(EvALP V) \<union> {Tick}]-TimeStopFree (PAR V)"

(* {Tick} added to allow <> *)



subsection \<open> Network of SKIPs \<close>

lemma TimeStopFreeNetworkSKIPS :
    "N \<noteq> 0 \<Longrightarrow> SkipTimeStopFreeNetwork ({1..N::nat}, \<lambda>i. (SKIP, {tock}))"
  apply (simp add: SkipTimeStopFreeNetwork_def)
  apply (simp add: TimeStopFree_def)
  apply (simp add: DeadlockFree_def)
  apply (simp add: isTPN_def)
  apply (simp add: in_failures)

  apply (simp add: insert_commute)
  (*apply (simp only: insert_Tick_NonTickTockEv_Un)
  apply (simp only: insert_Tock_NonTockEv_Un EvsetTick_Int)
  apply (simp add: ALP_def image_def)*)

  apply (simp add: PAR_def)
  apply (simp add: in_failures_par)
  apply (intro allI impI)

  apply (simp add: in_failures)
  apply (simp add: rest_tr_def)
  apply (intro conjI)

  apply (simp add: Union_eq set_eq_iff)
  apply (frule_tac x=Tick in spec)
  apply (drule_tac x=Tock in spec, simp, elim exE conjE)
  apply (rule_tac x=i in bexI, simp_all)

  apply (intro impI)
  apply (simp add: hide_tr_nilt_sett)
  apply (simp only: subset_eq, clarsimp)
  apply (simp add: Evset_def)

  apply (simp add: hide_tr_Tick_sett)
  apply (clarsimp)
done




section \<open> Lemmas \<close>


subsection \<open> isTimeStopStateOf subset alpha \<close>

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



subsection \<open> TimeStopFreeNetwork iff DeadlockFree Hiding NonTock \<close>


lemma TimeStopFreeNetwork_iff_DeadlockFree_PAR_Nontock :
    "fst V \<noteq> {} ==> isTPN V ==>
     TimeStopFreeNetwork V = [(EvALP V)]-DeadlockFree ((PAR V) -- Nontock)"
  apply (subst Tock_in_Ev_ALP_if_isTPN_V, simp, simp)
  apply (simp add: TimeStopFreeNetwork_def TimeStopFree_def)
  done



subsection \<open> TimeStopFreeNetwork iff not TimeStopState \<close>



subsubsection \<open> TimeStopState Existency \<close>

(*** Existency ***)


lemma in_failures_fst_PXf_iff_in_fst_FXf :
    "[| i \<in> I ;
        (I,FXf) isFailureOf (I,PXf) ;
        \<forall>i\<in>I. (s rest-tr snd (FXf i), Yf i) : fst (FXf i) |] ==>
        ((s rest-tr snd (PXf i), Yf i) :f failures (fst (PXf i)) MF) =
        ((s rest-tr snd (FXf i), Yf i) : fst (FXf i))"
  by (simp add: isFailureOf_def subseteqEX_restRefusal_iff)


lemma TimeStopState_notTimeStopFree_only_if_lmEX:
     "[| isTPN (I, PXf) ; 
         (I, FXf) isFailureOf (I, PXf) ;
         ALL i:I. (s rest-tr (snd (PXf i)), Yf i) :f failures (fst (PXf i)) MF ;
         EX i:I. {Tock} \<subseteq> Yf i |]
      ==>
      EX Zf. (ALL i:I. (s rest-tr (snd (FXf i)), Zf i) : fst (FXf i) &
                       Yf i Int (Ev ` snd (FXf i)) <= Zf i) &
             (EX i:I. {Tock} \<subseteq> Zf i)"

  apply (rule_tac x="(%i. (SOME Z. (s rest-tr (snd (FXf i)), Z) : fst (FXf i) &
                                    Yf i Int (Ev ` snd (FXf i)) <= Z &
                                    Z <= Ev ` snd (FXf i)))" in exI)
  apply (intro conjI)

  apply (intro ballI impI)
    apply (simp add: isFailureOf_def)
      apply (simp add: subseteqEX_restRefusal_iff)
      apply (drule_tac x="i" in bspec, simp)
      apply (drule_tac x="i" in bspec, simp)
      apply (elim conjE)
    apply (rotate_tac -2)
      apply (drule_tac x="s rest-tr snd (FXf i)" in spec)
      apply (drule_tac x="Yf i" in spec)
      apply (simp)
      apply (elim exE conjE)
    apply (rule_tac a="Z" in someI2, simp_all)

  apply (elim bexE conjE)
  apply (rule_tac x=i in bexI, simp_all)
    apply (simp add: isFailureOf_def)
      apply (simp add: subseteqEX_restRefusal_iff)
      apply (drule_tac x="i" in bspec, simp)
      apply (drule_tac x="i" in bspec, simp)
      apply (elim conjE)
    apply (rotate_tac -2)
      apply (drule_tac x="s rest-tr snd (FXf i)" in spec)
      apply (drule_tac x="Yf i" in spec)
      apply (simp)
      apply (elim exE conjE)
    apply (rule_tac a="Z" in someI2, simp_all)

    apply (simp add: isTPN_def)
    apply (elim conjE, blast)
  done





subsubsection \<open> not TimeStopFreeNetwork iff TimeStopState \<close>

(* only if part *)

lemma TimeStopState_notTimeStopFree_only_if:
    "[| isTPN (I,PXf) ; I \<noteq> {} ; finite I ;
        (I,FXf) isFailureOf (I,PXf) ;
        \<not> TimeStopFreeNetwork (I,PXf) |] ==>
     \<exists> sigma. sigma isTimeStopStateOf (I,FXf)"
  (* Get the trace and the indexed refusals of the non-TimeStopFreeNetwork *)
  apply (simp add: TimeStopFreeNetwork_def TimeStopFree_def DeadlockFree_def)
  apply (simp add: in_failures) (* failures hidding *)
  apply (simp add: PAR_def in_failures_par) (* failures PAR *)

  (* time-stop trace, full (deadlock) trace and indexed refusals (Yf) *)
  apply (elim conjE exE)
  
  (* traces are non-terminating *)
  apply (simp add: subset_insert)
  
  (* indexed refusals have no Tick *)
  apply (simp)

  (* TimeStopState has indexed communication refusals (Zf) *)
  apply (frule TimeStopState_notTimeStopFree_only_if_lmEX, simp_all)
    apply (rule exists_nonTerminatingAtom_refusing_Tock, simp_all)
      apply (simp add: refusalSet_def ALP_def)
  apply (elim exE conjE)

  (* the trace of the TimeStopState is the full (deadlock) trace *)
  apply (rule_tac x="sa" in exI)
  (* the indexed refusals of the TimeStopState is the indexed maximal refusals *)
  apply (rule_tac x=Zf in exI)

  apply (simp add: isTimeStopStateOf_def)
  apply (simp add: isStateOf_def)
  apply (frule isFailureOf_same_alpha)
  apply (intro conjI ballI)
    apply (simp add: ALP_def)
    apply (simp add: isFailureOf_def)
      apply (drule_tac x="i" in bspec, simp)
      apply (simp add: subseteqEX_restRefusal_iff, elim conjE)
      apply (drule_tac x="sa rest-tr snd (FXf i)" in spec)
      apply (drule_tac x="Zf i" in spec)
      apply (simp)

    apply (rule refusesAllNonTockEv_if, simp_all)
     apply (simp add: ball_conj_distrib)
    apply (rule refusesTock_if, simp)
  done



(*** if part ***)

lemma TimeStopState_notTimeStopFree_if:
    "[| isTPN (I,PXf) ; I \<noteq> {} ; finite I ;
        (I,FXf) isFailureOf (I,PXf) ;
        EX sigma. sigma isTimeStopStateOf (I,FXf) |]
     ==> \<not> TimeStopFreeNetwork (I,PXf)"
  (* Get the trace and the refusals from TimeStopState *)
  apply (simp add: isTimeStopStateOf_def)
  apply (elim exE conjE)
  apply (rename_tac s Yf)

  (* the time-stop trace is the trace of the TimeStopState hidding non-tock *)
  apply (simp add: TimeStopFreeNetwork_def)
  apply (simp add: TimeStopFree_def)
  apply (simp add: DeadlockFree_def)
  apply (rule_tac x="s --tr Nontock" in exI)
  apply (rule conjI)

  (* network does not terminate (traces in all states have no Tick) *)
  apply (frule sett_subset_EvALP_if_isStateOf)
  apply (simp add: ALP_def, fast)

  (* the complete deadlock trace is the non-hidding trace *)
  apply (simp add: in_failures)
  apply (rule_tac x="s" in exI, simp)

  (* failures PAR *)
  apply (simp add: PAR_def in_failures_par)
  apply (rule conjI)

    (* the deadlock trace only has events of the network alphabet *)
    apply (frule sett_subset_EvALP_if_isStateOf)
    apply (rule subset_insertI2)
    apply (simp add: isFailureOf_same_alpha ALP_def)

    (* refusals of the deadlock are those from TimestopState *)
    apply (rule_tac x="Yf" in exI)
    apply (frule Tick_notin_refusals_if_isStateOf, simp)
    apply (frule refusals_are_subsets_if_isStateOf, simp)
  
    apply (intro conjI)
      (* refusals are EvALP (i.e., refusesAllNonTock) *)
      apply (frule isFailureOf_same_alpha)
      apply (simp add: Collect_refusals_Int_insert_Tick)
      apply (simp add: Collect_refusals_Int_absorb)
      apply (simp add: refusesAllNonTockEv_def)
      apply (simp add: refusesTock_def)
      apply (simp add: refusalSet_def ALP_def)
      apply (blast)

      (* the network state is a state of each *)
      apply (intro ballI)
      apply (simp add: isStateOf_def in_failures_fst_PXf_iff_in_fst_FXf)
  done


(*** iff ***)

lemma notTimeStopFreeNetwork_iff_TimeStopState:
    "[| isTPN (I,PXf) ; I ~= {} ; finite I ;
        (I,FXf) isFailureOf (I,PXf) |]
     ==> (~ TimeStopFreeNetwork (I,PXf)) = (EX sigma. (sigma isTimeStopStateOf (I,FXf)))"
  apply (rule)
  apply (rule TimeStopState_notTimeStopFree_only_if, simp_all)
  apply (rule TimeStopState_notTimeStopFree_if, simp_all)
  done


subsubsection \<open> TimeStopFreeNetwork iff not TimeStopState \<close>

(*** TimeStopFree ***)

(*ALL sigma. (sigma isNonTockDeadlockStateOf (I,FXf)) ;*)
lemma TimeStopFreeNetwork_iff_notTimeStopState :
    "[| isTPN (I,PXf) ; I ~= {} ; finite I ;
        (I,FXf) isFailureOf (I,PXf) |]
     ==> TimeStopFreeNetwork (I,PXf) = (ALL sigma. ~(sigma isTimeStopStateOf (I,FXf)))"
  apply (rule iffI)
  apply (rotate_tac -1)
  apply (erule contrapos_pp)
  apply (simp add: notTimeStopFreeNetwork_iff_TimeStopState)
  apply (rotate_tac -1)
  apply (erule contrapos_pp)
  apply (simp add: notTimeStopFreeNetwork_iff_TimeStopState)
  done



end