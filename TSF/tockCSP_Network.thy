theory tockCSP_Network
imports tockCSP_DFP_Main
        TSF_law
begin



subsection \<open> TockNetwork \<close>


abbreviation isTockNetObj :: "('x * 'e::tockCSP set) => bool"
where
  "isTockNetObj X == (tock : (snd X))"


abbreviation isTockNet :: "('i set * ('i => ('b * 'e::tockCSP set))) => bool"
where
  "isTockNet V == (ALL i: fst V. isTockNetObj ((snd V) i))"



subsection \<open> Refusal Predicates \<close>

abbreviation netRefusals :: "('i) set => ('i \<Rightarrow> 'e event set) => ('e::tockCSP) event set"
                           ("(0netRefusals _ _)" [55,55] 55)
where
    "netRefusals I Yf == Union {(Yf i) |i. i : I}"


abbreviation refusalsOf :: "('i,'e) net_state => ('i,'e) NetworkF => ('e::tockCSP) event set"
                           ("(0_ refusalsOf _)" [55,55] 55)
where
    "sigma refusalsOf VF == netRefusals (fst VF) (snd sigma)"


definition refusesTock ("(0_ refusesTock _)" [55,55] 55)
where
    "sigma refusesTock VF == Tock : sigma refusalsOf VF"


definition refusesNonTock ("(0_ refusesNonTock _)" [55,55] 55)
where
    "sigma refusesNonTock VF == ~ sigma refusalsOf VF <= {Tock}"


definition refusesSomeNonTock ("(0_ refusesSomeNonTock _)" [55,55] 55)
where
    "sigma refusesSomeNonTock VF == sigma refusalsOf VF <= (Ev ` (ALP VF) - {Tock})"


definition refusesAllNonTock ("(0_ refusesAllNonTock _)" [55,55] 55)
where
    "sigma refusesAllNonTock VF == sigma refusalsOf VF = (Ev ` (ALP VF) - {Tock})"






subsection \<open> States: TimeStopState and NonTockDeadlockState \<close>


definition isTimeStopStateOf :: "('i,'e) net_state => ('i,'e::tockCSP) NetworkF => bool"
                           ("(0_ isTimeStopStateOf _)" [55,55] 55)
where
   "sigma isTimeStopStateOf VF == sigma isStateOf VF &
                                  sigma refusesTock VF"
(*
  SOMEONE REFUSES Tock    ==>     Tock : Union {((snd sigma) i) |i. i : fst VF}
  EVERYONE REFUSES Tock   ==>     Tock : Inter ...

  WHETHER SOMEONE REFUSES Tock (sigma refusesTock VF), IT WANTS TO CONTROL THE PASSAGE OF TIME
*)



definition isNonTockDeadlockStateOf :: "('i,'e) net_state => ('i,'e::tockCSP) NetworkF => bool"
                           ("(0_ isNonTockDeadlockStateOf _)" [55,55] 55)
where 
   "sigma isNonTockDeadlockStateOf VF == sigma isStateOf VF &
                                         sigma refusesAllNonTock VF"


subsection \<open> NonTockBusyNetwork Definition \<close>


definition NonTockBusyNetwork  :: "('i,'e::tockCSP) NetworkF => bool"
where
    "NonTockBusyNetwork VF ==
                  ALL i: fst VF. (ALL sigma. ~(sigma isNonTockDeadlockStateOf ({i}, snd VF)))"




subsection \<open> Lemmas \<close>



subsubsection \<open> PXf <--> FXf \<close>


lemma isTockNetObj_FXf_if_isTockNetObj_PXf :
    "(I,FXf) isFailureOf (I,PXf) ==> ALL i:I. isTockNetObj (PXf i) ==> ALL i:I. isTockNetObj (FXf i)"
  by (simp add: isFailureOf_def)

lemma isTockNetObj_PXf_if_isTockNetObj_FXf :
    "(I,FXf) isFailureOf (I,PXf) ==> ALL i:I. isTockNetObj (FXf i) ==> ALL i:I. isTockNetObj (PXf i)"
  by (simp add: isFailureOf_def)


lemma isTockNet_FXf_if_isTockNet_PXf :
    "isTockNet (I,PXf) ==> (I,FXf) isFailureOf (I,PXf) ==> isTockNet (I,FXf)"
  by (simp add: isFailureOf_def)

lemma isTockNet_PXf_if_isTockNet_FXf :
    "isTockNet (I,FXf) ==> (I,FXf) isFailureOf (I,PXf) ==> isTockNet (I,PXf)"
  by (simp add: isFailureOf_def)


lemma ALP_PXf_iff_ALP_FXf_if_isFailureOf :
    "(I,FXf) isFailureOf (I,PXf) ==> ALP (I,PXf) = ALP (I,FXf)"
   by (simp add: isFailureOf_def ALP_def)

lemma ALP_FXf_iff_ALP_PXf_if_isFailureOf :
    "(I,FXf) isFailureOf (I,PXf) ==> ALP (I,FXf) = ALP (I,PXf)"
   by (simp add: isFailureOf_def ALP_def)



subsubsection \<open> isTockNet syncSets \<close>


lemma not_empty_synchronisations_if_isTockNet :
    "[| isTockNet (I,FXf) |]
     ==> ALL i:I. Ev ` snd (FXf i) ~= {}"
  apply (rule)
  by (drule_tac x=i in bspec, simp, simp, fast)


lemma not_empty_syncSet :
    "[| isTockNet (I,FXf) ; i : I |] ==> Ev ` snd (FXf i) ~= {}"
  apply (drule not_empty_synchronisations_if_isTockNet)
  apply (drule_tac x=i in bspec, simp)
  by (simp)



subsubsection \<open> Tock, NonTockEv, EvsetTick and ALP \<close>


lemma NonTockEv_ALP_eq_EvsetTick_if_isTockNet :
    "isTockNet (I, PXf) ==> I ~= {} ==>
    NonTockEv Un Ev ` ALP (I, PXf) = EvsetTick"
  apply (rule NonTockEv_Un_eq_EvsetTick_if)
  by (simp add: ALP_def image_def, auto)


lemma NonTockEv_Un_absorb :
    "Tock \<notin> X ==> NonTockEv Un X = NonTockEv"
  by (auto simp only: NonTockEv_simp EvsetTick_def)


lemma NonTockEv_neq_ALP :
    "isTockNet (I, PXf) ==> I ~= {} ==>
    NonTockEv ~= Ev ` ALP (I, PXf)"
  apply (simp add: NonTockEv_simp EvsetTick_def)
  by (simp add: ALP_def image_def, auto)



lemma Tock_in_Ev_ALP_if_isTockNet :
    "I ~= {} ==> isTockNet (I, PXf) ==>
    Tock : Ev ` ALP (I, PXf)"
  apply (simp add: ALP_def image_def)
  by (force)


lemma Tock_in_Ev_ALP_if_isTockNet_V :
    "fst V ~= {} ==>
     isTockNet V ==> Ev ` (ALP V) = Ev ` (ALP V) Un {Tock}"
  apply (simp add: ALP_def)
  apply (rule insert_absorb[THEN sym])
  by (auto simp add: image_def)



lemma sett_subset_Ev_ALP :
    "(I,FXf) isFailureOf (I,PXf) ==>
     I ~= {} ==> Tick ~: sett sa ==>
     sett sa <= insert Tick (Ev ` (UN a:I. snd (PXf a))) ==>
     sett sa <= Ev ` ALP (I, FXf)"
  apply (simp add: ALP_FXf_iff_ALP_PXf_if_isFailureOf)
  apply (simp add: ALP_def)
  apply (simp add: subset_iff, force)
  done



subsubsection \<open> Refusals Predicates - Tock in and notin \<close>


lemma ex_Tock_in_refusals_if:
    "isTockNet (I,PXf) ==>
     I ~= {} ==>
     insert Tick (Ev ` (UN a:I. snd (PXf a))) = Union {Yf i Int insert Tick (Ev ` snd (PXf i)) |i. i : I} ==>
     EX i : I . Tock : Yf i"
  apply (simp add: image_def Int_def)
  apply (insert ex_in_conv[of I], simp, elim exE)
  apply (drule_tac x=x in bspec, simp, fast)
  done


lemma refusesTock_iff_ex_Tock_refusal :
    "(sigma refusesTock VF) = (EX i: fst VF. EX x: snd sigma i. x = Tock)"
   by (auto simp add: refusesTock_def)

lemma refusesNonTock_iff_ex_nonTock_refusal :
    "(sigma refusesNonTock VF) = (EX i: fst VF. EX x: snd sigma i. x ~= Tock)"
   by (auto simp add: refusesNonTock_def)



lemma Tock_notin_refusals_if_refusesAllNonTock :
    "(t, Yf) refusesAllNonTock (I, FXf) ==>
     ALL i:I. Tock ~: Yf i"
  apply (simp add: refusesAllNonTock_def)
  apply (simp add: Diff_eq ALP_def Union_eq, rule)
  by (blast)

lemma Tock_notin_refusals_if_not_refusesTock :
    "~ sigma refusesTock VF ==>
    Tock ~: sigma refusalsOf VF"
  by (simp add: refusesTock_def)


lemma not_refusesTock_if_refusesAllNonTock :
    "sigma refusesAllNonTock VF ==> ~ sigma refusesTock VF"
   by (auto simp add: refusesAllNonTock_def refusesTock_def)


lemma refusesSomeNonTock_if_refusesAllNonTock:
    "Ev ` ALP VF - {Tock} ~= {} ==>
     sigma refusesAllNonTock VF ==> sigma refusesSomeNonTock VF"
  apply (simp add: refusesSomeNonTock_def)
  apply (simp add: refusesAllNonTock_def)
  done

lemma refusesNonTock_if_refusesAllNonTock:
    "~ ALP VF <= {tock} ==>
     sigma refusesAllNonTock VF ==> sigma refusesNonTock VF"
  apply (simp add: refusesAllNonTock_def)
  apply (simp add: refusesNonTock_def, rule)
  apply (simp add: subset_singleton_iff)
  apply (fast)
  done


lemma refusesTock_and_not_hasNonTockRefusal :
    "(sigma refusesTock VF & ~ sigma refusesNonTock VF) = (sigma refusalsOf VF = {Tock})"
  apply (simp only: refusesTock_def refusesNonTock_def)
  apply (rule)
    apply (fast)
    apply (simp)
  done




subsubsection \<open> Refusals PXf --> FXf \<close>

lemma ex_refusals_superset_fst_FXf_if_failures_PXf:
    "I ~= {} ==> finite I ==> (I, FXf) isFailureOf (I, PXf) ==>
       i : I ==>
       (s rest-tr snd (FXf i), Yf i) :f failures (fst (PXf i)) MF ==>
       EX Z. Yf i Int Ev ` snd (FXf i) <= Z --> (s rest-tr snd (FXf i), Z) : fst (FXf i)"
  apply (simp add: isFailureOf_def)
  apply (drule_tac x=i in bspec, simp)
  apply (simp add: subseteqEX_restRefusal_iff, elim conjE)

  apply (frule memF_F2[of _ _ _ "Yf i Int Ev ` snd (FXf i)"], simp)

  apply (drule_tac x="s rest-tr snd (FXf i)" in spec)
  apply (drule_tac x="s rest-tr snd (FXf i)" in spec)
  apply (drule_tac x="Yf i Int Ev ` snd (FXf i)" in spec)
  apply (drule_tac x="Yf i" in spec)

  by (simp, force)






subsubsection \<open> State Refusals \<close>


lemma refusals_are_subsets_if_refusesTock :
    "(t, Yf) isStateOf (I, FXf) ==>
    (t, Yf) refusesTock (I, FXf) ==>
     ALL i:I. Yf i <= (Ev ` (snd (FXf i)))"
  apply (frule refusals_are_subsets_if_isStateOf, simp)
  done


lemma refusals_are_subsetsNonTock_if_not_refusesTock :
    "(t, Yf) isStateOf (I, FXf) ==>
     ~ (t, Yf) refusesTock (I, FXf) ==>
     ALL i:I. Yf i <= Ev ` snd (FXf i) - {Tock}"
  apply (simp add: Diff_eq)
  apply (subst ball_conj_distrib, rule)
  apply (frule refusals_are_subsets_if_isStateOf, simp)
  apply (frule Tock_notin_refusals_if_not_refusesTock)
  apply (rule)
  apply (simp add: Union_eq, fast)
  done


lemma refusals_are_subsetsNonTock_if_refusesAllNonTock :
    "(t, Yf) isStateOf (I, FXf) ==>
     (t, Yf) refusesAllNonTock (I, FXf) ==>
     ALL i:I. Yf i <= Ev ` snd (FXf i) - {Tock}"
  apply (simp add: Diff_eq)
  apply (subst ball_conj_distrib, rule)
  apply (frule refusals_are_subsets_if_isStateOf, simp)
  apply (rule Tock_notin_refusals_if_refusesAllNonTock, simp)
  done


lemma refusals_are_subsets_if_isTimeStopStateOf :
    "(t,Yf) isTimeStopStateOf (I,FXf) ==>
     ALL i:I. Yf i <= (Ev ` (snd (FXf i)))"
  apply (simp add: isTimeStopStateOf_def, elim conjE)
  by (simp add: refusals_are_subsets_if_refusesTock)


lemma refusals_are_subsetsNonTock_if_isNonTockDeadlockStateOf :
    "(t,Yf) isNonTockDeadlockStateOf (I,FXf) ==>
     ALL i:I. Yf i <= (Ev ` (snd (FXf i))) - {Tock}"
  apply (simp add: isNonTockDeadlockStateOf_def, elim conjE)
  by (simp add: refusals_are_subsetsNonTock_if_refusesAllNonTock)


lemma in_refusals_if_isNonTockDeadlockStateOf :
    "(t, Yf) isNonTockDeadlockStateOf (I, FXf) ==>
     i : I ==> j : I ==> i ~= j ==>
     x : Ev ` snd (FXf i) Int Ev ` snd (FXf j) - {Tock} ==>
     x : netRefusals I Yf"
  apply (simp only: isNonTockDeadlockStateOf_def)
  apply (simp add: refusesAllNonTock_def)

  apply (simp only: isStateOf_def, elim conjE)
  apply (simp add: image_iff)
  apply (simp (no_asm) add: ALP_def)

  apply (fast)
  done



subsubsection \<open> Tock in refusals TimeStopState \<close>


lemma Tock_notin_refusalsOf_if_not_isTimeStopStateOf :
    "sigma isStateOf VF ==>
     ~ (sigma isTimeStopStateOf VF) ==>
     Tock ~: sigma refusalsOf VF"
  apply (simp only: isTimeStopStateOf_def)
  by (rule Tock_notin_refusals_if_not_refusesTock, simp)


lemma Tock_in_refusalsOf_if_isTimeStopStateOf :
    "sigma isTimeStopStateOf VF ==>
     Tock : sigma refusalsOf VF"
  apply (simp add: isTimeStopStateOf_def)
  by (simp add: refusesTock_def)


lemma ex_Tock_in_refusals_if_isTimeStopStateOf :
    "(t, Yf) isTimeStopStateOf (I, FXf) ==>
     EX i : I. Tock : Yf i"
  apply (frule Tock_in_refusalsOf_if_isTimeStopStateOf)
  by (force)


lemma isTimeStopStateOf_iff_ex_Tock_in_refusals :
    "(t, Yf) isStateOf (I, FXf) ==>
     (t, Yf) isTimeStopStateOf (I, FXf) = (EX i : I. Tock : Yf i)"
  apply (simp add: isTimeStopStateOf_def)
  apply (simp add: refusesTock_def)
  by (force)



subsubsection \<open> Tock in refusals NonTockDeadlockState \<close>


lemma Tock_notin_refusals_if_isNonTockDeadlockStateOf :
    "sigma isNonTockDeadlockStateOf VF ==>
     Tock ~: sigma refusalsOf VF"
  apply (rule Tock_notin_refusals_if_not_refusesTock)
  apply (rule not_refusesTock_if_refusesAllNonTock)
  by (simp add: isNonTockDeadlockStateOf_def)


lemma neq_Tock_if_in_refusals_isNonTockDeadlockStateOf :
    "(t, Yf) isNonTockDeadlockStateOf (I, FXf) ==>
    x : netRefusals I Yf ==> x ~= Tock"
  apply (frule Tock_notin_refusals_if_isNonTockDeadlockStateOf)
  by (force)


lemma neq_tock_if_in_refusals_isNonTockDeadlockStateOf :
    "(t, Yf) isNonTockDeadlockStateOf (I, FXf) ==>
    Ev x : Yf i ==> i : I ==> x ~= tock"
  apply (frule Tock_notin_refusals_if_isNonTockDeadlockStateOf)
  by (force)


lemma neq_Tock_if_in_refusal_isNonTockDeadlockStateOf :
    "(t, Yf) isNonTockDeadlockStateOf (I, FXf) ==>
    x : Yf i ==> i : I ==> x ~= Tock"
  apply (frule Tock_notin_refusals_if_isNonTockDeadlockStateOf)
  by (force)



subsubsection \<open> States: TimeStopState and NonTockDeadlockState \<close>


lemma isStateOf_if_isTimeStopStateOf :
    "sigma isTimeStopStateOf VF ==> sigma isStateOf VF"
  by (simp add: isTimeStopStateOf_def)

lemma isStateOf_if_isNonTockDeadlockStateOf :
    "sigma isNonTockDeadlockStateOf VF ==> sigma isStateOf VF"
  by (simp add: isNonTockDeadlockStateOf_def)



lemma isTimeStopStateOf_if_isDeadlockStateOf :
    "fst VF ~= {} ==> isTockNet VF ==>
     sigma isDeadlockStateOf VF ==> sigma isTimeStopStateOf VF"
  apply (simp add: isDeadlockStateOf_def isTimeStopStateOf_def)
  apply (elim conjE)
  apply (insert ex_in_conv[of "fst VF"], simp, elim exE)
  apply (simp add: image_def Int_def ALP_def)
  apply (simp add: refusesTock_def)
  apply (fast)
  done



lemma not_isTimeStopStateOf_if_isNonTockDeadlockStateOf :
    "sigma isNonTockDeadlockStateOf VF ==>
    ~ (sigma isTimeStopStateOf VF)"
  apply (simp add: isNonTockDeadlockStateOf_def isTimeStopStateOf_def, elim conjE)
  by (rule not_refusesTock_if_refusesAllNonTock)


lemma not_isNonTockDeadlockStateOf_if_isTimeStopStateOf :
    "sigma isTimeStopStateOf VF ==>
    ~ (sigma isNonTockDeadlockStateOf VF)"
  apply (erule contrapos_pn)
  by (simp add: not_isTimeStopStateOf_if_isNonTockDeadlockStateOf)



lemma not_isTimeStopStateOf_iff_isNonTockDeadlockStateOf :
    "sigma isStateOf VF ==>
     (sigma isNonTockDeadlockStateOf VF) = (~ sigma isTimeStopStateOf VF & sigma refusesAllNonTock VF)"
  apply (rule)

  apply (frule not_isTimeStopStateOf_if_isNonTockDeadlockStateOf, simp)
  apply (simp add: isNonTockDeadlockStateOf_def isTimeStopStateOf_def)
  apply (simp add: isNonTockDeadlockStateOf_def isTimeStopStateOf_def)
  done


subsubsection \<open> Sub-States (States for each element) \<close>


lemma refusesTock_each_element :
   "[| (t, Yf) refusesTock (I, FXf) |] ==>
    EX i:I. (t rest-tr snd (FXf i), Yf) refusesTock ({i}, FXf)"
  apply (simp add: refusesTock_def)
  apply (elim conjE exE, fast)
  done


lemma isTimeStopStateOf_each_element :
   "[| (t, Yf) isTimeStopStateOf (I, FXf) |] ==>
    EX i: I. (t rest-tr snd (FXf i), Yf) isTimeStopStateOf ({i}, FXf)"
  apply (simp add: isTimeStopStateOf_def)

  apply (elim conjE)
    apply (simp add: isStateOf_each_element)
    apply (simp add: refusesTock_each_element)
  done


lemma not_isTimeStopStateOf_each_element :
   "[| (t, Yf) isStateOf (I, FXf) ; I ~= {} ;
       ~ (t, Yf) isTimeStopStateOf (I, FXf) |] ==>
    EX i: I. ~ (t rest-tr snd (FXf i), Yf) isTimeStopStateOf ({i}, FXf)"
  apply (simp only: isTimeStopStateOf_def refusesTock_def de_Morgan_conj)
  apply (erule disjE, simp)
  apply (simp add: refusesTock_each_element)
  apply (simp add: isStateOf_each_element)
  apply (fast)
  done


lemma refusesNonTock_each_element :
   "[| (t, Yf) refusesNonTock (I, FXf) |] ==>
    EX i:I. (t rest-tr snd (FXf i), Yf) refusesNonTock ({i}, FXf)"
  apply (simp add: refusesNonTock_def)
  apply (simp add: subset_singleton_iff)
  apply (elim conjE exE, fast)
  done





subsubsection \<open> NonTockBusyNetwork \<close>

(*-----------------------------------*
 |  How to check NonTockBusyNetworkF |
 *-----------------------------------*)

lemma check_NonTockBusyNetwork:
   "[| ALL i:I. ALL s Y. (s, Y) : fst (FXf i) --> Y ~= Ev ` (snd (FXf i)) - {Tock} |]
    ==> NonTockBusyNetwork (I,FXf)"
  apply (simp add: NonTockBusyNetwork_def)
  apply (intro allI ballI)
  apply (rename_tac s Yf)
  apply (drule_tac x="i" in bspec, simp)
  
  apply (simp add: isNonTockDeadlockStateOf_def refusesAllNonTock_def)
  apply (intro conjI allI impI)
  apply (simp add: isStateOf_def)
  apply (drule_tac x="s rest-tr (snd (FXf i))" in spec)
  apply (drule_tac x="Yf i" in spec)
  apply (simp)
  apply (simp add: ALP_def)
  done






subsubsection \<open> requests \<close>


lemma refusals_neq_ALP_diff_Tock_if_not_isNonTockDeadlockStateOf :
    "(t, Yf) isStateOf (I, FXf) ==> i : I ==> ~ Yf i <= {Tock} ==>
     ~ (t rest-tr snd (FXf i), Yf) isNonTockDeadlockStateOf ({i}, FXf) ==>
     Yf i ~= Ev ` snd (FXf i) - {Tock}"
  apply (simp add: isNonTockDeadlockStateOf_def)
  apply (frule isStateOf_each_element, simp, simp)

  apply (simp add: refusesAllNonTock_def refusesNonTock_def)
  by (simp add: ALP_def)


lemma Union_refusals_ALP_if_isNonTockDeadlockStateOf :
    "sigma isNonTockDeadlockStateOf (I, FXf) \<Longrightarrow>
    Union {snd sigma i |i. i : I} = Ev ` ALP (I,FXf) - {Tock}"
  by (simp add: isNonTockDeadlockStateOf_def refusesAllNonTock_def ALP_def)


(* i is not refusing event a (~= Tock) from its synchronisation set *)
lemma refusals_neq_ALP_diff_Tock_if_isNonTockDeadlockStateOf :
    "(t, Yf) isStateOf (I, FXf) ==>
     i : I ==> isTockNet (I, FXf) ==>
     (t rest-tr snd (FXf i), Yf) isNonTockDeadlockStateOf ({i}, FXf) ==>
     Yf i ~= Ev ` snd (FXf i) & Tock ~: Yf i"
  apply (simp add: isNonTockDeadlockStateOf_def refusesAllNonTock_def)
  apply (drule isStateOf_each_element, simp, simp)
  by (simp add: ALP_def, fast)



lemma ex_non_refused_nonTock_event_if_not_isTimeStopStateOf :
   "(t, Yf) isStateOf (I, FXf) ==> ~ (t, Yf) isTimeStopStateOf (I, FXf) ==>
    i \<in> I ==> 
    Yf i ~= Ev ` snd (FXf i) - {Tock} ==>
    EX a : Ev ` snd (FXf i). a ~: Yf i & a ~= Tock"
  apply (frule refusals_are_subsets_if_isStateOf)
  apply (frule not_isTimeStopStateOf_each_element, simp, fast)
  apply (simp add: isTimeStopStateOf_def)
  apply (simp add: isTimeStopStateOf_def refusesTock_def)
  by (fast)


lemma ex_non_refused_nonTock_event_if_isNonTockDeadlockStateOf :
   "(t, Yf) isNonTockDeadlockStateOf (I, FXf) ==>
    i \<in> I ==> 
     Yf i ~= Ev ` snd (FXf i) - {Tock} ==>
    EX a : Ev ` snd (FXf i). a ~: Yf i & a ~= Tock"
  apply (frule isStateOf_if_isNonTockDeadlockStateOf)
  apply (drule not_isTimeStopStateOf_if_isNonTockDeadlockStateOf)
  by (frule ex_non_refused_nonTock_event_if_not_isTimeStopStateOf, simp_all)



lemma ex_target_for_Request_nonTock_refusals :
    "isTockNet (I,FXf) ==>
     (t, Yf) isNonTockDeadlockStateOf (I, FXf) ==>
     Union {Yf i |i. i : I} = Ev ` {a. EX i:I. a : snd (FXf i)} - {Tock} ==>
     i : I ==>
     Yf i ~= Ev ` snd (FXf i) - {Tock} ==>
     EX j. (I, FXf) >> i --[(t, Yf)]--> j"
  apply (simp only: isRequestOf_def)

  apply (frule isStateOf_if_isNonTockDeadlockStateOf)
  apply (frule refusals_are_subsets_if_isStateOf)

  (* i is not refusing event a from its synchronisation set *)
  apply (frule ex_non_refused_nonTock_event_if_isNonTockDeadlockStateOf[of t Yf I FXf i])
  apply (simp_all, elim bexE)

  apply (subgoal_tac "Ev a : Ev ` {a. EX i:I. a : snd (FXf i)} - {Tock}")
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


lemma ex_Request_if_isNonTockDeadlockStateOf_NonTockBusyNetwork :
    "(t, Yf) isNonTockDeadlockStateOf (I, FXf) ==> NonTockBusyNetwork (I, FXf) ==> 
     isTockNet (I, FXf) ==>
     i : I ==> ~ Yf i <= {Tock} ==>
     EX j. (I, FXf) >> i --[(t, Yf)]--> j"
  apply (frule isStateOf_if_isNonTockDeadlockStateOf)

  apply (rule ex_target_for_Request_nonTock_refusals, simp_all)

  (* refusing ALL events *)
  apply (frule Union_refusals_ALP_if_isNonTockDeadlockStateOf, simp add: ALP_def)

  (* NonTock busy --> i is time-stop-free *)
  apply (simp only: NonTockBusyNetwork_def)

  (* State of i *)
  apply (drule_tac x="i" in bspec, simp)
  apply (drule_tac x="i" in bspec, simp)
  apply (drule_tac x="(t rest-tr (snd (FXf i)), Yf)" in spec)

  apply (simp add: isNonTockDeadlockStateOf_def refusesAllNonTock_def)
  apply (simp add: refusesNonTock_def ALP_def)
  apply (drule mp, simp add: isStateOf_each_element)
  apply (simp)
  done




end