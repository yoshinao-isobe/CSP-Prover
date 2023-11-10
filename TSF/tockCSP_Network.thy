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

theory tockCSP_Network
imports tockCSP_DFP
begin



section \<open> Timed Atom, Tock Net and Timed Process Network \<close>


abbreviation isTimedAtom :: "('x * 'e::tockCSP set) => bool"
where
  "isTimedAtom X == (tock : (snd X))"


(*definition isTockNet :: "('i set * ('i => ('b * 'e::tockCSP set))) => bool"
where
  "isTockNet V == (EX i: fst V. isTimedAtom ((snd V) i))"*)


definition isTPN :: "('i set * ('i => ('b * 'e::tockCSP set))) => bool"
where
  "isTPN V == (ALL i: fst V. isTimedAtom ((snd V) i))"




section \<open> Refusals Predicates \<close>

definition refusalSet :: "('i,'x,'e) Net => ('i \<Rightarrow> 'e event set) => ('e::tockCSP) event set"
                           ("(0refusalSet _<_>)" [55,0] 55)    
where
    "refusalSet V<Yf> == \<Union> {(Yf i) |i. i : fst V}"


(*abbreviation refusalsIn :: "('i,'x,'e) Net => ('i \<Rightarrow> 'e event set) => ('e::tockCSP) event set"
                           ("(0_-refusalsIn'(_'))" [55,0] 55)
where "V-refusalsIn(Yf) == refusalSet V<Yf>"*)



abbreviation interfaceRefusalsIn ::
    "('i,'x,'e) Net => ('i \<Rightarrow> 'e event set) => ('e::tockCSP) event set"
                           ("(0_-interfaceRefusalsIn<_>)" [55,0] 55)
where
    "V-interfaceRefusalsIn<Yf> == refusalSet V< (\<lambda>i. Yf i \<inter> Ev ` snd ((snd V) i)) >"


abbreviation nonTermInterfaceRefusalsIn ::
    "('i,'x,'e) Net => ('i \<Rightarrow> 'e event set) => ('e::tockCSP) event set"
                           ("(0_-nonTermInterfaceRefusalsIn<_>)" [55,55] 55)
where
    "V-nonTermInterfaceRefusalsIn<Yf> == refusalSet V< (\<lambda>i. Yf i \<inter> insert Tick (Ev ` snd ((snd V) i))) >"





lemma ALP_simp [simp]: "(\<Union>i\<in>I. snd (PXf i)) = ALP (I,PXf)"
  by (simp add: image_def ALP_def, blast)
(*
lemma EvALP_Union [simp]: "Ev ` (\<Union>a\<in>I. snd (PXf a)) = EvALP (I,PXf)"
  by (simp)
*)


definition refusesTock ("(0_ refusesTock _)" [55,55] 55)
where
    "sigma refusesTock V == Tock : refusalSet V<snd sigma>"


definition refusesTick ("(0_ refusesTick _)" [55,55] 55)
where
    "sigma refusesTick V == Tick : refusalSet V<snd sigma>"



abbreviation "NonTockEvALP V == (EvALP V) - {Tock}"


definition refusesAllNonTockEv ("(0_ refusesAllNonTockEv _)" [55,55] 55)
where
    "sigma refusesAllNonTockEv V == NonTockEvALP V <= refusalSet V<snd sigma>"


(*definition refusesSomeNonTockEv ("(0_ refusesSomeNonTockEv _)" [55,55] 55)
where
    "sigma refusesSomeNonTockEv V == refusalSet V<snd sigma> <= NonTockEvALP V"*)


definition refusesOnlyNonTockEv ("(0_ refusesOnlyNonTockEv _)" [55,55] 55)
where
    "sigma refusesOnlyNonTockEv V == refusalSet V<snd sigma> = NonTockEvALP V"






section \<open> States: TimeStopState and NonTockDeadlockState \<close>


definition isUrgentStateOf :: "('i,'e) net_state => ('i,'e::tockCSP) NetworkF => bool"
                           ("(0_ isUrgentStateOf _)" [55,55] 55)
where
   "sigma isUrgentStateOf VF == sigma isStateOf VF &
                                sigma refusesTock VF"

(*
  SOMEONE REFUSES Tock: sigma refusesTock VF == Tock : Union {((snd sigma) i) |i. i : fst VF}
  THUS, SOMEONE WANTS TO CONTROL TIME PASSING

  EVERYONE REFUSES Tock   ==>     Tock : Inter ...
*)



definition isNonTockDeadlockStateOf :: "('i,'e) net_state => ('i,'e::tockCSP) NetworkF => bool"
                           ("(0_ isNonTockDeadlockStateOf _)" [55,55] 55)
where 
   "sigma isNonTockDeadlockStateOf VF == sigma isStateOf VF &
                                         sigma refusesAllNonTockEv VF"



definition isTimeStopStateOf :: "('i,'e) net_state => ('i,'e::tockCSP) NetworkF => bool"
                           ("(0_ isTimeStopStateOf _)" [55,55] 55)
where
   "sigma isTimeStopStateOf VF == sigma isStateOf VF &
                                  (sigma refusesAllNonTockEv VF &
                                   sigma refusesTock VF)"




section \<open> Busyness Definitions \<close>


definition NonTockBusyNetwork  :: "('i,'e::tockCSP) NetworkF => bool"
where
    "NonTockBusyNetwork VF ==
         ALL i: fst VF. (ALL sigma. ~(sigma isNonTockDeadlockStateOf ({i}, snd VF)))"



definition TockBusyNetwork  :: "('i,'e::tockCSP) NetworkF => bool"
where
    "TockBusyNetwork VF ==
         ALL i: fst VF. (ALL sigma. ~(sigma isUrgentStateOf ({i}, snd VF)))"




section \<open> Lemmas \<close>

subsection \<open> isFailureOf \<close>

(*lemma isFailureOf_same_syncSet : 
     "(I, FXf) isFailureOf (I, PXf) ==>
      (\<Union>a\<in>I. snd (PXf a)) = {a. \<exists>i\<in>I. a \<in> snd (FXf i)}"
  apply (frule isFailureOf_same_alpha)
  by (blast)

lemma isFailureOf_same_syncSet2 : 
     "(I, FXf) isFailureOf (I, PXf) ==>
      {a. \<exists>i\<in>I. a: snd (PXf i)} = {a. \<exists>i\<in>I. a \<in> snd (FXf i)}"
  apply (frule isFailureOf_same_alpha)
  by (blast)

lemma isFailureOf_same_Ev_alpha:
   "(I, FXf) isFailureOf (I, PXf)
    ==> ALL i:I. Ev ` snd (PXf i) = Ev ` snd (FXf i)"          
by (simp add: isFailureOf_def)


lemma isFailureOf_same_Ev_syncSet : 
     "(I, FXf) isFailureOf (I, PXf) ==>
      Ev ` (\<Union>a\<in>I. snd (PXf a)) = Ev ` {a. \<exists>i\<in>I. a \<in> snd (FXf i)}"
  apply (frule isFailureOf_same_alpha)
  by (blast)


lemma isFailureOf_same_insert_Tick_Ev_syncSet : 
     "(I, FXf) isFailureOf (I, PXf) ==>
      insert Tick (Ev ` (\<Union>a\<in>I. snd (PXf a))) = insert Tick (Ev ` {a. \<exists>i\<in>I. a \<in> snd (FXf i)})"
  apply (frule isFailureOf_same_alpha)
  by (blast)*)



subsection \<open> Tick NOT in NETWORK \<close>


lemma Tick_notin_sett_if_isStateOf :
    "sigma isStateOf VF ==>
     Tick ~: sett (fst sigma)"
  apply (simp add: isStateOf_def)
  by (blast)


lemma Tick_notin_refusals_if_isStateOf :
    "sigma isStateOf VF ==>
     ALL i: fst VF . Tick ~: snd sigma i"
  apply (simp add: isStateOf_def)
  by (blast)


lemma Collect_refusals_Int_insert_Tick :
    "ALL i:I. Tick ~: Yf i ==>
     { Yf i Int insert Tick (Ev ` snd (PXf i)) |i. i : I } =
     { Yf i Int (Ev ` snd (PXf i)) |i. i : I }"
  by (fast)


lemma Collect_refusals_Int_absorb :
    "ALL i:I. Tick ~: Yf i ==>
     ALL i:I. Yf i <= Ev ` snd (FXf i) ==>
     { Yf i Int (Ev ` snd (FXf i)) |i. i : I } =
     { Yf i |i. i : I }"
  by (fast)


lemma Union_Collect_insert_Tick_refusals_iff :
    "I ~= {} ==>
     Union { insert Tick (Yf i) |i. i : I } =
     insert Tick (Union { Yf i |i. i : I })"
  apply (simp add: Union_eq)
  apply (rule)
    apply (blast)
    apply (blast)
  done



subsection \<open> refusalSet \<close>

lemma refusalSet_cong :
    "ALL i : I1 . EX i2 : I2 . Yf1 i = Yf2 i2 ==> 
     ALL i2 : I2 . EX i : I1 . Yf1 i = Yf2 i2 ==> 
     refusalSet(I1,Xf1)<Yf1> = refusalSet(I2,Xf2)<Yf2>"
  apply (simp add: refusalSet_def Union_eq)
  apply (rule Collect_cong)
  apply (rule ex_cong1)
  apply (rule conj_cong, simp_all)
  apply (rule, elim exE, fast)
  apply (elim exE, fast)
  done


lemma in_refusalSet :
    "i : I ==>
     e : Yf i ==>
     e : refusalSet(I,Xf)<Yf>"
  apply (simp add: refusalSet_def)
  by (fast)



subsection \<open> refusalSet subset \<close>


lemma Tock_notin_refusalSet_subset :
    "J <= I ==>
     a ~: refusalSet(I,Xf)<Yf> ==>
     a ~: refusalSet(J,Xf)<Yf>"
  by (auto simp add: refusalSet_def)



subsection \<open> NonTockBusyNetwork \<close>

(*-----------------------------------*
 |  How to check NonTockBusyNetworkF |
 *-----------------------------------*)

lemma check_NonTockBusyNetwork:
   "[| ALL i:I. ALL s Y. (s, Y) : fst (FXf i) --> ~ Ev ` (snd (FXf i)) - {Tock} <= Y |]
    ==> NonTockBusyNetwork (I,FXf)"
  apply (simp add: NonTockBusyNetwork_def)
  apply (intro allI ballI)
  apply (rename_tac s Yf)
  apply (drule_tac x="i" in bspec, simp)
  apply (drule_tac x="s rest-tr (snd (FXf i))" in spec)
  apply (drule_tac x="Yf i" in spec)

  apply (simp add: isNonTockDeadlockStateOf_def)
  apply (simp add: refusesAllNonTockEv_def ALP_def)
  apply (simp add: isStateOf_def refusalSet_def)
  done




subsection \<open> isTPN \<close>

lemma isTPN_subset :
    "isTPN (I,FXf) ==> S <= I ==> isTPN (S,FXf)"
  by (simp add: isTPN_def, fast)


subsection \<open> isTPN and ALP: PXf <--> FXf \<close>


lemma isFailureOf_same_TPN :
    "(I,FXf) isFailureOf (I,PXf) ==> isTPN (I,PXf) = isTPN (I,FXf)"
  by (simp add: isFailureOf_def isTPN_def)

lemma isFailureOf_same_ALP :
    "(I,FXf) isFailureOf (I,PXf) ==> ALP (I,PXf) = ALP (I,FXf)"
   by (simp add: isFailureOf_def ALP_def)



subsection \<open> isTPN syncSets \<close>


lemma not_empty_synchronisation_sets_if_isTPN :
    "[| isTPN (I,FXf) |]
     ==> ALL i:I. Ev ` snd (FXf i) ~= {}"
  apply (rule, simp add: isTPN_def)
  by (drule_tac x=i in bspec, simp, fast)


lemma not_empty_syncSet :
    "[| isTPN (I,FXf) ; i : I |] ==> Ev ` snd (FXf i) ~= {}"
  apply (drule not_empty_synchronisation_sets_if_isTPN)
  apply (drule_tac x=i in bspec, simp)
  by (simp)




subsection \<open> Tock, NonTockEv, EvsetTick and ALP \<close>


lemma NonTockEv_ALP_eq_EvsetTick_if_isTPN :
    "isTPN (I, PXf) ==> I ~= {} ==>
    NonTockEv Un EvALP (I, PXf) = EvsetTick"
  apply (rule NonTockEv_Un_eq_EvsetTick_if)
  by (simp add: ALP_def image_def isTPN_def, auto)


lemma NonTockEv_neq_ALP :
    "isTPN (I, PXf) ==> I ~= {} ==>
    NonTockEv ~= EvALP (I, PXf)"
  apply (simp add: NonTockEv_simp EvsetTick_def)
  by (simp add: ALP_def image_def, auto)



lemma Tock_in_Ev_ALP_if_isTPN :
    "isTPN VF ==> fst VF ~= {} ==>
    Tock : EvALP VF"
  apply (simp add: ALP_def image_def isTPN_def)
  by (force)


lemma Tock_in_Ev_ALP_if_isTPN_V :
    "fst V ~= {} ==>
     isTPN V ==> EvALP V = EvALP V Un {Tock}"
  apply (simp add: ALP_def isTPN_def)
  apply (rule insert_absorb[THEN sym])
  by (auto simp add: image_def)




subsection \<open> Trace and sett \<close>

(*lemma sett_subset_noTick :
    "Tick ~: sett sa ==>
     (sett sa <= insert Tick X) = (sett sa <= X)"
  by (simp add: subset_insert)
*)

lemma sett_subset_EvALP_if_isStateOf :
    "(s,Yf) isStateOf (I,PXf) ==>
     sett s <= EvALP (I, PXf)"
  by (simp add: isStateOf_def)

lemma sett_subset_EvALP :
    "(I,FXf) isFailureOf (I,PXf) ==>
     I ~= {} ==> Tick ~: sett sa ==>
     sett sa <= insert Tick (Ev ` (UN a:I. snd (PXf a))) ==>
     sett sa <= EvALP (I, FXf)"
  apply (simp add: isFailureOf_same_ALP)
  apply (simp add: ALP_def)
  apply (simp add: subset_iff, force)
  done


subsection \<open> tock refusals \<close>


lemma Tock_in_Ev_syncSet_if_isTPN :
    "isTPN (I,FXf) ==> I ~= {} ==>
     Tock \<in> Ev ` {a. \<exists>i\<in>I. a \<in> snd (FXf i)}"
  apply (simp add: isTPN_def)
  apply (blast)
  done

lemma Tock_in_insert_Tick_Ev_syncSet_if_isTPN :
    "isTPN (I,FXf) ==> I ~= {} ==>
     Tock \<in> insert Tick (Ev ` {a. \<exists>i\<in>I. a \<in> snd (FXf i)})"
  apply (simp add: isTPN_def)
  apply (blast)
  done


lemma exists_nonTerminatingAtom_refusing_Tock :
    "isTPN (I, PXf) ==> I ~= {} ==>
     (I, FXf) isFailureOf (I, PXf) ==>
     EvALP (I, PXf) = (I, PXf)-nonTermInterfaceRefusalsIn<Yf> ==>
     EX i:I. Tock : Yf i"
  apply (simp only: set_eq_iff)
  apply (drule_tac x=Tock in spec)
  apply (simp add: refusalSet_def ALP_def)
  apply (frule Tock_in_Ev_syncSet_if_isTPN, simp, simp)
  apply (elim exE bexE conjE, force)
  done


lemma exists_terminatingAtom_refusing_Tock :
    "isTPN (I, PXf) ==> I ~= {} ==>
     (I, FXf) isFailureOf (I, PXf) ==>
     EvALP (I, PXf) = (I, PXf)-interfaceRefusalsIn<Yf> ==>
     EX i:I. Tock : Yf i"
  apply (simp only: set_eq_iff)
  apply (frule isFailureOf_same_alpha)
  apply (simp only: isFailureOf_same_TPN)
  apply (frule Tock_in_Ev_syncSet_if_isTPN, simp)
    apply (simp add: refusalSet_def ALP_def)
  apply (elim exE conjE)
  apply (rule_tac x=i in bexI, simp_all)
  done


lemma refusesTock_if :
    "\<exists>i\<in>I. {Tock} \<subseteq> Zf i \<Longrightarrow> (sa, Zf) refusesTock (I, FXf)"
  apply (simp add: refusesTock_def refusalSet_def)
  apply (fast)
done


lemma refusesAllNonTockEv_if :
    "EvALP ({ i | i:PXf ` I }Fnet) = \<Union> {Yf i \<inter> insert Tick (Ev ` snd (PXf i)) |i. i \<in> I} \<Longrightarrow>
     \<forall>i\<in>I. (sa rest-tr snd (FXf i), Zf i) \<in> fst (FXf i) \<and> Yf i \<inter> Ev ` snd (FXf i) \<subseteq> Zf i \<Longrightarrow>
     \<forall>i\<in>I. snd (PXf i) = snd (FXf i) \<Longrightarrow>
     (sa, Zf) refusesAllNonTockEv (I, FXf)"
  apply (simp add: refusesAllNonTockEv_def)
  apply (simp add: ALP_def refusalSet_def)
  apply (simp add: Diff_subset_conv)
  apply (simp add: subset_eq)
  apply (intro allI impI, elim exE conjE, simp)
  apply (intro ballI)
  apply (rule disjI2)
  apply (rule_tac x="Zf i" in exI)
  apply (blast)
done



subsection \<open> non-Tock refusals \<close>

lemma in_ALP_Diff_Tock :
    "refusalSet(I,FXf)<Yf> = EvALP(I,FXf) - {Tock} ==>
     a : snd (FXf i) ==> a ~= tock ==> i : I ==>
     Ev a : EvALP(I,FXf) - {Tock}"
  by (simp add: ALP_def, blast)


lemma ex_in_ALP_Diff_Tock :
    "I ~= {} ==>
     ALL i:I. ~ Ev ` snd (FXf i) <= {Tock} ==>
    EX x. x : EvALP (I, FXf) - {Tock}"
  apply (insert ex_in_conv[of I], simp, elim exE)
  by (auto simp add: ALP_def)

(*lemma ALP_Diff_Tock :
    "(t,Yf) isStateOf (I,FXf) ==>
     \<forall>i\<in>I. Yf i \<subseteq> Ev ` snd (FXf i) - {Tock} ==>
     refusalSet I Yf = EvALP (I, FXf) - {Tock}"
  apply (simp add: ALP_def Diff_eq)
  apply (rule, rule, fast, rule)
  apply (elim IntE imageE, simp, elim bexE)
  apply (rule_tac x="Yf i" in exI, rule, fast)
  apply (frule refusals_are_subsets_if_isStateOf)*)


lemma not_alpha_subset_Tock_if_not_refusals_subset_Tock :
    "(t, Yf) isStateOf (I, FXf) ==>
     i : I ==>
     ~ Yf i <= {Tock} ==>
     ~ Ev ` snd (FXf i) <= {Tock}"
  apply (simp add: isStateOf_def, elim exE conjE)
  apply (drule_tac x=i in bspec, simp, elim conjE)
  by (blast)



subsection \<open> Refusal Predicates relations to Synchronisation Sets \<close>


lemma refusalsOf_are_subsets_if_isStateOf_1 :
    "sigma isStateOf VF ==>
     refusalSet VF<snd sigma> <= (EvALP VF)"
  apply (frule refusals_are_subsets_if_isStateOf)
  apply (simp add: refusalSet_def ALP_def, fast)
  done


lemma refusalsOf_are_subsets_if_isStateOf_2 :
    "(t, Yf) isStateOf VF ==>
     refusalSet VF<Yf> <= (EvALP VF)"
  apply (frule refusals_are_subsets_if_isStateOf)
  apply (simp add: refusalSet_def ALP_def, fast)
  done

lemmas refusalsOf_are_subsets_if_isStateOf =
       refusalsOf_are_subsets_if_isStateOf_1
       refusalsOf_are_subsets_if_isStateOf_2


lemma refusals_are_subsetsNonTock_if_not_refusesTock :
    "(t, Yf) isStateOf (I, FXf) ==>
     ~ (t, Yf) refusesTock (I, FXf) ==>
     ALL i:I. Yf i <= Ev ` snd (FXf i) - {Tock}"
  apply (simp add: Diff_eq)
  apply (subst ball_conj_distrib, rule)
  apply (drule refusals_are_subsets_if_isStateOf, simp)
  apply (simp only: refusesTock_def refusalSet_def)
  apply (rule)
  apply (simp add: Union_eq, fast)
  done


lemma Tock_notin_refusals_if_refusesOnlyNonTockEv :
    "(t, Yf) refusesOnlyNonTockEv (I, FXf) ==>
     ALL i:I. Tock ~: Yf i"
  apply (simp add: refusesOnlyNonTockEv_def refusalSet_def)
  apply (simp add: Diff_eq ALP_def Union_eq, rule)
  by (blast)


lemma refusals_are_subsetsNonTock_if_refusesOnlyNonTock :
    "(t, Yf) isStateOf (I, FXf) ==>
     (t, Yf) refusesOnlyNonTockEv (I, FXf) ==>
     ALL i:I. Yf i <= Ev ` snd (FXf i) - {Tock}"
  apply (simp add: Diff_eq)
  apply (subst ball_conj_distrib, rule)
  apply (frule refusals_are_subsets_if_isStateOf, simp)
  apply (rule Tock_notin_refusals_if_refusesOnlyNonTockEv, simp)
  done



subsubsection \<open> State + Refusals Predicates \<close>


(*lemma refusesSomeNonTock_if_refusesAllNonTockEv:
    "sigma isStateOf VF ==> ~ sigma refusesTock VF ==>
     sigma refusesAllNonTockEv VF ==> sigma refusesSomeNonTock VF"
  apply (drule refusalsOf_are_subsets_if_isStateOf)
  apply (simp add: refusesSomeNonTock_def)
  apply (simp add: refusesAllNonTockEv_def)
  apply (simp only: refusesTock_def)
  apply (simp add: subset_singleton_iff Diff_eq)
  done*)

lemma refusesOnlyNonTockEv_if_not_refusesTock_and_refusesAllNonTockEv :
    "sigma isStateOf VF ==>
     ~ sigma refusesTock VF ==> sigma refusesAllNonTockEv VF ==>
     sigma refusesOnlyNonTockEv VF"
  apply (case_tac sigma, simp)
  apply (drule refusalsOf_are_subsets_if_isStateOf)
  apply (simp add: refusesOnlyNonTockEv_def)
  apply (simp only: refusesTock_def)
  apply (simp only: refusalSet_def refusesAllNonTockEv_def)
  apply (rule)
  apply (simp (no_asm_simp) add: Diff_eq, rule)
  apply (simp)
  apply (simp)
  done


lemma not_refusesTock_if_refusesOnlyNonTockEv :
    "sigma refusesOnlyNonTockEv VF ==>
     ~ sigma refusesTock VF"
   by (auto simp add: refusesOnlyNonTockEv_def refusesTock_def)


lemma refusesAllNonTockEv_if_refusesOnlyNonTockEv :
    "sigma refusesOnlyNonTockEv VF ==>
     sigma refusesAllNonTockEv VF"
   by (auto simp add: refusesOnlyNonTockEv_def refusesAllNonTockEv_def)


lemma refusesOnlyNonTockEv_iff_not_refusesTock_and_refusesAllNonTockEv :
    "sigma isStateOf VF ==>
     sigma refusesOnlyNonTockEv VF =
     (~ sigma refusesTock VF & sigma refusesAllNonTockEv VF)"
  apply (rule iffI)
  apply (simp add: not_refusesTock_if_refusesOnlyNonTockEv)
  apply (simp add: refusesAllNonTockEv_if_refusesOnlyNonTockEv)
  apply (clarify)
  apply (simp add: refusesOnlyNonTockEv_if_not_refusesTock_and_refusesAllNonTockEv)
  done


subsubsection \<open> Sub-Refusal Predicates \<close>


lemma refusesTock_each_element :
   "[| (t, Yf) refusesTock (I, FXf) |] ==>
    EX i:I. (t rest-tr snd (FXf i), Yf) refusesTock ({i}, FXf)"
  apply (simp add: refusesTock_def refusalSet_def)
  apply (elim conjE exE, fast)
  done


lemma not_refusesTock_each_element :
   "[| ~ (t, Yf) refusesTock (I, FXf) |] ==>
    ALL i:I. ~ (t rest-tr snd (FXf i), Yf) refusesTock ({i}, FXf)"
  apply (simp add: refusesTock_def refusalSet_def, rule)
  apply (fast)
  done




subsubsection \<open> Tock notin refusals refusesOnlyNonTockEv \<close>


lemma neq_Tock_if_in_refusals_refusesOnlyNonTockEv :
    "(t, Yf) refusesOnlyNonTockEv (I, FXf) ==>
    x \<in> refusalSet(I,FXf)<Yf> ==> x \<noteq> Tock"
  apply (simp add: refusalSet_def)
  apply (frule Tock_notin_refusals_if_refusesOnlyNonTockEv)
  by (force)


lemma neq_tock_if_in_refusals_refusesOnlyNonTockEv :
    "(t, Yf) refusesOnlyNonTockEv (I, FXf) ==>
    Ev x : Yf i ==> i : I ==> x ~= tock"
  apply (frule Tock_notin_refusals_if_refusesOnlyNonTockEv)
  by (force)


lemma neq_Tock_if_in_refusal_refusesOnlyNonTockEv :
    "(t, Yf) refusesOnlyNonTockEv (I, FXf) ==>
    x : Yf i ==> i : I ==> x ~= Tock"
  apply (frule Tock_notin_refusals_if_refusesOnlyNonTockEv)
  by (force)





subsection \<open> TimeStopState and NonTockDeadlockState \<close>


lemma isStateOf_if_isUrgentStateOf :
    "sigma isUrgentStateOf VF ==> sigma isStateOf VF"
  by (simp add: isUrgentStateOf_def)

lemma isStateOf_if_isTimeStopStateOf :
    "sigma isTimeStopStateOf VF ==> sigma isStateOf VF"
  by (simp add: isTimeStopStateOf_def)

lemma isUrgentStateOf_if_isTimeStopStateOf :
    "sigma isTimeStopStateOf VF ==> sigma isUrgentStateOf VF"
  by (simp add: isTimeStopStateOf_def isUrgentStateOf_def)

lemma isStateOf_if_isNonTockDeadlockStateOf :
    "sigma isNonTockDeadlockStateOf VF ==> sigma isStateOf VF"
  by (simp add: isNonTockDeadlockStateOf_def)



lemma isTimeStopStateOf_if_isDeadlockStateOf :
    "isTPN VF ==> fst VF ~= {} ==>
     sigma isDeadlockStateOf VF ==> sigma isTimeStopStateOf VF"
  apply (simp add: isDeadlockStateOf_def isTimeStopStateOf_def)
  apply (elim conjE)
  apply (frule refusalsOf_are_subsets_if_isStateOf)
  apply (simp add: refusesTock_def)
  apply (simp add: refusesAllNonTockEv_def)
  apply (simp add: refusalSet_def)

  apply (insert ex_in_conv[of "fst VF"], simp, elim exE)
  apply (simp add: Tock_in_Ev_ALP_if_isTPN)
  done

lemma not_isDeadlockStateOf_if_not_isTimeStopStateOf :
    "isTPN VF ==> fst VF ~= {} ==>
     ~ sigma isTimeStopStateOf VF ==> ~ sigma isDeadlockStateOf VF"
  apply (rotate_tac -1, erule contrapos_nn)
  by (rule isTimeStopStateOf_if_isDeadlockStateOf)



lemma isNonTockDeadlockStateOf_if_isDeadlockStateOf :
    "sigma isDeadlockStateOf VF ==> sigma isNonTockDeadlockStateOf VF"
  apply (simp add: isDeadlockStateOf_def isNonTockDeadlockStateOf_def)
  apply (elim conjE)
  apply (frule refusalsOf_are_subsets_if_isStateOf)
  apply (simp add: refusalSet_def refusesAllNonTockEv_def)
  done

lemma not_isDeadlockStateOf_if_not_isNonTockDeadlockStateOf :
    "isTPN VF ==> fst VF ~= {} ==>
     ~ sigma isNonTockDeadlockStateOf VF ==> ~ sigma isDeadlockStateOf VF"
  apply (rotate_tac -1, erule contrapos_nn)
  by (rule isNonTockDeadlockStateOf_if_isDeadlockStateOf)



lemma isTimeStopStateOf_iff_isNonTockDeadlockStateOf_and_isUrgentStateOf :
    "sigma isTimeStopStateOf V = (sigma isNonTockDeadlockStateOf V & sigma isUrgentStateOf V)"
  apply (simp add: isTimeStopStateOf_def)
  apply (simp add: isNonTockDeadlockStateOf_def)
  apply (simp add: isUrgentStateOf_def)
  apply (force)
done


lemma DeadlockState_iff_UrgentState_and_NonTockDeadlockState :
    "isTPN (I,FXf) ==> I ~= {} ==>
     sigma isStateOf (I,FXf) ==>
     ((sigma isNonTockDeadlockStateOf (I,FXf)) & (sigma isUrgentStateOf (I,FXf))) =
     (sigma isDeadlockStateOf (I,FXf))"
  apply (frule refusalsOf_are_subsets_if_isStateOf)
  apply (simp add: isDeadlockStateOf_def)
  apply (simp add: isUrgentStateOf_def isNonTockDeadlockStateOf_def)
  apply (rule)
  apply (rule, simp add: refusalSet_def)
    apply (simp add: refusesTock_def refusalSet_def refusesAllNonTockEv_def, blast)
  apply (simp add: refusalSet_def refusesTock_def refusesAllNonTockEv_def)
    apply (simp add: Tock_in_Ev_ALP_if_isTPN)
  done


lemma DeadlockState_iff_TimeStopState :
    "isTPN (I,FXf) ==> I ~= {} ==>
     sigma isStateOf (I,FXf) ==>
     (sigma isDeadlockStateOf (I,FXf)) = (sigma isTimeStopStateOf (I,FXf))"
  apply (frule refusalsOf_are_subsets_if_isStateOf)
  apply (simp add: isDeadlockStateOf_def)
  apply (simp add: isTimeStopStateOf_def)
  apply (rule)
  apply (rule, simp add: refusalSet_def)
    apply (simp add: refusesAllNonTockEv_def refusalSet_def)
    apply (simp add: refusesTock_def refusalSet_def)
      apply (simp add: Tock_in_Ev_ALP_if_isTPN)
  apply (simp add: refusesAllNonTockEv_def)
    apply (simp add: refusesTock_def refusalSet_def)
    apply (simp add: ALP_def, blast)
  done


(*subsubsection \<open> States: TimeStopState and NonTockDeadlockState \<close>


lemma not_isTimeStopStateOf_if_isNonTockDeadlockStateOf :
    "sigma isNonTockDeadlockStateOf VF ==>
    ~ (sigma isTimeStopStateOf VF)"
  apply (simp add: isNonTockDeadlockStateOf_def isTimeStopStateOf_def, elim conjE)
  by (rule not_refusesTock_if_refusesAllNonTockEv)


lemma not_isNonTockDeadlockStateOf_if_isTimeStopStateOf :
    "sigma isTimeStopStateOf VF ==>
    ~ (sigma isNonTockDeadlockStateOf VF)"
  apply (erule contrapos_pn)
  by (simp add: not_isTimeStopStateOf_if_isNonTockDeadlockStateOf)



lemma not_isTimeStopStateOf_iff_isNonTockDeadlockStateOf :
    "sigma isStateOf VF ==>
     (sigma isNonTockDeadlockStateOf VF) = (~ sigma isTimeStopStateOf VF & sigma refusesAllNonTockEv VF)"
  apply (rule)

  apply (frule not_isTimeStopStateOf_if_isNonTockDeadlockStateOf, simp)
  apply (simp add: isNonTockDeadlockStateOf_def isTimeStopStateOf_def)
  apply (simp add: isNonTockDeadlockStateOf_def isTimeStopStateOf_def)
  done*)



subsubsection \<open> Sub-States (States for each element) \<close>


lemma EX_urgent_atom :
   "[| (t, Yf) isUrgentStateOf (I, FXf) |] ==>
    EX i: I. (t rest-tr snd (FXf i), Yf) isUrgentStateOf ({i}, FXf)"
  apply (simp add: isUrgentStateOf_def)

  apply (elim conjE)
    apply (simp add: isStateOf_each_element)
    apply (simp add: refusesTock_each_element)
  done


lemma EX_non_urgent_atom_if :
   "[| (t, Yf) isStateOf (I, FXf) ; I ~= {} ;
       ~ (t, Yf) isUrgentStateOf (I, FXf) |] ==>
    EX i: I. ~ (t rest-tr snd (FXf i), Yf) isUrgentStateOf ({i}, FXf)"
  apply (simp only: isUrgentStateOf_def refusesTock_def de_Morgan_conj)
  apply (erule disjE, simp)
  apply (simp add: refusesTock_each_element refusalSet_def)
  apply (simp add: isStateOf_each_element)
  apply (fast)
  done

lemma isUrgentStateOf_if :
   "[| I ~= {} ; (t, Yf) isStateOf (I, FXf) ;
       EX i: I. ALL a b. (a, b) isUrgentStateOf ({i}, FXf) |] ==>
    (t, Yf) isUrgentStateOf (I, FXf)"
  apply (simp only: isUrgentStateOf_def refusesTock_def)
  apply (simp only: de_Morgan_conj disj_not1 snd_conv)

  apply (elim bexE)
  apply (drule_tac x="t rest-tr (snd (FXf i))" in spec)
  apply (drule_tac x=Yf in spec, elim conjE)

  apply (simp add: refusalSet_def)
  apply (fast)
  done

lemma not_refusesTock_if :
   "[| I ~= {} ;
       ALL i: I. ~ (t rest-tr (snd (FXf i)), Yf) refusesTock ({i}, FXf) |] ==>
    ~ (t, Yf) refusesTock (I, FXf)"
  apply (simp only: refusesTock_def)
  apply (simp only: de_Morgan_conj disj_not1 snd_conv)

  apply (rule)

  apply (simp add: refusalSet_def, elim exE conjE)
  apply (fast)
  done

lemma not_isUrgentStateOf_if :
   "[| I ~= {} ;
       ALL i: I. ALL a b. ~ (a, b) isUrgentStateOf ({i}, FXf) |] ==>
    ~ (t, Yf) isUrgentStateOf (I, FXf)"
  apply (simp only: isUrgentStateOf_def refusesTock_def)
  apply (simp only: de_Morgan_conj disj_not1 snd_conv)

  apply (intro allI impI)

  apply (rule)

  apply (simp add: refusalSet_def, elim exE conjE)
  apply (frule isStateOf_each_element, simp)
  apply (fast)
  done



subsubsection \<open> TimeStopState/NonTockDeadlockState + Refusals Predicates \<close>


lemma refusals_are_subsets_if_isTimeStopStateOf :
    "(t,Yf) isTimeStopStateOf (I,FXf) ==>
     ALL i:I. Yf i <= (Ev ` (snd (FXf i)))"
  apply (simp add: isTimeStopStateOf_def, elim conjE)
  by (frule refusals_are_subsets_if_isStateOf, simp)


lemma refusals_are_subsets_if_isNonTockDeadlockStateOf :
    "(t,Yf) isNonTockDeadlockStateOf (I,FXf) ==>
     ALL i:I. Yf i <= (Ev ` (snd (FXf i)))"
  apply (simp add: isNonTockDeadlockStateOf_def, elim conjE)
  by (frule refusals_are_subsets_if_isStateOf, simp)


(*lemma refusals_are_subsetsNonTock_if_not_isTimeStopStateOf :
    "(t,Yf) isStateOf (I,FXf) ==>
     ~ (t,Yf) isTimeStopStateOf (I,FXf) ==>
     ALL i:I. Yf i <= (Ev ` (snd (FXf i))) - {Tock}"
  apply (simp add: isTimeStopStateOf_def)
  by (simp add: refusals_are_subsetsNonTock_if_not_refusesTock)*)



subsubsection \<open> Tock notin refusals TimeStopState/NonTockDeadlockState \<close>


lemma Tock_notin_refusalsOf_if_not_isTimeStopStateOf :
    "sigma isStateOf VF ==> sigma refusesAllNonTockEv VF ==>
     ~ (sigma isTimeStopStateOf VF) ==>
     Tock ~: refusalSet(VF)<snd sigma>"
  apply (simp only: isTimeStopStateOf_def)
  by (simp add: refusesTock_def)


lemma refusals_neq_ALP_diff_Tock_if_not_isNonTockDeadlockStateOf :
    "(t, Yf) isStateOf (I, FXf) ==>
     i : I ==> ~ Yf i <= {Tock} ==>
     ~ (t rest-tr snd (FXf i), Yf) isNonTockDeadlockStateOf ({i}, FXf) ==>
     Yf i ~= Ev ` snd (FXf i) - {Tock}"
  apply (simp add: isNonTockDeadlockStateOf_def)

  apply (frule isStateOf_each_element, simp)
  apply (simp add: refusesAllNonTockEv_def refusalSet_def)
  apply (simp add: isStateOf_def)
  apply (simp add: ALP_def)
  done


subsubsection \<open> Tock in refusals TimeStopState/NonTockDeadlockState \<close>


lemma Tock_in_refusalsOf_if_isTimeStopStateOf :
    "sigma isTimeStopStateOf VF ==>
     Tock : refusalSet(VF)<snd sigma>"
  apply (simp add: isTimeStopStateOf_def)
  by (simp add: refusesTock_def)


lemma ex_Tock_in_refusals_if_isTimeStopStateOf :
    "(t, Yf) isTimeStopStateOf (I, FXf) ==>
     EX i : I. Tock : Yf i"
  apply (frule Tock_in_refusalsOf_if_isTimeStopStateOf)
  apply (simp add: refusalSet_def)
  by (force)



(* i is not refusing event a (~= Tock) from its synchronisation set *)
lemma refusals_neq_ALP_diff_Tock_if_isNonTockDeadlockStateOf :
    "(t, Yf) isStateOf (I, FXf) ==>
     i : I ==> isTPN (I, FXf) ==>
     (t rest-tr snd (FXf i), Yf) isNonTockDeadlockStateOf ({i}, FXf) ==>
     ~ (t rest-tr snd (FXf i), Yf) refusesTock ({i}, FXf) ==>
     Yf i ~= Ev ` snd (FXf i) & Tock ~: Yf i"
  apply (simp add: isNonTockDeadlockStateOf_def)
  apply (drule isStateOf_each_element, simp, simp)
  apply (frule refusesOnlyNonTockEv_if_not_refusesTock_and_refusesAllNonTockEv, simp, simp) 
  apply (simp add: refusesOnlyNonTockEv_def)
  apply (frule isTPN_subset[of _ _ "{i}"], simp)
  apply (drule Tock_in_Ev_ALP_if_isTPN[of "({i},FXf)"], simp)
  by (simp add: refusalSet_def ALP_def, fast)



(*lemma ex_non_refused_nonTock_event_if_not_isTimeStopStateOf :
   "(t, Yf) isStateOf (I, FXf) ==> ~ (t, Yf) isTimeStopStateOf (I, FXf) ==>
    i \<in> I ==> 
    Yf i ~= Ev ` snd (FXf i) - {Tock} ==>
    EX a : Ev ` snd (FXf i). a ~: Yf i & a ~= Tock"
  apply (frule refusals_are_subsets_if_isStateOf)
  apply (frule not_isTimeStopStateOf_each_element, simp, fast)
  apply (simp add: isTimeStopStateOf_def)
  apply (simp add: isTimeStopStateOf_def)
  apply (simp add: refusesTock_def refusalSet_def)
  by (fast)*)



subsection \<open> refusalSet in TimeStopState/NonTockDeadlockState \<close>


(*lemma Union_refusals_eq_ALP_diff_Tock_if_isNonTockDeadlockStateOf :
    "(t, Yf) isNonTockDeadlockStateOf (I, FXf) ==>
     ~ (t, Yf) isTimeStopStateOf (I, FXf) ==>
     refusalSet(I,FXf)<Yf> = EvALP (I,FXf) - {Tock}"
  apply (frule isStateOf_if_isNonTockDeadlockStateOf)
  apply (frule refusals_are_subsetsNonTock_if_not_isTimeStopStateOf)
    apply (simp)
    apply (simp add: isNonTockDeadlockStateOf_def)
    apply (simp add: refusesAllNonTockEv_def) 
  apply (frule refusals_are_subsets_if_isStateOf)
    apply (simp add: refusalSet_def ALP_def)
  by (blast)*)


lemma ALP_Diff_Tock_subset_Union_refusals_if_isNonTockDeadlockStateOf :
    "(t, Yf) isNonTockDeadlockStateOf (I, FXf) ==>
     EvALP (I,FXf) - {Tock} <= refusalSet(I,FXf)<Yf>"
  apply (frule isStateOf_if_isNonTockDeadlockStateOf)
    apply (simp add: isNonTockDeadlockStateOf_def)
    apply (simp add: refusesAllNonTockEv_def)
  done


lemma in_refusals_if_isNonTockDeadlockStateOf :
    "(t, Yf) isNonTockDeadlockStateOf (I, FXf) ==>
     i : I ==> j : I ==> i ~= j ==>
     x : Ev ` snd (FXf i) Int Ev ` snd (FXf j) - {Tock} ==>
     x : refusalSet(I,FXf)<Yf>"
  apply (elim DiffE IntE imageE)

  apply (frule isStateOf_if_isNonTockDeadlockStateOf)
  apply (drule refusalsOf_are_subsets_if_isStateOf)

  apply (simp)
  apply (simp only: isNonTockDeadlockStateOf_def)
  apply (simp add: refusesAllNonTockEv_def)

  apply (elim conjE)
  apply (simp add: ALP_def)
  apply (elim subsetE)
  apply (drule_tac x="Ev xa" in bspec)
  apply (drule_tac x="Ev xa" in bspec, simp, fast, simp)
  apply (simp add: image_iff)
  done




subsection \<open> Refusals PXf --> FXf \<close>

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







subsection \<open> Busyness \<close>

(*lemma NonTockBusyNetwork_if_BusyNetwork :
    ""*)


(*lemma TockBusyNetwork_if_BusyNetwork :
    "BusyNetwork VF ==>
     TockBusyNetwork VF"
  apply (simp add: BusyNetwork_def)
  apply (simp add: TockBusyNetwork_def)
  apply (intro ballI allI)
  apply (simp add: isTimeStopStateOf_if_isDeadlockStateOf)
  apply (rule contrapos_nn)*)


end