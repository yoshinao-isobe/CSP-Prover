theory tockCSP_Network
imports tockCSP_DFP_Main
begin



subsection \<open> TimeStopFree Network \<close>


(*definition TockNet :: "('i,'p,'e) Network \<Rightarrow> ('i,'p,'e::tockCSP) Network"
where
  "TockNet V == (fst V, \<lambda>i. case (snd V i) of (p, a) \<Rightarrow> (p, a \<union> {tock}))"*)


abbreviation isTockNetObj :: "('x * 'e::tockCSP set) \<Rightarrow> bool"
where
  "isTockNetObj X == (tock : (snd X))"


abbreviation isTockNet :: "('i set * ('i => ('b * 'e::tockCSP set))) \<Rightarrow> bool"
where
  "isTockNet V == (ALL i: fst V. isTockNetObj ((snd V) i))"




subsection \<open> States: isTimeStopStateOf and isNonTockDeadlockStateOf \<close>


definition isTimeStopStateOf :: "('i,'e) net_state => ('i,'e::tockCSP) NetworkF => bool"
                           ("(0_ isTimeStopStateOf _)" [55,55] 55)
where
   "sigma isTimeStopStateOf VF == sigma isStateOf VF &
                                  Tock : Union {((snd sigma) i) |i. i : fst VF}"
(*
  SOMEONE REFUSES Tock    \<Longrightarrow>     Tock : Union {((snd sigma) i) |i. i : fst VF}
  EVERYONE REFUSES Tock   \<Longrightarrow>     Tock : Inter ...

  WHETHER SOMEONE REFUSES Tock, IT WANTS TO CONTROL THE PASSAGE OF TIME
*)


definition isNonTockDeadlockStateOf :: "('i,'e) net_state => ('i,'e::tockCSP) NetworkF => bool"
                           ("(0_ isNonTockDeadlockStateOf _)" [55,55] 55)
where 
   "sigma isNonTockDeadlockStateOf VF == 
                sigma isDeadlockStateOf VF &
                ~ (sigma isTimeStopStateOf VF)"



subsection \<open> NonTockBusyNetwork \<close>


definition NonTockBusyNetwork  :: "('i,'e::tockCSP) NetworkF => bool"
where
    "NonTockBusyNetwork VF == BusyNetwork VF &
                              ~ (EX sigma. sigma isTimeStopStateOf VF)"



(*definition
  isNonTockDeadlockStateOf :: 
   "('i,'e) net_state => ('i,'e::tockCSP) NetworkF => bool"
                           ("(0_ isNonTockDeadlockStateOf _)" [55,55] 55)
  where
  isNonTockDeadlockStateOf_def : 
   "sigma isNonTockDeadlockStateOf VF == 
                sigma isStateOf VF & 
                Union {((snd sigma) i) |i. i : fst VF}
                = Ev ` (ALP VF) - {Tock}"
  
definition  
  NonTockBusyNetwork  :: "('i,'e::tockCSP) NetworkF => bool"
  where
  NonTockBusyNetwork_def :
    "NonTockBusyNetwork VF == 
     ALL i: fst VF. (ALL sigma. ~(sigma isNonTockDeadlockStateOf ({i}, snd VF)))"
*)



subsection \<open> Laws \<close>


(*lemma isTockNet_TockNet :
   "isTockNet (TockNet V)"
  apply (simp add: TockNet_def)
  apply (case_tac V, clarsimp)
  apply (case_tac "b i", clarsimp)
  done*)


lemma isTockNetObj_FXf_if_isTockNetObj_PXf :
    "(I,FXf) isFailureOf (I,PXf) \<Longrightarrow> ALL i:I. isTockNetObj (PXf i) \<Longrightarrow> ALL i:I. isTockNetObj (FXf i)"
  by (simp add: isFailureOf_def)

lemma isTockNetObj_PXf_if_isTockNetObj_FXf :
    "(I,FXf) isFailureOf (I,PXf) \<Longrightarrow> ALL i:I. isTockNetObj (FXf i) \<Longrightarrow> ALL i:I. isTockNetObj (PXf i)"
  by (simp add: isFailureOf_def)


lemma isTockNet_FXf_if_isTockNet_PXf :
    "(I,FXf) isFailureOf (I,PXf) \<Longrightarrow> isTockNet (I,PXf) \<Longrightarrow> isTockNet (I,FXf)"
  by (simp add: isFailureOf_def)


lemma isTockNet_PXf_if_isTockNet_FXf :
    "(I,FXf) isFailureOf (I,PXf) \<Longrightarrow> isTockNet (I,FXf) \<Longrightarrow> isTockNet (I,PXf)"
  by (simp add: isFailureOf_def)



lemma NonTockEv_ALP_eq_EvsetTick_if_isTockNet :
    "isTockNet (I, PXf) \<Longrightarrow> I \<noteq> {} \<Longrightarrow>
    NonTockEv \<union> Ev ` ALP (I, PXf) = EvsetTick"
  apply (simp add: NonTockEv_simp EvsetTick_def)
  by (simp add: ALP_def image_def, auto)


lemma ALP_PXf_iff_ALP_FXf_if_isFailureOf :
    "(I,FXf) isFailureOf (I,PXf) \<Longrightarrow> ALP (I,PXf) = ALP (I,FXf)"
   by (simp add: isFailureOf_def ALP_def)


lemma Tock_in_Ev_ALP_if_isTockNet :
    "I \<noteq> {} \<Longrightarrow> isTockNet (I, PXf) \<Longrightarrow>
    Tock \<in> Ev ` ALP (I, PXf)"
  apply (simp add: ALP_def image_def)
  by (force)


lemma Tock_in_Ev_ALP_if_isTockNet_V :
    "fst V \<noteq> {} \<Longrightarrow>
     isTockNet V \<Longrightarrow> Ev ` (ALP V) = Ev ` (ALP V) \<union> {Tock}"
  apply (simp add: ALP_def)
  apply (rule insert_absorb[THEN sym])
  by (auto simp add: image_def)


(*lemma PAR_TockNet_simp :
    "PAR TockNet V = [||]i:(fst V) .. (case (snd V i) of (p, a) \<Rightarrow> (p, a \<union> {tock}))"
  by (simp add: TockNet_def PAR_def)*)


(*lemma ALP_TockNet_simp :
    "fst V \<noteq> {} \<Longrightarrow>
     ALP (TockNet V) = ALP V \<union> {tock}"
  apply (simp add: TockNet_def ALP_def)
  apply (case_tac V, simp)
  apply (simp only: ex_in_conv[THEN sym], elim exE)
  apply (safe)
  apply (case_tac "b i", simp, force)
  apply (rule_tac x=x in bexI)
  apply (case_tac "b x", simp, simp)
  apply (rule_tac x=i in bexI)
  apply (case_tac "b i", simp_all)
  done*)

end