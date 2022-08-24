theory tockCSP_Network
imports tockCSP_DFP_Main
begin



subsection \<open> NonTockBusyNetwork \<close>


abbreviation isTockNetObj :: "('x * 'e::tockCSP set) \<Rightarrow> bool"
where
  "isTockNetObj X == (tock : (snd X))"


abbreviation isTockNet :: "('i set * ('i => ('b * 'e::tockCSP set))) \<Rightarrow> bool"
where
  "isTockNet V == (ALL i: fst V. isTockNetObj ((snd V) i))"




subsubsection \<open> States: isTimeStopStateOf and isNonTockDeadlockStateOf \<close>


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



subsubsection \<open> NonTockBusyNetwork Definition \<close>


definition NonTockBusyNetwork  :: "('i,'e::tockCSP) NetworkF => bool"
where
    "NonTockBusyNetwork VF == BusyNetwork VF &
                              ~ (EX sigma. sigma isTimeStopStateOf VF)"



subsection \<open> Laws \<close>


subsubsection \<open> PXf <--> FXf \<close>


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


lemma ALP_PXf_iff_ALP_FXf_if_isFailureOf :
    "(I,FXf) isFailureOf (I,PXf) \<Longrightarrow> ALP (I,PXf) = ALP (I,FXf)"
   by (simp add: isFailureOf_def ALP_def)

lemma ALP_FXf_iff_ALP_PXf_if_isFailureOf :
    "(I,FXf) isFailureOf (I,PXf) \<Longrightarrow> ALP (I,FXf) = ALP (I,PXf)"
   by (simp add: isFailureOf_def ALP_def)



subsubsection \<open> Tock, NonTockEv and ALP \<close>


lemma NonTockEv_ALP_eq_EvsetTick_if_isTockNet :
    "isTockNet (I, PXf) \<Longrightarrow> I \<noteq> {} \<Longrightarrow>
    NonTockEv \<union> Ev ` ALP (I, PXf) = EvsetTick"
  apply (rule NonTockEv_Un_eq_EvsetTick_if)
  by (simp add: ALP_def image_def, auto)


lemma NonTockEv_Un_absorb :
    "Tock \<notin> X \<Longrightarrow> NonTockEv \<union> X = NonTockEv"
  by (auto simp only: NonTockEv_simp EvsetTick_def)


lemma NonTockEv_neq_ALP :
    "isTockNet (I, PXf) \<Longrightarrow> I \<noteq> {} \<Longrightarrow>
    NonTockEv \<noteq> Ev ` ALP (I, PXf)"
  apply (simp add: NonTockEv_simp EvsetTick_def)
  by (simp add: ALP_def image_def, auto)



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



end