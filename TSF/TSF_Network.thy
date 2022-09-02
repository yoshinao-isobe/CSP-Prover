theory TSF_Network
imports TSF_Blocked
        TSF_law
begin


subsection \<open> TimeStopFreeNetwork \<close>


definition TimeStopFreeNetwork :: "('i,'p,'e::tockCSP) Network => bool" 
where
  "TimeStopFreeNetwork V == isTockNet V &
                            [Ev ` (ALP V)]-TimeStopFree (PAR V)"







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




lemma TimeStopFreeNetwork_iff_DeadlockFree_PAR_Nontock :
    "fst V \<noteq> {} \<Longrightarrow> isTockNet V \<Longrightarrow>
     TimeStopFreeNetwork V = [Ev ` (ALP V) \<union> {Tick}]-DeadlockFree ((PAR V) -- Nontock)"
  apply (subst Tock_in_Ev_ALP_if_isTockNet_V, simp, simp)
  apply (simp add: TimeStopFreeNetwork_def TimeStopFree_def)
  done

lemma unfolded_DeadlockFree_PAR_Hiding_notNonTockDeadlockState:
  "[| isTockNet (I,PXf) ; I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) |]
   ==> (\<forall>s. Tick \<notin> sett s \<longrightarrow> (s, (Ev ` ALP (I, PXf)) Un {Tick}) ~:f failures ((PAR (I, PXf)) -- Nontock) MF) = 
       (ALL sigma. ~(sigma isNonTockDeadlockStateOf (I,FXf)))"

  apply (frule isTockNet_FXf_if_isTockNet_PXf, simp)
  apply (subst ALP_PXf_iff_ALP_FXf_if_isFailureOf, simp)
  apply (simp only: isNonTockDeadlockStateOf_def)
  apply (simp only: in_failures_Hiding hide_tr_sym)

  apply (rule)

  apply (rule)
defer
  apply (simp add: image_iff ALP_def)
  apply (insert ex_in_conv[of I], simp)

  sorry

end