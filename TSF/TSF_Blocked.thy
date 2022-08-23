theory TSF_Blocked
imports tockCSP_Network
begin



subsection \<open> tock_triple_conjoint \<close>


definition tock_triple_conjoint :: "('i set * ('i => ('b * 'e::tockCSP set))) => bool"
where
    "tock_triple_conjoint VF == 
       (ALL i: fst VF. ALL j: fst VF. ALL k: fst VF. i ~= j & j ~= k & k ~= i
          --> (snd ((snd VF) i) Int snd ((snd VF) j) Int snd ((snd VF) k) = {tock}))"


subsection \<open> Requests \<close>


definition isUngrantedNonTockRequestOf :: "('i,'e) NetworkF => 'i => ('i,'e::tockCSP) net_state => 'i => bool"
      ("(1_ >> /(0_ (1/--tock[_]-->o) /_))" [800, 800,0,800] 900)
where
    "VF >> i --tock[sigma]-->o j == VF >> i --[sigma]--> j & ~ (sigma isTimeStopStateOf VF) &
        Ev ` (snd (snd VF i)) Int Ev ` (snd (snd VF j)) - {Tock}
        <= (snd sigma) i Un (snd sigma) j"

definition isUngrantedNonTockRequestOfwrt :: "('i,'e) NetworkF => 'i => ('i,'e) net_state => 'e::tockCSP set => 'i => bool"
      ("(1_ >> /(0_ (1/--tock[(0_,/_)]-->o) /_))" [800, 800,0,0,800] 900)
where
    "VF >> i --tock[sigma,Lambda]-->o j == VF >> i --tock[sigma]-->o j &
        ((Ev ` (snd (snd VF i))) - (snd sigma) i) Un
        ((Ev ` (snd (snd VF j))) - (snd sigma) j) <= Ev ` Lambda"



subsection \<open> BlockedIn \<close>


definition  isBlockedInNonTock :: "('i,'e) NetworkF => 'i => ('i,'e::tockCSP) net_state => bool"
      ("(_ >> _ isBlockedInNonTock _)" [800, 800, 800] 900)
where
    "VF >> i isBlockedInNonTock sigma == 
          tock_triple_conjoint VF &
          (EX j. VF >> i --[sigma]--> j) &
          (ALL j. VF >> i --[sigma]--> j
          --> (VF >> i --tock[sigma, (VocabularyOf VF) - {tock}]-->o j))"




subsection \<open> Auxiliary lemmas \<close>


subsubsection \<open> Auxiliary lemmas - in index I \<close>

lemma in_index_NonTock_I1:
  "(I, FXf) >> i --tock[sigma]-->o j ==> i : I & j : I & i ~= j"
apply (simp add: isUngrantedNonTockRequestOf_def)
apply (elim conjE)
by (simp add: in_index_I)

lemma in_index_NonTock_I2:
  "(I, FXf) >> i --tock[sigma,Lambda]-->o j ==> i : I & j : I & i ~= j"
apply (simp add: isUngrantedNonTockRequestOfwrt_def)
apply (elim conjE)
by (simp add: in_index_NonTock_I1)

lemmas in_index_NonTock_I = in_index_NonTock_I1 in_index_NonTock_I2



subsubsection \<open> Auxiliary lemmas - sub request \<close>

lemma isUngrantedNonTockRequestOf_subsetI:
  "[| (I, FXf) >> i --tock[(t,Yf)]-->o j; J <= I; i:J ; j:J ; 
      X = Union {snd (FXf i)|i. i:J} |]
   ==> (J, FXf) >> i --tock[(t rest-tr X,Yf)]-->o j"
apply (simp add: isUngrantedNonTockRequestOf_def)
apply (rule)
apply (rule isRequestOf_subsetI, simp_all)
apply (simp add: isTimeStopStateOf_def, elim conjE)
apply (rule)
apply (simp add: isRequestOf_def, elim conjE)
apply (rule)
apply (drule_tac x=x in spec, fast)
done

lemma isUngrantedNonTockRequestOfwrt_subsetI:
  "[| (I, FXf) >> i --tock[(t,Yf), Lambda1]-->o j; J <= I; i:J ; j:J ; 
      Lambda1 <= Lambda2 ; X = Union {snd (FXf i)|i. i:J} |]
   ==> (J, FXf) >> i --tock[(t rest-tr X,Yf), Lambda2]-->o j"
apply (simp add: isUngrantedNonTockRequestOfwrt_def)
apply (rule conjI)
apply (rule isUngrantedNonTockRequestOf_subsetI)
apply (simp_all)
apply (blast)
done



subsubsection \<open> Auxiliary lemmas - is________StateOf \<close>

lemma isDeadlockStateOf_if_isNonTockDeadlockStateOf :
    "(t, Yf) isNonTockDeadlockStateOf (I, FXf) \<Longrightarrow>
    (t, Yf) isDeadlockStateOf (I, FXf)"
  by (simp add: isNonTockDeadlockStateOf_def)
(*  by (simp add: isDeadlockStateOf_def) *)


lemma BusyNetwork_if_NonTockBusyNetwork :
    "NonTockBusyNetwork (I, FXf) \<Longrightarrow> BusyNetwork (I, FXf)"
  by (simp add: NonTockBusyNetwork_def)



lemma not_isTimeStopStateOf_if_isNonTockDeadlockStateOf :
    "sigma isNonTockDeadlockStateOf VF \<Longrightarrow>
    ~ (sigma isTimeStopStateOf VF)"
  by (simp add: isNonTockDeadlockStateOf_def)



lemma Tock_notin_refusals_if_not_isTimeStopStateOf :
    "~ (sigma isTimeStopStateOf VF) \<Longrightarrow> sigma isStateOf VF \<Longrightarrow>
    Tock \<notin> Union {((snd sigma) i) |i. i : fst VF}"
  by (simp add: isTimeStopStateOf_def)


lemma Tock_notin_refusals_if_isNonTockDeadlockStateOf :
    "sigma isNonTockDeadlockStateOf VF \<Longrightarrow>
    Tock \<notin> Union {((snd sigma) i) |i. i : fst VF}"
  apply (simp only: isNonTockDeadlockStateOf_def)
  apply (simp only: isDeadlockStateOf_def, elim conjE)
  by (simp add: isTimeStopStateOf_def)



lemma refusals_are_subsets_if_isStateOf :
    "(t,Yf) isStateOf (I,FXf) \<Longrightarrow>
     ALL i:I. Yf i <= (Ev ` (snd (FXf i)))"
  apply (simp add: isStateOf_def)
  done

lemma refusals_are_subsets_if_isDeadlockStateOf :
    "(t,Yf) isDeadlockStateOf (I,FXf) \<Longrightarrow>
     ALL i:I. Yf i <= (Ev ` (snd (FXf i)))"
  apply (simp only: isDeadlockStateOf_def, elim conjE)
  apply (rule refusals_are_subsets_if_isStateOf, simp)
  done

lemma refusals_are_subsets_if_isNonTockDeadlockStateOf :
    "(t,Yf) isNonTockDeadlockStateOf (I,FXf) \<Longrightarrow>
     ALL i:I. Yf i <= (Ev ` (snd (FXf i)))"
  apply (simp only: isNonTockDeadlockStateOf_def, elim conjE)
  apply (rule refusals_are_subsets_if_isDeadlockStateOf, simp)
  done
                             

lemma in_refusals_if_isDeadlockStateOf :
    "(t, Yf) isDeadlockStateOf (I, FXf) \<Longrightarrow>
     i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow>
     x \<in> Ev ` snd (FXf i) \<inter> Ev ` snd (FXf j) \<Longrightarrow>
     x : Union {Yf i |i. i : I}"
  apply (simp add: isDeadlockStateOf_def)

  apply (simp add: isStateOf_def)
  apply (simp add: ALP_def)
  apply (simp add: image_iff)
  apply (elim conjE bexE, simp)
  
  apply (rule_tac x="i" in bexI)
  apply (simp, simp)
  done

lemma in_refusals_if_isNonTockDeadlockStateOf :
    "(t, Yf) isNonTockDeadlockStateOf (I, FXf) \<Longrightarrow>
     i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow>
     x \<in> Ev ` snd (FXf i) \<inter> Ev ` snd (FXf j) - {Tock} \<Longrightarrow>
     x : Union {Yf i |i. i : I}"
  apply (frule isDeadlockStateOf_if_isNonTockDeadlockStateOf)
  apply (drule in_refusals_if_isDeadlockStateOf, simp_all)
  by (simp)



lemma ex_Request_if_isDeadlockStateOf_BusyNetwork :
    "(t, Yf) isDeadlockStateOf (I, FXf) \<Longrightarrow>
     i \<in> I \<Longrightarrow> BusyNetwork (I, FXf) \<Longrightarrow>
     EX j. (I, FXf) >> i --[(t, Yf)]--> j"

  (* busy --> i is deadlock-free *)
  apply (simp only: BusyNetwork_def)
  apply (drule_tac x="i" in bspec, simp)

  (* Refusals are subsets *)
  apply (frule refusals_are_subsets_if_isDeadlockStateOf)

  apply (simp add: isRequestOf_def)
  apply (simp add: isDeadlockStateOf_def)

    (* EX j *)
    apply (elim conjE)

    (* Refusals i *)
    apply (frule_tac x="i" in bspec, simp)
  
    apply (drule_tac x="t rest-tr (snd (FXf i))" in spec)
    apply (drule_tac x="Yf" in spec)
    apply (drule mp)
    apply (rule isStateOf_each_element, simp, simp)
    apply (simp add: ALP_def)

    apply (subgoal_tac "EX a: Ev ` snd (FXf i). a ~: Yf i")        (* ... sub 1 *)
    apply (elim bexE)
    apply (subgoal_tac "a : Ev ` {a. EX i:I. a : snd (FXf i)}")    (* ... sub 2 *)
      apply (rotate_tac 5)
      apply (drule sym)
      apply (simp)
      apply (elim conjE exE)
      apply (simp)
      apply (rule_tac x="ia" in exI)
      apply (case_tac "i = ia", simp)
      apply (simp)
      apply (drule_tac x="ia" in bspec, simp)
      apply (simp only: Int_commute Int_Diff[THEN sym])
      apply (rule)
      apply (fast)

     (* sub 2 *)
     apply (blast)
    (* sub 1 *)
    apply (blast)
  done


lemma ex_Request_if_isNonTockDeadlockStateOf_NonTockBusyNetwork :
    "(t, Yf) isNonTockDeadlockStateOf (I, FXf) \<Longrightarrow>
     i \<in> I \<Longrightarrow> NonTockBusyNetwork (I, FXf) \<Longrightarrow>
     \<exists>j. (I, FXf) >> i --[(t, Yf)]--> j"
  apply (frule isDeadlockStateOf_if_isNonTockDeadlockStateOf)
  apply (frule BusyNetwork_if_NonTockBusyNetwork)
  apply (rule ex_Request_if_isDeadlockStateOf_BusyNetwork, simp_all)
  done



lemma tock_notin_refusals_if_isNonTockDeadlockStateOf :
    "(t, Yf) isNonTockDeadlockStateOf (I, FXf) \<Longrightarrow>
       x \<in> \<Union> {Yf i |i. i \<in> I} \<Longrightarrow> x \<noteq> Tock"
  apply (frule Tock_notin_refusals_if_isNonTockDeadlockStateOf)
  by (force)


lemma tock_notin_refusals_if_isNonTockDeadlockStateOf2 :
    "(t, Yf) isNonTockDeadlockStateOf (I, FXf) \<Longrightarrow>
       Ev x \<in> Yf i \<Longrightarrow> i \<in> I \<Longrightarrow> x \<noteq> tock"
  apply (frule Tock_notin_refusals_if_isNonTockDeadlockStateOf)
  by (force)







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



lemma tock_triple_conjoint_PXf_FXf :
    "tock_triple_conjoint (I,PXf) \<Longrightarrow> (I,FXf) isFailureOf (I,PXf) \<Longrightarrow>
     tock_triple_conjoint (I,FXf)"
  apply (simp add: tock_triple_conjoint_def)
  by (simp add: isFailureOf_def)




end