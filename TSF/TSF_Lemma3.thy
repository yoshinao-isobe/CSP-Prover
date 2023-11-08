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

theory TSF_Lemma3
imports TSF_Theorem3
begin


subsection \<open> TimeStopFreeNetwork local analysis \<close>

text \<open> For Lemma 3 in Jesus and Sampaio's SCP 2023 paper
       see Lemma3_Jesus_Sampaio_2023 below. \<close>

lemma Lemma3_Jesus_Sampaio_2023:
    "[| I ~= {} ; finite I ;
        EX f::('i => 'a::tockCSP failure => ('pi::order)).
           ALL i:I. ALL j:I. i ~= j -->
           (ALL t Yf. (t,Yf) isStateOf ({i,j},FXf) &
                      ({i,j},FXf) >> i --tock[(t,Yf), (VocabularyOf (I,FXf))]-->o j -->
                      f j (t rest-tr (snd (FXf j)), Yf j) <
                      f i (t rest-tr (snd (FXf i)), Yf i)) |] ==>
     EX f::('i => 'a::tockCSP failure => ('pi::order)).
        ALL t Yf. (t,Yf) isStateOf (I,FXf) -->
        (ALL i j. (I,FXf) >> i --tock[(t,Yf), (VocabularyOf (I,FXf))]-->o j -->
                  f j (t rest-tr (snd (FXf j)), Yf j) <
                  f i (t rest-tr (snd (FXf i)), Yf i))"
  apply (elim exE)
  apply (rule_tac x="f" in exI)
  apply (intro allI impI)
  apply (drule_tac x="i" in bspec)
  apply (simp add: in_index_NonTock_I)
  apply (drule_tac x="j" in bspec)
  apply (simp add: in_index_NonTock_I)
  apply (simp add: in_index_NonTock_I)
  
  apply (drule_tac x="t rest-tr ((snd (FXf i) Un snd (FXf j)))" in spec)
  apply (drule_tac x="Yf" in spec)
  apply (drule mp)
   apply (rule conjI)
   apply (rule isStateOf_subsetI)
   apply (simp)
   apply (simp add: in_index_NonTock_I)
   apply (blast)
   apply (rule isUngrantedNonTockRequestOfwrt_subsetI)
   apply (simp add: in_index_NonTock_I)
   apply (simp add: in_index_NonTock_I)
   apply (fast)
   apply (fast)
   apply (fast)
   apply (fast)
  
   apply (subgoal_tac 
      "t rest-tr ((snd (FXf i) Un snd (FXf j))) rest-tr (snd (FXf i))
     = t rest-tr (snd (FXf i))")
   apply (subgoal_tac 
      "t rest-tr ((snd (FXf i) Un snd (FXf j))) rest-tr (snd (FXf j))
     = t rest-tr (snd (FXf j))")
   apply (simp)
   apply (rule rest_tr_of_rest_tr_subset)
   apply (force)
   apply (rule rest_tr_of_rest_tr_subset)
   apply (force)
  done


end