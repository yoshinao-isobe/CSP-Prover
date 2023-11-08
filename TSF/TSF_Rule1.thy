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

theory TSF_Rule1
imports TSF_Lemma3
begin


subsection \<open> Hereditary Time-stop free Network \<close>

text \<open> For Rule 1 in Jesus and Sampaio's SBMF 2022 paper
       see Rule1_Jesus_Sampaio_2022 below. \<close>

lemma Rule1_Jesus_Sampaio_2023:
    "[| isTPN (I,PXf); I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) ;
        tock_triple_conjoint (I,FXf) ; NonTockBusyNetwork (I,FXf) ; TockBusyNetwork (I,FXf) ;
        ALL sigma. sigma isNonTockDeadlockStateOf (I,FXf) ;
        ALL i:I. \<not> Ev ` snd (FXf i) \<subseteq> {Tock} ; 
        EX f::('i => 'a::tockCSP failure => ('pi::order)) .
        ALL i:I. ALL j:I. i ~= j -->
            (ALL t Yf.
            ({i,j},FXf) >> i --tock[(t,Yf), (VocabularyOf (I,FXf))]-->o j-->
                       f j (t rest-tr (snd (FXf j)), Yf j) <
                       f i (t rest-tr (snd (FXf i)), Yf i)) |]
     ==> TimeStopFreeNetwork (I,PXf)"
  apply (rule Theorem1_Jesus_Sampaio_2022)
  apply (simp_all)
  apply (rule Lemma3_Jesus_Sampaio_2023)
  apply (simp_all)
  apply (simp add: isUngrantedNonTockRequestOfwrt_def)
  apply (simp add: isUngrantedNonTockRequestOf_def)
  apply (simp add: hasNonTockRequestFor_def)
  apply (simp add: isRequestOf_def)
  done

lemma Rule1_Jesus_Sampaio_2023_I:
    "[| isTPN V; I ~= {} ; finite I ; (I,FXf) isFailureOf V ;
        tock_triple_conjoint (I,FXf) ; NonTockBusyNetwork (I,FXf) ; TockBusyNetwork (I,FXf) ;
        ALL sigma. sigma isNonTockDeadlockStateOf (I,FXf) ;
        ALL i:I. \<not> Ev ` snd (FXf i) \<subseteq> {Tock} ;
        EX f::('i => 'a::tockCSP failure => ('pi::order)).
        ALL i:I. ALL j:I. i ~= j -->
            (ALL t Yf. ({i,j},FXf) >> i --tock[(t,Yf), (VocabularyOf (I,FXf))]-->o j -->
                   f j (t rest-tr (snd (FXf j)), Yf j) <
                   f i (t rest-tr (snd (FXf i)), Yf i)) |]
     ==> TimeStopFreeNetwork V"
  apply (insert decompo_V[of V])
  apply (rotate_tac -1, erule exE)
  apply (rotate_tac -1, erule exE)
  apply (subgoal_tac "Ia = I")
  apply (simp)
  apply (subst Rule1_Jesus_Sampaio_2023, simp_all)
  apply (simp add: isFailureOf_def)
  done

(*** looks test ***)

theorem Rule1_Jesus_Sampaio_2023_simp:
    "[| VF = {(F i, X i) | i:I}Fnet ; V = {(P i, X i) | i:I}net ;
        VF isFailureOf V ; I ~= {} ; finite I ; isTPN VF ;
        tock_triple_conjoint VF ; NonTockBusyNetwork VF ; TockBusyNetwork VF ;
        ALL sigma. sigma isNonTockDeadlockStateOf VF ;
        ALL i:I. ~ Ev ` snd (snd VF i) <= {Tock} ;
        EX f::('i => 'a::tockCSP failure => ('pi::order)).
        ALL i:I. ALL j:I. i ~= j -->
        (ALL t Y.
         {(F i, X i) | i:{i,j}}Fnet >> 
                 i --tock[(t,Y), (VocabularyOf VF)]-->o j
                   --> f j (t rest-tr (X j), Y j)
                     < f i (t rest-tr (X i), Y i)) |]
     ==> TimeStopFreeNetwork V"
  apply (simp)
  apply (rule Rule1_Jesus_Sampaio_2023_I)
  apply (simp_all add: isTPN_def, simp)
  apply (elim conjE exE)
  apply (rule_tac x="f" in exI)
  apply (auto)
  done

end