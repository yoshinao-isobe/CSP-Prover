           (*-------------------------------------------*
            |                DFP package                |
            |                    May 2005               |
            |               December 2005  (modified)   |
            |                                           |
            |   DFP on CSP-Prover ver.3.0               |
            |              September 2006  (modified)   |
            |                  April 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory DFP_Block
imports DFP_Deadlock
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  Union (B ` A) = (UN x:A. B x)                      *)
(*                  Inter (B ` A) = (INT x:A. B x)                     *)
(*
declare Union_image_eq [simp del]
declare Inter_image_eq [simp del]
*)

(* no simp rules in Isabelle 2017 
declare Sup_image_eq [simp del]
declare Inf_image_eq [simp del]
*)

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite (notick | t = []t)                 *)
(*                                                                     *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*****************************************************************

         1. 
         2. 
         3. 
         4. 

 *****************************************************************)

(*********************************************************
                    definitions
 *********************************************************)

definition
  triple_disjoint :: "('i,'a) NetworkF => bool"
  where
  triple_disjoint_def :
    "triple_disjoint VF == 
       (ALL i: fst VF. ALL j: fst VF. ALL k: fst VF. i ~= j & j ~= k & k ~= i
          --> (snd ((snd VF) i) Int snd ((snd VF) j) Int snd ((snd VF) k) = {}))"

definition
  VocabularyOf :: "('i,'a) NetworkF => 'a set"
  where
  VocabularyOf_def : 
    "VocabularyOf VF == 
     Union {X. EX i: fst VF. EX j: fst VF. i ~= j &
               X = snd((snd VF) i) Int snd((snd VF) j)}"
    (* internal communication *)

definition  
  BusyNetworkP :: "('i,'p,'a) Network => bool"
  where
  BusyNetworkP_def : 
    "BusyNetworkP V == 
     ALL i: fst V. DeadlockFreeNetwork ({i}, snd V)"
  
definition  
  BusyNetwork  :: "('i,'a) NetworkF => bool"
  where
  BusyNetwork_def : 
    "BusyNetwork VF == 
     ALL i: fst VF. (ALL sigma. ~(sigma isDeadlockStateOf ({i}, snd VF)))"

definition
  isRequestOf :: "('i,'a) NetworkF => 'i => ('i,'a) net_state => 'i => bool"
     ("(1_ >> /(0_ (1/--[_]-->) /_))" [800, 800,100,800] 900)
  where
  isRequestOf_def :
    "VF >> i --[sigma]--> j == 
        sigma isStateOf VF & 
        i ~= j & i : fst VF & j : fst VF &
        (Ev ` (snd (snd VF i)) - (snd sigma) i) Int 
         Ev ` (snd (snd VF j)) ~= {}"

definition
  isStrongRequestOf :: "('i,'a) NetworkF => 'i => ('i,'a) net_state => 'i => bool"
     ("(1_ >> /(0_ (1/==[_]==>) /_))" [800, 800,100,800] 900)
  where
  isStrongRequestOf_def :
    "VF >> i ==[sigma]==> j == 
        sigma isStateOf VF & 
        i ~= j & i : fst VF & j : fst VF &
        Ev ` (snd (snd VF i)) - (snd sigma) i ~= {} &
        Ev ` (snd (snd VF i)) - (snd sigma) i <= Ev ` (snd (snd VF j))"

definition
  isUngrantedRequestOf ::
      "('i,'a) NetworkF => 'i => ('i,'a) net_state => 'i => bool"
      ("(1_ >> /(0_ (1/--[_]-->o) /_))" [800, 800,0,800] 900)
  where
  isUngrantedRequestOf_def :
    "VF >> i --[sigma]-->o j == VF >> i --[sigma]--> j &
        Ev ` (snd (snd VF i)) Int Ev ` (snd (snd VF j))
        <= (snd sigma) i Un (snd sigma) j"
  
definition
  isUngrantedStrongRequestOf ::
      "('i,'a) NetworkF => 'i => ('i,'a) net_state => 'i => bool"
      ("(1_ >> /(0_ (1/==[_]==>o) /_))" [800, 800,0,800] 900)
  where
  isUngrantedStrongRequestOf_def :
    "VF >> i ==[sigma]==>o j == VF >> i ==[sigma]==> j &
        Ev ` (snd (snd VF i)) Int Ev ` (snd (snd VF j))
        <= (snd sigma) i Un (snd sigma) j"

definition
  isUngrantedRequestOfwrt ::
      "('i,'a) NetworkF => 'i => ('i,'a) net_state => 'a set => 'i => bool"
      ("(1_ >> /(0_ (1/--[(0_,/_)]-->o) /_))" [800, 800,0,0,800] 900)
  where
  isUngrantedRequestOfwrt_def :
    "VF >> i --[sigma,Lambda]-->o j == VF >> i --[sigma]-->o j &
        ((Ev ` (snd (snd VF i))) - (snd sigma) i) Un
        ((Ev ` (snd (snd VF j))) - (snd sigma) j) <= Ev ` Lambda"

(*** Block ***)

definition
  isBlockedIn ::
      "('i,'a) NetworkF => 'i => ('i,'a) net_state => bool"
      ("(_ >> _ isBlockedIn _)" [800, 800, 800] 900)
  where
  isBlockedIn_def :
    "VF >> i isBlockedIn sigma == 
          triple_disjoint VF &
          (EX j. VF >> i --[sigma]--> j) &
          (ALL j. VF >> i --[sigma]--> j
          --> (VF >> i --[sigma, (VocabularyOf VF)]-->o j))"

(*********************************************************
                  BusyNetwork lemmas
 *********************************************************)

lemma BusyNetwork_BusyNetworkP :
    "[| I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) |]
     ==> BusyNetwork (I,FXf) = BusyNetworkP (I,PXf)"
apply (simp add: BusyNetwork_def)
apply (simp add: BusyNetworkP_def)
apply (rule)

 apply (rule ballI)
 apply (drule_tac x="i" in bspec, simp)
 apply (subgoal_tac "({i}, FXf) isFailureOf ({i}, PXf)")
 apply (simp add: DeadlockFree_notDeadlockState)
 apply (rule isFailureOf_subset_index)
 apply (simp)
 apply (simp)

 apply (rule ballI)
 apply (drule_tac x="i" in bspec, simp)
 apply (subgoal_tac "({i}, FXf) isFailureOf ({i}, PXf)")
 apply (simp add: DeadlockFree_notDeadlockState)
 apply (rule isFailureOf_subset_index)
 apply (simp)
 apply (simp)
done

(*-----------------------------------*
 |     How to check BusyNetworkF     |
 *-----------------------------------*)

lemma check_BusyNetwork:
   "[| ALL i:I. ALL s Y. (s, Y) : fst (FXf i) --> Y ~= Ev ` (snd (FXf i)) |]
    ==> BusyNetwork (I,FXf)"
apply (simp add: BusyNetwork_def)
apply (intro allI ballI)
apply (rename_tac s Yf)
apply (drule_tac x="i" in bspec, simp)

apply (simp add: isDeadlockStateOf_def)
apply (simp add: disj_not1)
apply (intro impI)
apply (simp add: isStateOf_def)
apply (drule_tac x="s rest-tr (snd (FXf i))" in spec)
apply (drule_tac x="Yf i" in spec)
apply (simp)
apply (simp add: ALP_def)
done

(*********************************************************
                     in index I
 *********************************************************)

lemma in_index_I1:
  "(I, FXf) >> i --[sigma]--> j ==> i : I & j : I & i ~= j"
by (simp add: isRequestOf_def)

lemma in_index_I2:
  "(I, FXf) >> i ==[sigma]==> j ==> i : I & j : I & i ~= j"
by (simp add: isStrongRequestOf_def)

lemma in_index_I3:
  "(I, FXf) >> i --[sigma]-->o j ==> i : I & j : I & i ~= j"
apply (simp add: isUngrantedRequestOf_def)
apply (elim conjE)
by (simp add: in_index_I1)

lemma in_index_I4:
  "(I, FXf) >> i ==[sigma]==>o j ==> i : I & j : I & i ~= j"
apply (simp add: isUngrantedStrongRequestOf_def)
apply (elim conjE)
by (simp add: in_index_I2)

lemma in_index_I5:
  "(I, FXf) >> i --[sigma,Lambda]-->o j ==> i : I & j : I & i ~= j"
apply (simp add: isUngrantedRequestOfwrt_def)
apply (elim conjE)
by (simp add: in_index_I3)

lemmas in_index_I = in_index_I1 in_index_I2 in_index_I3 in_index_I4 in_index_I5

(*********************************************************
                       note (P.7)
 *********************************************************)

lemma isUngrantedRequestOfwrt_note1:
  "[| Lambda1 <= Lambda2 ; VF >> i --[sigma,Lambda1]-->o j |]
   ==> VF >> i --[sigma,Lambda2]-->o j"
apply (simp add: isUngrantedRequestOfwrt_def)
by (blast)

lemma isUngrantedRequestOfwrt_note2:
  "(snd (snd VF i)) Un (snd (snd VF j)) <= Lambda
   ==> (VF >> i --[sigma,Lambda]-->o j) = (VF >> i --[sigma]-->o j)"
by (auto simp add: isUngrantedRequestOfwrt_def)

(*********************************************************
                     sub request
 *********************************************************)

lemma isRequestOf_subsetI:
  "[| (I, FXf) >> i --[(t,Yf)]--> j; J <= I; i:J ; j:J ; 
      X = Union {snd (FXf i)|i. i:J} |]
   ==> (J, FXf) >> i --[(t rest-tr X,Yf)]--> j"
apply (simp add: isRequestOf_def)
apply (rule isStateOf_subsetI)
apply (simp_all)
done

lemma isStrongRequestOf_subsetI:
  "[| (I, FXf) >> i ==[(t,Yf)]==> j; J <= I; i:J ; j:J ; 
      X = Union {snd (FXf i)|i. i:J} |]
   ==> (J, FXf) >> i ==[(t rest-tr X,Yf)]==> j"
apply (simp add: isStrongRequestOf_def)
apply (rule isStateOf_subsetI)
apply (simp_all)
done

lemma isUngrantedRequestOf_subsetI:
  "[| (I, FXf) >> i --[(t,Yf)]-->o j; J <= I; i:J ; j:J ; 
      X = Union {snd (FXf i)|i. i:J} |]
   ==> (J, FXf) >> i --[(t rest-tr X,Yf)]-->o j"
apply (simp add: isUngrantedRequestOf_def)
apply (rule isRequestOf_subsetI)
apply (simp_all)
done

lemma isUngrantedStrongRequestOf_subsetI:
  "[| (I, FXf) >> i ==[(t,Yf)]==>o j; J <= I; i:J ; j:J ; 
      X = Union {snd (FXf i)|i. i:J} |]
   ==> (J, FXf) >> i ==[(t rest-tr X,Yf)]==>o j"
apply (simp add: isUngrantedStrongRequestOf_def)
apply (rule isStrongRequestOf_subsetI)
apply (simp_all)
done

lemma isUngrantedRequestOfwrt_subsetI:
  "[| (I, FXf) >> i --[(t,Yf), Lambda1]-->o j; J <= I; i:J ; j:J ; 
      Lambda1 <= Lambda2 ; X = Union {snd (FXf i)|i. i:J} |]
   ==> (J, FXf) >> i --[(t rest-tr X,Yf), Lambda2]-->o j"
apply (simp add: isUngrantedRequestOfwrt_def)
apply (rule conjI)
apply (rule isUngrantedRequestOf_subsetI)
apply (simp_all)
apply (blast)
done

(*********************************************************
                      blocked
 *********************************************************)

(*---------------------------------*
 | lemma 1 [Roscoe_Dathi_1987 P.7] |
 *---------------------------------*)

(*** only if ***)

lemma Lemma1_Roscoe_Dathi_1987_only_if:
  "[| triple_disjoint (I,FXf) ; BusyNetwork (I,FXf) ; 
      (t,Yf) isDeadlockStateOf (I,FXf) |]
   ==> ALL i:I. (I,FXf) >> i isBlockedIn (t,Yf)"
apply (intro ballI)
apply (subgoal_tac "ALL i:I. Yf i <= (Ev ` (snd (FXf i)))")
 apply (simp only: isBlockedIn_def)
  apply (rule conjI)
  apply (simp)
  apply (rule conjI)

 (* 1 *)

 (* busy --> i is deadlock-free *)
  apply (simp add: isRequestOf_def)
  apply (simp add: BusyNetwork_def)
  apply (drule_tac x="i" in bspec, simp)

  (* i is deadlock-free --> EX j *)
  apply (rule conjI)
  apply (simp add: isDeadlockStateOf_def)

  apply (simp add: isDeadlockStateOf_def)
  apply (simp add: disj_not1)
  apply (elim conjE)
  apply (drule_tac x="t rest-tr (snd (FXf i))" in spec)
  apply (drule_tac x="Yf" in spec)
  apply (simp add: isStateOf_each_element)
  apply (simp add: ALP_def)

  apply (subgoal_tac "EX a: Ev ` snd (FXf i). a ~: Yf i")
                                                  (* ... sub 1 *)
   apply (elim bexE)
   apply (subgoal_tac "a : Ev ` {a. EX i:I. a : snd (FXf i)}")
                                                  (* ... sub 2 *)
    apply (rotate_tac 4)
    apply (drule sym)
    apply (simp)
    apply (elim conjE exE)
    apply (simp)
    apply (rule_tac x="ia" in exI)
    apply (case_tac "i = ia", simp)
    apply (simp)
    apply (drule_tac x="ia" in bspec, simp)
    apply (blast)
   (* sub 2 *)
   apply (blast)
  (* sub 1 *)
  apply (blast)

(* 2 *) 
 apply (intro allI impI)
 apply (unfold isUngrantedRequestOfwrt_def)
 apply (rule conjI)

 (* 2-1 *)
  apply (simp add: isUngrantedRequestOf_def)
  apply (rule)

  apply (subgoal_tac "x : Union {Yf i |i. i : I}")
   apply (simp)
   apply (elim conjE bexE exE)
   apply (case_tac "ia = i", simp)
   apply (case_tac "ia = j", simp)
   (* ia ~= i & ia ~= j ==> contradict with triple_dijoint *)
   apply (drule_tac x="ia" in bspec, simp)
   apply (simp add: isDeadlockStateOf_def isStateOf_def)
   apply (simp add: triple_disjoint_def)
   apply (drule_tac x="i" in bspec, simp)
   apply (drule_tac x="j" in bspec, simp add: isRequestOf_def)
   apply (drule_tac x="ia" in bspec, simp)
    apply (drule mp)
    apply (simp add: isRequestOf_def)
   apply (rotate_tac -1)
   apply (erule contrapos_pp)
   apply (blast)

  apply (simp add: isDeadlockStateOf_def)
  apply (simp add: ALP_def)
  apply (simp add: image_iff)
  apply (elim conjE bexE, simp)
  apply (rule_tac x="i" in bexI)
  apply (simp)
  apply (simp)

 (* 2-2 *)
  apply (rule)
  apply (simp add: VocabularyOf_def)
  apply (subgoal_tac "x : Union {Yf i |i. i : I}")

   apply (simp)
   apply (elim conjE bexE exE)
   apply (simp add: image_iff)
   apply (elim disjE conjE bexE)

    apply (case_tac "i = ia", simp)
    apply (drule_tac x="ia" in bspec, simp)
    apply (simp add: isDeadlockStateOf_def isStateOf_def)
    apply (rule_tac x="snd (FXf i) Int snd (FXf ia)" in exI)
    apply (rule conjI)
     apply (rule_tac x="i" in bexI)
     apply (rule_tac x="ia" in bexI)
     apply (simp)
     apply (simp)
     apply (simp)
     apply (blast)

    apply (case_tac "j = ia", simp)
    apply (drule_tac x="ia" in bspec, simp)
    apply (simp add: isDeadlockStateOf_def isStateOf_def)
    apply (rule_tac x="snd (FXf j) Int snd (FXf ia)" in exI)
    apply (rule conjI)
     apply (rule_tac x="j" in bexI)
     apply (rule_tac x="ia" in bexI)
     apply (simp)
     apply (simp)
     apply (simp add: isRequestOf_def)
     apply (blast)

  apply (simp add: isDeadlockStateOf_def)
  apply (simp add: ALP_def)
  apply (simp add: image_iff)
  apply (elim disjE conjE bexE)

   apply (rule_tac x="xa" in exI)
   apply (simp)
   apply (fast)

   apply (rule_tac x="xa" in exI)
   apply (simp)
   apply (rule_tac x="j" in bexI)
   apply (simp)
   apply (simp add: isRequestOf_def)

apply (simp add: isDeadlockStateOf_def)
apply (simp add: isStateOf_def)
done

(*** if ***)

lemma Lemma1_Roscoe_Dathi_1987_if:
  "[| triple_disjoint (I,FXf) ; BusyNetwork (I,FXf) ; 
      (t,Yf) isStateOf (I,FXf) ;
      ALL i:I. (I,FXf) >> i isBlockedIn (t,Yf) |]
   ==> (t,Yf) isDeadlockStateOf (I,FXf)"
apply (simp add: isDeadlockStateOf_def)
apply (simp add: ALP_def)
apply (rule)

 (* <= *)
 apply (rule)
 apply (simp)
 apply (elim exE conjE)
 apply (simp)
 apply (drule_tac x="i" in bspec, simp)
 apply (simp add: isStateOf_def)
 apply (elim conjE)
 apply (drule_tac x="i" in bspec, simp)
 apply (simp add: ALP_def)
 apply (force)

 (* => *)
 apply (rule)
 apply (simp)
 apply (simp only: isBlockedIn_def)
 apply (simp add: image_iff)
 apply (elim conjE exE bexE)
 apply (simp)

 apply (case_tac "Ev xa : Yf i")
  apply (rule_tac x="Yf i" in exI)
  apply (fast)

 (* Ev xa ~: Yf i *)
  apply (subgoal_tac "xa : VocabularyOf (I,FXf)")
   apply (simp add: VocabularyOf_def)
   apply (elim conjE exE bexE)
   apply (simp)

   apply (case_tac "ia = i")
    apply (simp)
    apply (drule_tac x="i" in bspec, simp)
    apply (elim conjE exE)

    apply (drule_tac x="j" in spec)
    apply (drule mp)
    apply (simp add: isRequestOf_def)
    apply (blast)

    apply (simp add: isUngrantedRequestOfwrt_def)
    apply (simp add: isUngrantedRequestOf_def)
    apply (rule_tac x="Yf j" in exI)
    apply (fast)

   apply (case_tac "j = i")
    apply (simp)
    apply (drule_tac x="i" in bspec, simp)
    apply (elim conjE exE)
     apply (drule_tac x="ia" in spec)
     apply (drule mp)
     apply (simp add: isRequestOf_def)
     apply (blast)

     apply (simp add: isUngrantedRequestOfwrt_def)
     apply (simp add: isUngrantedRequestOf_def)
     apply (rule_tac x="Yf ia" in exI)
     apply (fast)

   (* ia ~= i; j ~= i; ia ~= j, but xa : snd (PXf i), ... *)
   apply (simp add: triple_disjoint_def)
   apply (drule_tac x="i" in bspec, simp)
   apply (rotate_tac -1)
   apply (drule_tac x="ia" in bspec, simp)
   apply (rotate_tac -1)
   apply (drule_tac x="j" in bspec, simp)
   apply (fast)

  (* xa : VocabularyOf VF *)
   apply (drule_tac x="i" in bspec, simp)
   apply (elim exE conjE)
   apply (drule_tac x="xb" in spec)
   apply (simp add: isUngrantedRequestOfwrt_def)
   apply (fast)
done

lemma Lemma1_Roscoe_Dathi_1987:
  "[| triple_disjoint (I,FXf) ; BusyNetwork (I,FXf) ; 
      (t,Yf) isStateOf (I,FXf) |]
   ==> (t,Yf) isDeadlockStateOf (I,FXf)
       = (ALL i:I. (I,FXf) >> i isBlockedIn (t,Yf))"
apply (rule)
apply (simp add: Lemma1_Roscoe_Dathi_1987_only_if)
apply (simp add: Lemma1_Roscoe_Dathi_1987_if)
done

(****************** to add it again ******************)

declare disj_not1   [simp]
(*
declare Union_image_eq [simp]
declare Inter_image_eq [simp]
*)
(*
declare Sup_image_eq [simp]
declare Inf_image_eq [simp]
*)
end
