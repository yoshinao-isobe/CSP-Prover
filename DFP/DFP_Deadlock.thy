           (*-------------------------------------------*
            |                DFP package                |
            |                   June 2005               |
            |               December 2005  (modified)   |
            |                                           |
            |   DFP on CSP-Prover ver.3.0               |
            |              September 2006  (modified)   |
            |                  April 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory DFP_Deadlock
imports DFP_Network
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
  DeadlockFree :: "'a event set => ('p,'a) proc => bool" 
                                           ("(0[_]-DeadlockFree _)" [0,55] 55)
  where
  DeadlockFree_def : 
    "[X]-DeadlockFree P == (ALL s. (Tick ~: sett(s)) --> (s,X) ~:f failures P MF)"

  (* R is deadlock free with respect to X, thus
     R can always perform an event in X at least *)

definition     
  DeadlockFreeNetwork :: "('i,'p,'a) Network => bool" 
  where
  DeadlockFreeNetwork_def : 
    "DeadlockFreeNetwork V == 
     [Ev ` (ALP V)]-DeadlockFree PAR V"


(*** UNIV deadlockfree ***)

syntax
  "@isDeadlockFree"  :: "('p,'a) proc => bool" 
                         ("_ isDeadlockFree" [1000] 1000)

translations
  "P isDeadlockFree"  == "[(CONST UNIV)]-DeadlockFree P"

definition
  isDeadlockStateOf :: 
   "('i,'a) net_state => ('i,'a) NetworkF => bool"
                           ("(0_ isDeadlockStateOf _)" [55,55] 55)
  where
  isDeadlockStateOf_def : 
   "sigma isDeadlockStateOf VF == 
                sigma isStateOf VF & 
                Union {((snd sigma) i) |i. i : fst VF}
                = Ev ` (ALP VF)"

(*********************************************************
           isDeadlockStateOf subset alpha
 *********************************************************)

lemma isDeadlockStateOf_subset_alpha1:
   "[| (I, FXf) isFailureOf (I, PXf) ; 
       (t, Yf) isDeadlockStateOf (I, FXf) ;
       i : I ; e : Yf i|]
    ==> e : (Ev ` (snd (PXf i)))"
apply (simp add: isDeadlockStateOf_def)
apply (auto simp add: isStateOf_subset_alpha)
done

lemma isDeadlockStateOf_subset_alpha2:
   "[| (I, FXf) isFailureOf (I, PXf) ; 
       (t, Yf) isDeadlockStateOf (I, FXf) ;
       i : I ; e : Yf i|]
    ==> e : (Ev ` (snd (FXf i)))"
apply (simp add: isDeadlockStateOf_def)
apply (auto simp add: isStateOf_subset_alpha)
done

lemmas isDeadlockStateOf_subset_alpha = isDeadlockStateOf_subset_alpha1
                                        isDeadlockStateOf_subset_alpha2

(*********************************************************
             Deadlock and Deadlock freedom
 *********************************************************)

(*** Existency ***)

lemma DeadlockState_notDeadlockFree_only_if_lmEX_lm:
  "[|  ALL s Y.
                 (s, Y) : fst (FXf i) -->
                 (s, Y) :f failures (fst (PXf i)) MF & Y <= Ev ` snd (FXf i);
        (s rest-tr snd (FXf i), Z) : fst (FXf i);
              Yf i Int Ev ` snd (FXf i) <= Z |]
           ==> (s rest-tr snd (FXf i),
                SOME Z.
                   (s rest-tr snd (FXf i), Z) : fst (FXf i) &
                   Yf i Int Ev ` snd (FXf i) <= Z & Z <= Ev ` snd (FXf i))
               : fst (FXf i) &
               Yf i Int Ev ` snd (FXf i)
               <= (SOME Z.
                      (s rest-tr snd (FXf i), Z) : fst (FXf i) &
                      Yf i Int Ev ` snd (FXf i) <= Z & Z <= Ev ` snd (FXf i)) &
               (SOME Z.
                   (s rest-tr snd (FXf i), Z) : fst (FXf i) &
                   Yf i Int Ev ` snd (FXf i) <= Z & Z <= Ev ` snd (FXf i))
               <= Ev ` snd (FXf i)"
apply (rule someI2[of
"(%Z. (s rest-tr snd (FXf i), Z) : fst (FXf i) &
      Yf i Int Ev ` snd (FXf i) <= Z & Z <= Ev ` snd (FXf i))" Z])
apply (rule conjI)
apply (simp)
apply (simp)
apply (simp)
done

lemma DeadlockState_notDeadlockFree_only_if_lmEX:
   "[| (I, FXf) isFailureOf (I, PXf) ;
       ALL i:I. (s rest-tr (snd (PXf i)), Yf i)
                :f failures (fst (PXf i)) MF |]
    ==>
    EX Zf. ALL i:I. (s rest-tr (snd (FXf i)), Zf i) : fst (FXf i) &
                    Yf i Int Ev ` snd (FXf i) <= Zf i &
                    Zf i <= Ev ` snd (FXf i)"
 apply (rule_tac x=
   "(%i. (SOME Z. (s rest-tr (snd (FXf i)), Z) : fst (FXf i) &
                    Yf i Int Ev ` snd (FXf i) <= Z &
                    Z <= Ev ` snd (FXf i)))" in exI)
apply (intro ballI impI)
apply (simp add: isFailureOf_def)
apply (drule_tac x="i" in bspec, simp)
apply (drule_tac x="i" in bspec, simp)
apply (simp add: subseteqEX_restRefusal_iff)
apply (elim conjE exE)
apply (rotate_tac -2)

apply (drule_tac x="s rest-tr snd (FXf i)" in spec)
apply (drule_tac x="Yf i" in spec)
apply (simp)
apply (elim conjE exE)
apply (rule DeadlockState_notDeadlockFree_only_if_lmEX_lm)
apply (simp_all)
apply (force)
done

(* only if part *)
       
lemma DeadlockState_notDeadlockFree_only_if:
  "[| I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) ;
      ~ DeadlockFreeNetwork (I,PXf) |]
   ==> (EX sigma. (sigma isDeadlockStateOf (I,FXf)))"
apply (simp add: DeadlockFreeNetwork_def)
apply (simp add: DeadlockFree_def)
apply (simp add: isDeadlockStateOf_def)
apply (subgoal_tac "Union (snd ` PXf ` I) = {a. EX i:I. a : snd (FXf i)}")
                                               (* ... sub 1 *)

 apply (elim conjE exE)
 apply (simp add: PAR_def)
 apply (simp add: in_failures_par)
 apply (elim conjE exE)

 apply (subgoal_tac 
   "EX Zf. ALL i:I. (s rest-tr (snd (FXf i)), Zf i) :  fst (FXf i) & 
           ((Yf i) Int (Ev ` snd (FXf i))) <= Zf i &
           Zf i <= (Ev ` snd (FXf i))")
                                               (* ... sub 2 *)
  apply (elim conjE exE)

 apply (rule_tac x="s" in exI)
 apply (rule_tac x="Zf" in exI)
 apply (rule conjI)

  apply (simp add: isStateOf_def)
  apply (simp add: ALP_def)
  apply (simp add: subset_insert)

  (* set *)
  apply (simp add: ALP_def)
  apply (simp add: isFailureOf_def)
  apply (simp add: Int_insert_eq)
  apply (rule)
   (* <= *)
   apply (rotate_tac -3)
   apply (drule sym)
   apply (simp)
   apply (rule)
   apply (simp)
   apply (elim conjE exE)
   apply (simp)
   apply (rotate_tac 1)
   apply (drule_tac x="i" in bspec, simp)
   apply (elim conjE)

   apply (rule rev_subsetD)
   apply (simp)
   apply (simp)
   apply (rule order_trans)
   apply (simp)

   apply (rule)
   apply (simp add: image_iff)
   apply (elim conjE bexE)
   apply (simp)
   apply (rule_tac x="i" in bexI)
   apply (simp)
   apply (simp)

   (* => *)
   apply (rule)
   apply (simp)
   apply (elim conjE bexE exE)
   apply (simp)
   apply (rule_tac x="Zf i" in exI)
   apply (rule conjI)
   apply (fast)

   apply (elim conjE disjE)
    apply (drule_tac x="i" in bspec, simp)
    apply (simp)
    apply (subgoal_tac 
      "Tick : Union {(Yf i Int insert Tick (Ev ` snd (PXf i))) |i. i : I}")
     apply (rotate_tac 5)
     apply (drule sym)
     apply (simp add: image_iff)
    apply (simp)
    apply (rule_tac x="Yf i Int insert Tick (Ev ` snd (PXf i))" in exI, simp)
    apply (rule_tac x="i" in exI, simp)

    apply (rotate_tac -5)
    apply (drule_tac x="i" in bspec, simp)
    apply (elim conjE disjE)
    apply (rule subsetD)
    apply (simp)
    apply (fast)

 (* sub 2 *)
 apply (simp add: DeadlockState_notDeadlockFree_only_if_lmEX)

(* sub 1 *)
apply (simp add: isFailureOf_def)
apply (auto)
done

(*** if part ***)

lemma DeadlockState_notDeadlockFree_if:
  "[| I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) ;
      EX sigma. (sigma isDeadlockStateOf (I,FXf)) |]
   ==> ~ DeadlockFreeNetwork (I,PXf)"
apply (simp add: DeadlockFreeNetwork_def)
apply (simp add: DeadlockFree_def)
apply (simp add: isDeadlockStateOf_def)

apply (elim conjE exE)
apply (simp add: PAR_def)

apply (rule_tac x="a" in exI)
apply (simp add: in_failures_par)
apply (simp add: isStateOf_def ALP_def)

apply (elim conjE exE)
apply (rule conjI)
apply (fast)
apply (rule conjI)

apply (rule order_trans)
apply (simp)
apply (simp add: isFailureOf_def)
apply (fast)

apply (rule_tac x="b" in exI)
apply (rename_tac s Ys)
apply (drule sym)
apply (simp)
apply (subgoal_tac "Union (snd ` PXf ` I) = {a. EX i:I. a : snd (PXf i)}")
apply (simp add: Int_insert_eq)
apply (rule conjI)
 apply (rule)

 (* <= *)
  apply (rule)
   apply (simp add: image_iff)
   apply (elim conjE exE bexE)
   apply (simp)
   apply (subgoal_tac "x : Ev ` {a. EX i:I. a : snd (FXf i)}")

    apply (simp)
    apply (elim conjE exE)
    apply (rule_tac x="Ys ia Int insert Tick (Ev ` snd (PXf ia))" in exI)
    apply (rule conjI)
    apply (fast)

    apply (simp)
    apply (drule_tac x="ia" in bspec, simp)
    apply (simp add: isFailureOf_same_alpha)
    apply (blast)

   apply (simp (no_asm) add: image_iff)
   apply (rule_tac x="xa" in exI)
   apply (simp add: isFailureOf_def)
   apply (force)

 (* => *)
  apply (rule)
   apply (simp)
   apply (elim conjE exE)
   apply (simp add: image_iff)
   apply (elim disjE conjE exE)
    apply (drule_tac x="i" in bspec, simp)
    apply (force)

    apply (elim conjE bexE)
    apply (rule_tac x="xb" in exI, simp)
    apply (rule_tac x="i" in bexI)
    apply (simp)
    apply (simp)

apply (intro ballI)
apply (simp add: isFailureOf_def)
apply (simp add: subseteqEX_restRefusal_iff)

apply (auto)
done

(*** iff ***)

lemma DeadlockState_notDeadlockFree:
  "[| I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) |]
   ==> (~ DeadlockFreeNetwork (I,PXf)) = 
       (EX sigma. (sigma isDeadlockStateOf (I,FXf)))"
apply (rule)
apply (rule DeadlockState_notDeadlockFree_only_if, simp_all)
apply (simp add: DeadlockState_notDeadlockFree_if)
done

(*** DeadlockFree ***)

lemma DeadlockFree_notDeadlockState:
  "[| I ~= {} ; finite I ; (I,FXf) isFailureOf (I,PXf) |]
   ==> DeadlockFreeNetwork (I,PXf) = 
       (ALL sigma. ~(sigma isDeadlockStateOf (I,FXf)))"
apply (rule iffI)
apply (rotate_tac -1)
apply (erule contrapos_pp)
apply (simp add: DeadlockState_notDeadlockFree)
apply (rotate_tac -1)
apply (erule contrapos_pp)
apply (simp add: DeadlockState_notDeadlockFree)
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
