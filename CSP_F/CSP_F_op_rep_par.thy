           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                    May 2005               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_op_rep_par
imports CSP_F_op_alpha_par CSP_T.CSP_T_op_rep_par
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
(*  because they unexpectly rewrite (notick | t = <>)                 *)
(*                                                                     *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*============================================================*
 |                                                            |
 |            replicated alphabetized parallel                |
 |                                                            |
 *============================================================*)

(*** Inductive_parallel ***)

lemma in_failures_Inductive_parallel_lm1: 
       "Y Int insert Tick (Ev ` snd a) Un
        Union {Y Int insert Tick (Ev ` X) |X Y. EX P. ((P, X), Y) : set PXYs} =
          Union {Ya Int insert Tick (Ev ` X) |X Ya.
                 EX P. P = fst a & X = snd a & Ya = Y | ((P, X), Ya) : set PXYs}"
by (auto)

lemma in_failures_Inductive_parallel_lm2: 
  "((P, X), Y) : set s ==> X <= Union (snd ` fst ` set s)"
  apply (auto)
(* not necessary for Isabelle 2017
apply (rule_tac x="((P, X), Y)" in bexI)
by (simp_all)
*)
  done

lemma in_failures_Inductive_parallel_lm3:
   "Union {Y Int insert Tick (Ev ` X) |X Y. EX P. ((P, X), Y) : set zs} <=
    insert Tick (Ev ` Union (snd ` fst ` set zs))"
apply (rule)
apply (simp)
apply (elim conjE exE)
apply (simp)
apply (elim conjE disjE)
apply (simp)
apply (rule disjI2)
apply (auto)
apply (simp add: image_iff)
apply (rule_tac x="((P, X), Y)" in bexI)
apply (auto)
done

lemma in_failures_Inductive_parallel_lm4:
   "Union {Y Int insert Tick (Ev ` X) |X Y. EX P. ((P, X), Y) : set zs} Int
    insert Tick (Ev ` Union (snd ` fst ` set zs))
    = Union {Y Int insert Tick (Ev ` X) |X Y. EX P. ((P, X), Y) : set zs}"
  apply (rule Int_absorb2)
(* for Isabelle 2017 *)
apply (simp add: in_failures_Inductive_parallel_lm3[simplified])
done

(* main *)

lemma in_failures_Inductive_parallel_lm:
 "PXs ~= [] --> (ALL f.
   (f :f failures([||] PXs) M) =
         (EX u. (sett(u) <= insert Tick (Ev ` Union (snd ` set PXs)) & 
          (EX Z. f = (u, Z) &
          (EX PXYs. map fst PXYs = PXs &
          (Z Int insert Tick (Ev ` Union (snd ` set PXs))
           = Union {(Y Int insert Tick (Ev ` X))|X Y. EX P. ((P,X),Y) : set PXYs} &
          (ALL P X Y. ((P,X),Y) : set PXYs --> ((u rest-tr X), Y) :f failures(P) M)))))))"
apply (induct_tac PXs)

(* case 0 *)
 apply (simp)

(* case 1 *)
 apply (case_tac "list = []")
 apply (simp)
 apply (intro allI)
 apply (simp add: in_failures_Alpha_parallel)
 apply (simp add: in_failures)
 apply (rule iffI)
 (* => *)
  apply (elim conjE exE)
  apply (simp)
  apply (erule disjE)

   apply (rule_tac x="[(a,Y)]" in exI)
   apply (simp)

    apply (rule conjI)
    apply (simp add: Evset_def pair_eq_decompo)
    apply (fast)
    apply (intro allI impI)
    apply (simp add: pair_eq_decompo)

   apply (case_tac "Tick ~: Z")
    apply (rule_tac x="[(a,Y)]" in exI)
    apply (simp add: Evset_def pair_eq_decompo)
(*    apply (fast) *)
   (* Tick : Z *)
    apply (rule_tac x="[(a,insert Tick Y)]" in exI)
    apply (simp)

    apply (simp add: rest_tr_Tick_sett)
    apply (elim conjE exE)
    apply (simp add: pair_eq_decompo)
    apply (rule conjI)
    apply (fast)
    apply (rule proc_T2_T3, simp)
    apply (simp)

 (* <= *)
  apply (elim conjE exE)
  apply (simp)
  apply (subgoal_tac "EX bb. PXYs=[(a,bb)]")
  apply (elim conjE exE)
  apply (subgoal_tac "aa rest-tr {} = <> | aa rest-tr {} = <Tick>")
  apply (erule disjE)

   (* <> *)
   apply (rule_tac x="bb" in exI)
   apply (rule_tac x="{}" in exI)
   apply (simp add: pair_eq_decompo)

   (* <Tick> *)
   apply (rule_tac x="bb" in exI)
   apply (rule_tac x="{}" in exI)
   apply (simp add: pair_eq_decompo)

   apply (simp add: rest_tr_empty)
   apply (force)

(* step case *)
apply (simp add: in_failures_Alpha_parallel)
apply (intro allI impI)
apply (rule iffI)

(* => *)
 apply (elim conjE exE, simp)
 apply (rule_tac x="(a,Y) # PXYs" in exI)
 apply (simp add: pair_eq_decompo)
 apply (simp add: in_failures_Inductive_parallel_lm1)

 apply (intro allI impI)
 apply (drule_tac x="P" in spec)
 apply (drule_tac x="X" in spec)
 apply (drule_tac x="Ya" in spec)
 apply (simp)
 apply (subgoal_tac "X <= Union (snd ` set list)")
 apply (simp add: rest_tr_of_rest_tr_subset)

 apply (rotate_tac -4)
   apply (drule sym)
(* for Isabelle 2017 *)
 apply (simp add: in_failures_Inductive_parallel_lm2[simplified])

(* <= *)
 apply (simp)
 apply (elim conjE exE)

 apply (subgoal_tac "EX bb zs. PXYs = (a, bb) # zs & map fst zs = list")
 apply (elim conjE exE)
 apply (rule_tac x="bb" in exI)
 apply (rule_tac x=
    "Union {Y Int insert Tick (Ev ` X) |X Y. EX P. ((P, X), Y) : set zs}" in exI)
 apply (simp)
 apply (rule conjI)
 apply (simp add: pair_eq_decompo)
 apply (rotate_tac -1)
 apply (drule sym)
 apply (simp)
 (* Isabelle 2017 *)
 apply (simp add: in_failures_Inductive_parallel_lm4[simplified])
 apply (simp add: in_failures_Inductive_parallel_lm1[simplified])

 apply (rule_tac x="zs" in exI)
 apply (rotate_tac -1)
 apply (drule sym)
 apply (simp add: in_failures_Inductive_parallel_lm4[simplified])

 apply (intro allI impI)
 apply (subgoal_tac "X <= Union (snd ` set list)")
 apply (simp add: rest_tr_of_rest_tr_subset)
 apply (simp add: in_failures_Inductive_parallel_lm2)
apply (auto)
done

(*** remove ALL ***)

lemma in_failures_Inductive_parallel:
 "PXs ~= [] ==> 
   (f :f failures([||] PXs) M) =
         (EX u. (sett(u) <= insert Tick (Ev ` Union (snd ` set PXs)) & 
          (EX Z. f = (u, Z) &
          (EX PXYs. map fst PXYs = PXs &
          (Z Int insert Tick (Ev ` Union (snd ` set PXs))
           = Union {(Y Int insert Tick (Ev ` X))|X Y. EX P. ((P,X),Y) : set PXYs} &
          (ALL P X Y. ((P,X),Y) : set PXYs --> ((u rest-tr X), Y) :f failures(P) M))))))"
by (simp add: in_failures_Inductive_parallel_lm)

(*** Semantics for replicated alphabetized parallel on F ***)

lemma failures_Inductive_parallel:
  "PXs ~= []
   ==> failures([||] PXs) M =
      {f. (EX u. (sett(u) <= insert Tick (Ev ` Union (snd ` set PXs)) & 
          (EX Z. f = (u, Z) &
          (EX PXYs. map fst PXYs = PXs &
          (Z Int insert Tick (Ev ` Union (snd ` set PXs))
           = Union {(Y Int insert Tick (Ev ` X))|X Y. EX P. ((P,X),Y) : set PXYs} &
          (ALL P X Y. ((P,X),Y) : set PXYs --> ((u rest-tr X), Y) :f failures(P) M))))))}f"
apply (simp add: in_failures_Inductive_parallel[THEN sym])
done

(************************************
 |              traces              |
 ************************************)

lemma sett_in_failures_Inductive_parallel:
  "[| PXs ~= [] ; (t,X) :f failures([||] PXs) M |] 
   ==> sett t <= insert Tick (Ev ` Union (snd ` set PXs))"
by (simp add: in_failures_Inductive_parallel)

(*---------------------------------------------------------*
 |        another expression of Inductive_parallel_eval          |
 *---------------------------------------------------------*)

lemma in_failures_Inductive_parallel_nth:
 "PXs ~= [] ==> 
   (f :f failures([||] PXs) M) =
         (EX u. (sett(u) <= insert Tick (Ev ` Union (snd ` set PXs)) & 
          (EX Z. f = (u, Z) &
          (EX Ys. length PXs = length Ys &
          (Z Int insert Tick (Ev ` Union (snd ` set PXs))
           = Union {((Ys!i) Int insert Tick (Ev ` (snd (PXs!i))))|i. i < length PXs} &
          (ALL i. i < length PXs --> ((u rest-tr (snd (PXs!i))), Ys!i) :f 
            failures(fst (PXs!i)) M))))))"
apply (simp add: in_failures_Inductive_parallel)
apply (simp add: set_nth)
apply (rule iffI)

(* => *)
 apply (elim conjE exE)
 apply (simp)
 apply (rule_tac x="map snd PXYs" in exI)
 apply (simp)
 apply (rotate_tac 3)
 apply (drule sym)
 apply (simp)
 apply (rule conjI)
 apply (simp add: pair_eq_decompo)

 apply (rule equalityI)
 (* <= *)
  apply (rule)
  apply (simp)
  apply (elim conjE exE)
  apply (simp)
  apply (elim conjE disjE)
   apply (simp)
   apply (rule_tac x="map snd PXYs ! i Int
                      insert Tick (Ev ` snd (map fst PXYs ! i))" in exI)
   apply (simp)
   apply (rule_tac x="i" in exI)
   apply (simp)

   apply (rule_tac x="map snd PXYs ! i Int
                      insert Tick (Ev ` snd (map fst PXYs ! i))" in exI)
   apply (simp)
   apply (rule_tac x="i" in exI)
   apply (simp)

 (* => *)
  apply (rule)
  apply (simp)
  apply (elim conjE exE)
  apply (simp)
  apply (elim conjE disjE)
   apply (simp)
   apply (rule_tac x=
     "(snd (PXYs ! i)) Int insert Tick (Ev ` snd (fst (PXYs ! i)))" in exI)
   apply (simp)
   apply (rule_tac x="snd (fst (PXYs ! i))" in exI)
   apply (rule_tac x="snd (PXYs ! i)" in exI)
   apply (simp)
   apply (rule_tac x="i" in exI)
   apply (simp)

   apply (rule_tac x=
     "(snd (PXYs ! i)) Int insert Tick (Ev ` snd (fst (PXYs ! i)))" in exI)
   apply (simp)
   apply (rule_tac x="snd (fst (PXYs ! i))" in exI)
   apply (rule_tac x="snd (PXYs ! i)" in exI)
   apply (simp)
   apply (rule_tac x="i" in exI)
   apply (simp)

  apply (intro allI impI)
  apply (drule_tac x="fst (fst (PXYs ! i))" in spec)
  apply (drule_tac x="snd (fst (PXYs ! i))" in spec)
  apply (drule_tac x="snd (PXYs ! i)" in spec)
  apply (simp)
  apply (fast)

 (* => *)
 apply (elim conjE exE)
 apply (simp)
 apply (rule_tac x="zip PXs Ys" in exI)
 apply (simp add: map_fst_zip_eq)

 apply (rule conjI)
 apply (simp add: pair_eq_decompo)

 apply (rule equalityI)
 (* <= *)
  apply (rule)
  apply (simp)
  apply (elim conjE exE)
  apply (simp)
  apply (elim conjE disjE)
   apply (simp)
   apply (rule_tac x="Ys ! i Int insert Tick (Ev ` snd (PXs ! i))" in exI)
   apply (simp)
   apply (rule_tac x="snd (PXs ! i)" in exI)
   apply (rule_tac x="Ys ! i" in exI)
   apply (simp)
   apply (rule_tac x="i" in exI)
   apply (simp)

   apply (rule_tac x="Ys ! i Int insert Tick (Ev ` snd (PXs ! i))" in exI)
   apply (simp)
   apply (rule_tac x="snd (PXs ! i)" in exI)
   apply (rule_tac x="Ys ! i" in exI)
   apply (simp)
   apply (rule_tac x="i" in exI)
   apply (simp)

 (* => *)
  apply (rule)
  apply (simp)
  apply (elim conjE exE)
  apply (simp)
  apply (elim conjE disjE)
   apply (simp)
   apply (rule_tac x="Ys ! i Int insert Tick (Ev ` snd (PXs ! i))" in exI)
   apply (simp)
   apply (rule_tac x="i" in exI)
   apply (simp)

   apply (rule_tac x="Ys ! i Int insert Tick (Ev ` snd (PXs ! i))" in exI)
   apply (simp)
   apply (rule_tac x="i" in exI)
   apply (simp)

  apply (intro allI impI)
  apply (elim conjE exE)
  apply (drule_tac x="i" in spec)
  apply (simp add: pair_eq_decompo)
done

(*============================================================*
 |                                                            |
 |              indexed alphabetized parallel                 |
 |                                                            |
 *============================================================*)

(*** failures Inductive_parallel ***)

lemma in_failures_Rep_parallel_lm1:
  "[| Is isListOf I ; length Ys = length Is |] ==>
    Union {(Ys ! i Int insert Tick (Ev ` snd (map PXf Is ! i))) |i. i < length Ys} =
    Union {(Ys ! (THE n. Is ! n = i & n < length Is) Int
            insert Tick (Ev ` snd (PXf i))) | i. i : I}"
apply (rule)

 (* <= *)
 apply (rule)
 apply (simp)
 apply (elim conjE exE)
 apply (rule_tac x=
   "Ys ! (THE n. Is ! n = (Is ! i) & n < length Is) Int
    insert Tick (Ev ` snd (PXf (Is ! i)))" in exI)
 apply (simp add: isListOf_THE_nth)
 apply (rule_tac x="(Is ! i)" in exI)
 apply (simp add: isListOf_THE_nth)
 apply (simp add: isListOf_nth_in_index)

 (* => *)
 apply (rule)
 apply (simp)
 apply (elim conjE exE)
 apply (simp)
 apply (erule isListOf_index_to_nthE)
 apply (drule_tac x="i" in bspec, simp)
 apply (elim conjE exE, simp)
 apply (simp add: isListOf_THE_nth)
 apply (rule_tac x=
   "Ys ! n Int insert Tick (Ev ` snd (PXf (Is ! n)))" in exI)
 apply (simp)
 apply (rule_tac x="n" in exI)
 apply (simp)
done

lemma in_failures_Rep_parallel_lm2:
  "Is isListOf I ==>
   Union {(Yf i Int insert Tick (Ev ` snd (PXf i))) |i. i : I} =
   Union {(map Yf Is ! i Int insert Tick (Ev ` snd (map PXf Is ! i))) |i. i < length Is}"
apply (rule)

 (* <= *)
 apply (rule)
 apply (simp)
 apply (elim conjE exE)
 apply (erule isListOf_index_to_nthE)
 apply (drule_tac x="i" in bspec, simp)
 apply (elim conjE exE, simp)
 apply (rule_tac x=
   "map Yf Is ! n Int insert Tick (Ev ` snd (map PXf Is ! n))" in exI)
 apply (simp)
 apply (rule_tac x="n" in exI)
 apply (simp)

 (* => *)
 apply (rule)
 apply (simp)
 apply (elim conjE exE)
 apply (rule_tac x= "Yf (Is!i) Int insert Tick (Ev ` snd (PXf (Is!i)))" in exI)
 apply (simp)
 apply (rule_tac x="(Is!i)" in exI)
 apply (simp add: isListOf_nth_in_index)
done

lemma in_failures_Rep_parallel:
  "[| I ~= {} ; finite I |]
   ==> (f :f failures ([||]:I PXf) M) =
         (EX u. (sett(u) <= insert Tick (Ev ` Union (snd ` PXf ` I)) & 
          (EX Z. f = (u, Z) &
          (EX Yf. 
          (Z Int insert Tick (Ev ` Union (snd ` PXf ` I))
           = Union {((Yf i) Int insert Tick (Ev ` (snd (PXf i))))|i. i : I} &
          (ALL i:I. ((u rest-tr (snd (PXf i))), Yf i) :f failures(fst (PXf i)) M))))))"
apply (simp add: Rep_parallel_def)
apply (subgoal_tac "EX Is. Is isListOf I")
apply (elim conjE exE)
apply (subgoal_tac "(map PXf (SOME Is. Is isListOf I)) ~= []")
apply (simp add: in_failures_Inductive_parallel_nth)
apply (rule someI2)
 apply (simp)
 apply (rule iffI)

  (* => *)
  apply (elim conjE exE)
  apply (rename_tac Is' Is u Z Ys)
  apply (rule_tac x="u" in exI)
  apply (simp add: isListOf_set_eq)
  apply (rule_tac x= "(%i. (Ys!(THE n. (Is!n) = i & n<length Is)))" in exI)
  apply (rule conjI)
  apply (simp add: in_failures_Rep_parallel_lm1)
  apply (rule ballI)

  apply (rotate_tac 4)
  apply (erule isListOf_index_to_nthE)
  apply (drule_tac x="i" in bspec, simp)
  apply (elim conjE exE, simp)

  apply (rotate_tac 2)
  apply (drule sym)
  apply (simp add: isListOf_THE_nth)

  (* <= *)
  apply (elim conjE exE)
  apply (rename_tac Is' Is u Z Yf)
  apply (rule_tac x="u" in exI)
  apply (simp add: isListOf_set_eq)
  apply (rule_tac x= "map Yf Is" in exI)
  apply (simp)
  apply (rule conjI)
  apply (rule in_failures_Rep_parallel_lm2, simp)
  apply (intro allI impI)
  apply (drule_tac x="Is ! i" in bspec)
  apply (simp add: isListOf_nth_in_index)
  apply (simp)

 apply (rule someI2)
 apply (simp)
 apply (simp add: isListOf_nonemptyset)

apply (simp add: isListOf_EX)
done

lemmas in_failures_par = in_failures_Alpha_parallel
                         in_failures_Inductive_parallel
                         in_failures_Rep_parallel

(*** Semantics for indexed alphabetized parallel on F ***)

lemma failures_Rep_parallel:
  "[| I ~= {} ; finite I |]
   ==> failures ([||]:I PXf) M =
      {f. (EX u. (sett(u) <= insert Tick (Ev ` Union (snd ` PXf ` I)) & 
          (EX Z. f = (u, Z) &
          (EX Yf. 
          (Z Int insert Tick (Ev ` Union (snd ` PXf ` I))
           = Union {((Yf i) Int insert Tick (Ev ` (snd (PXf i))))|i. i : I} &
          (ALL i:I. ((u rest-tr (snd (PXf i))), Yf i) :f failures(fst (PXf i)) M))))))}f"
(* for Isabelle 2017 *)
  apply (simp add: in_failures_Rep_parallel[simplified, THEN sym])
done

(************************************
 |              traces              |
 ************************************)

lemma sett_in_failures_Rep_parallel:
  "[| I ~= {} ; finite I ; (t,X) :f failures([||]:I PXf) M |] 
   ==> sett t <= insert Tick (Ev ` Union (snd ` PXf ` I))"
by (simp add: in_failures_Rep_parallel)

(****************** to add it again ******************)

declare disj_not1      [simp]
(*
declare Union_image_eq [simp]
declare Inter_image_eq [simp]
*)
(*
declare Sup_image_eq [simp]
declare Inf_image_eq [simp]
*)
end
