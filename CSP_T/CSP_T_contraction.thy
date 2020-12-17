           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005  (modified)   |
            |                 August 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |               November 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2008         |
            |                   June 2008  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009-2       |
            |                October 2010  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_contraction
imports CSP_T_traces CSP.RS_prod
begin

(*****************************************************************

         1. contraction traces
         2. contraction [[ ]]Tfun

 *****************************************************************)

(*============================================*
 |                   gSKIP                    |
 *============================================*)

lemma gSKIP_to_Tick_notin_traces:
  "ALL P M. gSKIP P --> <Tick> ~:t traces (P) M"
apply (intro allI)
apply (induct_tac P)
apply (simp_all add: in_traces)
apply (intro impI conjI allI)

 apply (erule noTick_rmTickE)
 apply (simp)
 apply (auto)
 apply (erule noTick_rmTickE)
 apply (simp)
 apply (erule noTick_rmTickE)
 apply (simp)
done

(*--------------------------------*
 |        STOP,SKIP,DIV           |
 *--------------------------------*)

(*** Constant_contraction ***)

lemma map_alpha_Constant: "0 <= alpha ==> map_alpha (%M. C) alpha"
apply (simp add: map_alpha_def)
(* for Isabelle 2013
apply (simp add: real_mult_order_eq)
*)
done

(*** non_expanding_Constant ***)

lemma non_expanding_Constant: "non_expanding (%M. C)"
by (simp add: non_expanding_def map_alpha_Constant)

(*** Constant_contraction_alpha ***)

lemma contraction_alpha_Constant:
   "[| 0 <= alpha ; 1 > alpha |] ==> contraction_alpha (%M. C) alpha"
by (simp add: contraction_alpha_def map_alpha_Constant)

(*** STOP ***)

lemma map_alpha_traces_STOP: 
  "0 <= alpha ==> map_alpha (traces (STOP)) alpha"
by (simp add: traces_iff map_alpha_Constant)

lemma non_expanding_traces_STOP: 
  "non_expanding (traces (STOP))"
by (simp add: non_expanding_def map_alpha_traces_STOP)

lemma contraction_alpha_traces_STOP: 
  "[| 0 <= alpha ; 1 > alpha |] ==> contraction_alpha (traces (STOP)) alpha"
by (simp add: traces_iff contraction_alpha_Constant)

(*** SKIP ***)

lemma map_alpha_traces_SKIP: 
  "0 <= alpha ==> map_alpha (traces (SKIP)) alpha"
by (simp add: traces_iff map_alpha_Constant)

lemma non_expanding_traces_SKIP: 
  "non_expanding (traces (SKIP))"
by (simp add: non_expanding_def map_alpha_traces_SKIP)

lemma contraction_alpha_traces_SKIP: 
  "[| 0 <= alpha ; 1 > alpha |] ==> contraction_alpha (traces (SKIP)) alpha"
by (simp add: traces_iff contraction_alpha_Constant)

(*** DIV ***)

lemma map_alpha_traces_DIV: 
  "0 <= alpha ==> map_alpha (traces (DIV)) alpha"
by (simp add: traces_iff map_alpha_Constant)

lemma non_expanding_traces_DIV: 
  "non_expanding (traces (DIV))"
by (simp add: non_expanding_def map_alpha_traces_DIV)

lemma contraction_alpha_traces_DIV: 
  "[| 0 <= alpha ; 1 > alpha |] ==> contraction_alpha (traces (DIV)) alpha"
by (simp add: traces_iff contraction_alpha_Constant)

(*--------------------------------*
 |          Act_prefix            |
 *--------------------------------*)

lemma contraction_half_traces_Act_prefix_lm: 
   "distance (traces (a -> P) M1, traces (a -> Q) M2) * 2
    = distance (traces P M1, traces Q M2)"
apply (rule sym)
apply (simp add: to_distance_rs)

apply (rule rest_Suc_dist_half[simplified])
apply (rule allI)
apply (simp add: rest_domT_eq_iff)
apply (rule iffI)

 (* => *)
 apply (rule allI)
 apply (simp add: in_traces)
 apply (rule iffI)

  (* => *)
  apply (elim conjE exE disjE, simp)
  apply (drule_tac x="sa" in spec)
  apply (simp)
  (* <= *)
  apply (elim conjE exE disjE, simp)
  apply (drule_tac x="sa" in spec)
  apply (simp)

 (* <= *)
 apply (rule allI)
 apply (drule_tac x="<Ev a> ^^^ s" in spec)
 apply (simp add: in_traces)
done

(***  contraction_half ***)

lemma contraction_half_traces_Act_prefix: 
 "non_expanding (traces P)
  ==> contraction_alpha (traces (a -> P)) (1 / 2)"
apply (simp add: contraction_alpha_def non_expanding_def map_alpha_def)
apply (intro allI)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (simp add: contraction_half_traces_Act_prefix_lm)
done

(***  contraction ***)

lemma contraction_traces_Act_prefix: 
 "non_expanding (traces P)
  ==> contraction (traces (a -> P))"
apply (simp add: contraction_def)
apply (rule_tac x="1/2" in exI)
by (simp add: contraction_half_traces_Act_prefix)

(*** non_expanding ***)

lemma non_expanding_traces_Act_prefix: 
 "non_expanding (traces P)
  ==> non_expanding (traces (a -> P))"
apply (rule contraction_non_expanding)
by (simp add: contraction_traces_Act_prefix)

(*--------------------------------*
 |        Ext_pre_choice          |
 *--------------------------------*)

(*** rest_domT (subset) ***)

lemma Ext_pre_choice_Act_prefix_rest_domT_sub:
   "[| ALL a : X.
         traces (a -> Pf a) M1 .|. n <= traces (a -> Qf a) M2 .|. n |]
    ==> traces (? a:X -> Pf a) M1 .|. n <=
        traces (? a:X -> Qf a) M2 .|. n"
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_rest_domT)
apply (simp add: in_traces)
apply (elim conjE exE disjE)
apply (simp_all)

apply (drule_tac x="a" in bspec, simp)
apply (drule_tac x="t" in spec)
apply (simp add: in_traces)
done

(*** rest_domT (equal) ***)

lemma Ext_pre_choice_Act_prefix_rest_domT:
   "[| ALL a : X.
         traces (a -> Pf a) M1 .|. n = traces (a -> Qf a) M2 .|. n |]
    ==> traces (? a:X -> Pf a) M1 .|. n =
        traces (? a:X -> Qf a) M2 .|. n"
apply (rule order_antisym)
by (simp_all add: Ext_pre_choice_Act_prefix_rest_domT_sub)

(*** distT lemma ***)

lemma Ext_pre_choice_Act_prefix_distT_nonempty:
"[| X ~= {} ; PQs = {(traces (a -> Pf a) M1, traces (a -> Qf a) M2)|a. a : X} |]
 ==> (EX PQ. PQ:PQs & 
             distance(traces (? a:X -> Pf a) M1, traces (? a:X -> Qf a) M2)
          <= distance(fst PQ, snd PQ))"
apply (simp only: to_distance_rs)
apply (rule rest_to_dist_pair)
apply (force)

apply (intro allI impI)
apply (rule Ext_pre_choice_Act_prefix_rest_domT)
apply (rule ballI)
apply (simp)
apply (drule_tac x="traces (a -> Pf a) M1" in spec)
apply (drule_tac x="traces (a -> Qf a) M2" in spec)
by (auto)

(*** contraction lemma ***)

lemma contraction_half_traces_Ext_pre_choice_lm:
  "[| X ~= {} ; ALL a. distance (traces (Pf a) M1, traces (Qf a) M2)
                    <= distance (x1, x2) |]
    ==> distance (traces (? a:X -> Pf a) M1, traces (? a:X -> Qf a) M2) * 2 
     <= distance (x1, x2)"
apply (insert Ext_pre_choice_Act_prefix_distT_nonempty
       [of X "{(traces (a -> Pf a) M1, traces (a -> Qf a) M2) |a. a : X}" Pf M1 Qf M2])
apply (simp)
apply (elim conjE exE)
apply (simp)
apply (subgoal_tac 
    "distance (traces (aa -> Pf aa) M1, traces (aa -> Qf aa) M2) * 2
   = distance (traces (Pf aa) M1, traces (Qf aa) M2)")
apply (drule_tac x="aa" in spec)
apply (force)
by (simp add: contraction_half_traces_Act_prefix_lm)

(*** contraction_half ***)

lemma contraction_half_traces_Ext_pre_choice:
 "ALL a. non_expanding (traces (Pf a))
  ==> contraction_alpha (traces (? :X -> Pf)) (1 / 2)"
apply (simp add: contraction_alpha_def non_expanding_def map_alpha_def)
apply (case_tac "X = {}")
apply (simp add: traces_iff)
by (simp add: contraction_half_traces_Ext_pre_choice_lm)

(*** Ext_pre_choice_evalT_contraction ***)

lemma contraction_traces_Ext_pre_choice:
 "ALL a. non_expanding (traces (Pf a))
  ==> contraction (traces (? :X -> Pf))"
apply (simp add: contraction_def)
apply (rule_tac x="1/2" in exI)
by (simp add: contraction_half_traces_Ext_pre_choice)

(*** Ext_pre_choice_evalT_non_expanding ***)

lemma non_expanding_traces_Ext_pre_choice:
 "ALL a. non_expanding (traces (Pf a))
  ==> non_expanding (traces (? :X -> Pf))"
apply (rule contraction_non_expanding)
by (simp add: contraction_traces_Ext_pre_choice)

(*--------------------------------*
 |          Ext_choice            |
 *--------------------------------*)

(*** rest_domT (subset) ***)

lemma Ext_choice_rest_domT_sub:
   "[| traces P1 M1 .|. n <= traces P2 M2 .|. n ;
       traces Q1 M1 .|. n <= traces Q2 M2 .|. n  |]
    ==> traces (P1 [+] Q1) M1 .|. n <= traces (P2 [+] Q2) M2 .|. n"
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_rest_domT)
apply (simp add: in_traces)
by (auto)

(*** rest_domT (equal) ***)

lemma Ext_choice_rest_domT:
   "[| traces P1 M1 .|. n = traces P2 M2 .|. n ;
       traces Q1 M1 .|. n = traces Q2 M2 .|. n  |]
    ==> traces (P1 [+] Q1) M1 .|. n = traces (P2 [+] Q2) M2 .|. n"
apply (rule order_antisym)
by (simp_all add: Ext_choice_rest_domT_sub)

(*** distT lemma ***)

lemma Ext_choice_distT:
"PQs = {(traces P1 M1, traces P2 M2), (traces Q1 M1, traces Q2 M2)}
 ==> (EX PQ. PQ:PQs & 
             distance(traces (P1 [+] Q1) M1, traces (P2 [+] Q2) M2)
          <= distance((fst PQ), (snd PQ)))"
apply (simp only: to_distance_rs)
apply (rule rest_to_dist_pair)
by (auto intro: Ext_choice_rest_domT)

(*** map_alpha T lemma ***)

lemma map_alpha_traces_Ext_choice_lm:
  "[| distance (traces P1 M1, traces P2 M2) <= alpha * distance (x1, x2) ;
      distance (traces Q1 M1, traces Q2 M2) <= alpha * distance (x1, x2) |]
    ==> distance (traces (P1 [+] Q1) M1, traces (P2 [+] Q2) M2)
     <= alpha * distance (x1, x2)"
apply (insert Ext_choice_distT)
apply (insert Ext_choice_distT
       [of "{(traces P1 M1, traces P2 M2), (traces Q1 M1, traces Q2 M2)}" 
           P1 M1 P2 M2 Q1 Q2])
by (auto)

(*** map_alpha ***)

lemma map_alpha_traces_Ext_choice:
 "[| map_alpha (traces P) alpha ; map_alpha (traces Q) alpha |]
  ==> map_alpha (traces (P [+] Q)) alpha"
apply (simp add: map_alpha_def)
apply (intro allI)
apply (erule conjE)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="y" in spec)
by (simp add: map_alpha_traces_Ext_choice_lm)

(*** non_expanding ***)

lemma non_expanding_traces_Ext_choice:
 "[| non_expanding (traces P) ; non_expanding (traces Q) |]
  ==> non_expanding (traces (P [+] Q))"
by (simp add: non_expanding_def map_alpha_traces_Ext_choice)

(*** contraction ***)

lemma contraction_alpha_traces_Ext_choice:
 "[| contraction_alpha (traces P) alpha ; 
     contraction_alpha (traces Q) alpha|]
  ==> contraction_alpha (traces (P [+] Q)) alpha"
by (simp add: contraction_alpha_def map_alpha_traces_Ext_choice)

(*--------------------------------*
 |          Int_choice            |
 *--------------------------------*)

(*** map_alpha ***)

lemma map_alpha_traces_Int_choice:
 "[| map_alpha (traces P) alpha ; map_alpha (traces Q) alpha |]
  ==> map_alpha (traces (P |~| Q)) alpha"
by (simp add: map_alpha_traces_Ext_choice traces_Int_choice_Ext_choice)

(*** non_expanding ***)

lemma non_expanding_traces_Int_choice:
 "[| non_expanding (traces P) ; non_expanding (traces Q) |]
  ==> non_expanding (traces (P |~| Q))"
by (simp add: non_expanding_traces_Ext_choice traces_Int_choice_Ext_choice)

(*** contraction ***)

lemma contraction_alpha_traces_Int_choice:
 "[| contraction_alpha (traces P) alpha ; 
     contraction_alpha (traces Q) alpha|]
  ==> contraction_alpha (traces (P |~| Q)) alpha"
by (simp add: contraction_alpha_traces_Ext_choice traces_Int_choice_Ext_choice)

(*--------------------------------*
 |        Rep_int_choice          |
 *--------------------------------*)

(*** rest_domT (subset) ***)

lemma Rep_int_choice_rest_domT_sub:
   "[| ALL c : sumset C.
         traces (Pf c) M1 .|. n <= traces (Qf c) M2 .|. n |]
    ==>  traces (!! :C .. Pf) M1 .|. n <=
         traces (!! :C .. Qf) M2 .|. n"
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_rest_domT)
apply (simp add: in_traces)
by (auto)

(*** rest_domT (equal) ***)

lemma Rep_int_choice_rest_domT:
   "[| ALL c : sumset C.
         traces (Pf c) M1 .|. n = traces (Qf c) M2 .|. n |]
    ==>  traces (!! :C .. Pf) M1 .|. n =
         traces (!! :C .. Qf) M2 .|. n"
apply (rule order_antisym)
by (simp_all add: Rep_int_choice_rest_domT_sub)

(*** distT lemma ***)

lemma Rep_int_choice_distT_nonempty:
"[| sumset C ~= {} ; 
    PQs = {(traces (Pf c) M1, traces (Qf c) M2)|c. c : sumset C} |]
 ==> (EX PQ. PQ:PQs & 
             distance(traces (!! :C .. Pf) M1, traces (!! :C .. Qf) M2)
          <= distance(fst PQ, snd PQ))"
apply (simp only: to_distance_rs)
apply (rule rest_to_dist_pair)
apply (fast)

apply (intro allI impI)
apply (rule Rep_int_choice_rest_domT)
by (auto)

(*** map_alpha T lemma ***)

lemma map_alpha_traces_Rep_int_choice_lm:
"[| sumset C ~= {} ; 
    ALL c. distance (traces (Pf c) M1, traces (Qf c) M2) 
                  <= alpha * distance (x1, x2) |]
 ==> distance(traces(!! :C .. Pf) M1, (traces(!! :C .. Qf) M2))
  <= alpha * distance(x1, x2)"
apply (insert Rep_int_choice_distT_nonempty
       [of C "{(traces (Pf c) M1, traces (Qf c) M2)|c. c : sumset C}" 
           Pf M1 Qf M2])
apply (simp)
apply (elim conjE exE, simp)
apply (drule_tac x="c" in spec)
by (force)

(*** map_alpha ***)
lemma map_alpha_traces_Rep_int_choice:
 "ALL c. map_alpha (traces (Pf c)) alpha
  ==> map_alpha (traces (!! :C .. Pf)) alpha"
apply (simp add: map_alpha_def)
apply (case_tac "sumset C = {}")
 apply (simp add: traces_iff)
(* for Isabelle 2013
apply (simp add: real_mult_order_eq)
*)
apply (simp add: map_alpha_traces_Rep_int_choice_lm)
done

(*** non_expanding ***)

lemma non_expanding_traces_Rep_int_choice:
 "ALL c. non_expanding (traces (Pf c))
  ==> non_expanding (traces (!! :C .. Pf))"
by (simp add: non_expanding_def map_alpha_traces_Rep_int_choice)

(*** Rep_int_choice_evalT_contraction_alpha ***)

lemma contraction_alpha_traces_Rep_int_choice:
 "ALL c. contraction_alpha (traces (Pf c)) alpha 
     ==> contraction_alpha (traces (!! :C .. Pf)) alpha"
by (simp add: contraction_alpha_def map_alpha_traces_Rep_int_choice)

(*--------------------------------*
 |               IF               |
 *--------------------------------*)

(*** rest_domT (subset) ***)

lemma IF_rest_domT_sub:
   "[| traces P1 M1 .|. n <= traces P2 M2 .|. n ;
       traces Q1 M1 .|. n <= traces Q2 M2 .|. n  |]
    ==> traces (IF b THEN P1 ELSE Q1) M1 .|. n <= 
        traces (IF b THEN P2 ELSE Q2) M2 .|. n"
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_rest_domT)
apply (simp add: in_traces)
done

(*** rest_domT (equal) ***)

lemma IF_rest_domT:
   "[| traces P1 M1 .|. n = traces P2 M2 .|. n ;
       traces Q1 M1 .|. n = traces Q2 M2 .|. n  |]
    ==> traces (IF b THEN P1 ELSE Q1) M1 .|. n = 
        traces (IF b THEN P2 ELSE Q2) M2 .|. n"
apply (rule order_antisym)
by (simp_all add: IF_rest_domT_sub)

(*** distT lemma ***)

lemma IF_distT:
   "PQs = {(traces P1 M1, traces P2 M2), (traces Q1 M1, traces Q2 M2)}
    ==> (EX PQ. PQ:PQs & 
             distance(traces (IF b THEN P1 ELSE Q1) M1,
                      traces (IF b THEN P2 ELSE Q2) M2)
          <= distance((fst PQ), (snd PQ)))"
apply (simp only: to_distance_rs)
apply (rule rest_to_dist_pair)
by (auto intro: IF_rest_domT)

(*** map_alpha T lemma (not used) ***)

lemma map_alpha_traces_IF_lm:
  "[| distance (traces P1 M1, traces P2 M2) <= alpha * distance (x1, x2) ;
      distance (traces Q1 M1, traces Q2 M2) <= alpha * distance (x1, x2) |]
    ==> distance(traces (IF b THEN P1 ELSE Q1) M1,
                 traces (IF b THEN P2 ELSE Q2) M2)
     <= alpha * distance (x1, x2)"
apply (insert IF_distT
       [of "{(traces P1 M1, traces P2 M2), 
             (traces Q1 M1, traces Q2 M2)}"  P1 M1 P2 M2 Q1 Q2 b])
by (auto)

(*** map_alpha ***)

lemma map_alpha_traces_IF:
 "[| map_alpha (traces P) alpha ; map_alpha (traces Q) alpha |]
  ==> map_alpha (traces (IF b THEN P ELSE Q)) alpha"
apply (simp add: map_alpha_def)
apply (intro allI)
apply (erule conjE)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="y" in spec)
apply (simp add: traces_iff)
done

(*** non_expanding ***)

lemma non_expanding_traces_IF:
 "[| non_expanding (traces P) ; non_expanding (traces Q) |]
  ==> non_expanding (traces (IF b THEN P ELSE Q))"
by (simp add: non_expanding_def map_alpha_traces_IF)

(*** contraction_alpha ***)

lemma contraction_alpha_traces_IF:
 "[| contraction_alpha (traces P) alpha ; contraction_alpha (traces Q) alpha|]
  ==> contraction_alpha (traces (IF b THEN P ELSE Q)) alpha"
by (simp add: contraction_alpha_def map_alpha_traces_IF)

(*--------------------------------*
 |           Parallel             |
 *--------------------------------*)

(*** rest_domT (subset) ***)

lemma Parallel_rest_domT_sub:
   "[| traces P1 M1 .|. n <= traces P2 M2 .|. n ;
       traces Q1 M1 .|. n <= traces Q2 M2 .|. n  |]
    ==> traces (P1 |[X]| Q1) M1 .|. n <= traces (P2 |[X]| Q2) M2 .|. n"
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_rest_domT)
apply (simp add: in_traces)
apply (elim conjE exE)
apply (rule_tac x="s" in exI)
apply (rule_tac x="ta" in exI)
apply (simp)

apply (erule par_tr_lengthtE)
by (auto)

(*** rest_domT (equal) ***)

lemma Parallel_rest_domT:
   "[| traces P1 M1 .|. n = traces P2 M2 .|. n ;
       traces Q1 M1 .|. n = traces Q2 M2 .|. n  |]
    ==> traces (P1 |[X]| Q1) M1 .|. n = traces (P2 |[X]| Q2) M2 .|. n"
apply (rule order_antisym)
by (simp_all add: Parallel_rest_domT_sub)

(*** distT lemma ***)

lemma Parallel_distT:
"PQs = {(traces P1 M1, traces P2 M2), (traces Q1 M1, traces Q2 M2)}
 ==> (EX PQ. PQ:PQs & 
             distance(traces (P1 |[X]| Q1) M1, traces (P2 |[X]| Q2) M2)
          <= distance((fst PQ), (snd PQ)))"
apply (simp only: to_distance_rs)
apply (rule rest_to_dist_pair)
by (auto intro: Parallel_rest_domT)

(*** map_alpha T lemma ***)

lemma map_alpha_traces_Parallel_lm:
  "[| distance (traces P1 M1, traces P2 M2) <= alpha * distance (x1, x2) ;
      distance (traces Q1 M1, traces Q2 M2) <= alpha * distance (x1, x2) |]
    ==> distance (traces (P1 |[X]| Q1) M1, traces (P2 |[X]| Q2) M2)
     <= alpha * distance (x1, x2)"
apply (insert Parallel_distT
       [of "{(traces P1 M1, traces P2 M2), (traces Q1 M1, traces Q2 M2)}"
           P1 M1 P2 M2 Q1 Q2 X])
by (auto)

(*** map_alpha ***)

lemma map_alpha_traces_Parallel:
 "[| map_alpha (traces P) alpha ; map_alpha (traces Q) alpha |]
  ==> map_alpha (traces (P |[X]| Q)) alpha"
apply (simp add: map_alpha_def)
apply (intro allI)
apply (erule conjE)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="y" in spec)
by (simp add: map_alpha_traces_Parallel_lm)

(*** non_expanding ***)

lemma non_expanding_traces_Parallel:
 "[| non_expanding (traces P) ; non_expanding (traces Q) |]
  ==> non_expanding (traces (P |[X]| Q))"
by (simp add: non_expanding_def map_alpha_traces_Parallel)

(*** contraction_alpha ***)

lemma contraction_alpha_traces_Parallel:
 "[| contraction_alpha (traces P) alpha ; 
     contraction_alpha (traces Q) alpha |]
  ==> contraction_alpha (traces (P |[X]| Q)) alpha"
by (simp add: contraction_alpha_def map_alpha_traces_Parallel)

(*--------------------------------*
 |            Hiding              |
 *--------------------------------*)

(* cms rules for Hiding is not necessary 
   because processes are guarded. *)

(*--------------------------------*
 |           Renaming             |
 *--------------------------------*)

(*** rest_domT (subset) ***)

lemma Renaming_rest_domT_sub:
   "traces P M1 .|. n <= traces Q M2 .|. n
    ==> traces (P [[r]]) M1 .|. n <= traces (Q [[r]]) M2 .|. n"
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_rest_domT)
apply (simp add: in_traces)
apply (elim conjE exE)
apply (rule_tac x="s" in exI)
apply (drule_tac x="s" in spec)
by (simp add: ren_tr_lengtht)

(*** rest_domT (equal) ***)

lemma Renaming_rest_domT:
   "traces P M1 .|. n = traces Q M2 .|. n
    ==> traces (P [[r]]) M1 .|. n = traces (Q [[r]]) M2 .|. n"
apply (rule order_antisym)
by (simp_all add: Renaming_rest_domT_sub)

(*** distT lemma ***)

lemma Renaming_distT:
     "distance(traces (P [[r]]) M1, traces (Q [[r]]) M2) <= 
      distance(traces P M1, traces Q M2)"
apply (simp only: to_distance_rs)
apply (rule rest_distance_subset)
by (auto intro: Renaming_rest_domT)

(*** map_alphaT lemma ***)

lemma map_alpha_traces_Renaming_lm:
  "distance(traces P M1, traces Q M2) <= alpha * distance (x1, x2)
    ==> distance(traces (P [[r]]) M1, traces (Q [[r]]) M2)
     <= alpha * distance(x1, x2)"
apply (insert Renaming_distT[of P r M1 Q M2])
by (simp)

(*** map_alpha ***)

lemma map_alpha_traces_Renaming:
 "map_alpha (traces P) alpha
  ==> map_alpha (traces (P [[r]])) alpha"
apply (simp add: map_alpha_def)
apply (intro allI)
apply (erule conjE)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
by (simp add: map_alpha_traces_Renaming_lm)

(*** non_expanding ***)

lemma non_expanding_traces_Renaming:
 "non_expanding (traces P)
  ==> non_expanding (traces (P [[r]]))"
by (simp add: non_expanding_def map_alpha_traces_Renaming)

(*** contraction_alpha ***)

lemma contraction_alpha_traces_Renaming:
 "contraction_alpha (traces P) alpha
  ==> contraction_alpha (traces (P [[r]])) alpha"
by (simp add: contraction_alpha_def map_alpha_traces_Renaming)

(*--------------------------------*
 |           Seq_compo            |
 *--------------------------------*)

(*** rest_domT (subset) ***)

lemma Seq_compo_rest_domT_sub:
   "[| traces P1 M1 .|. n <= traces P2 M2 .|. n ;
       traces Q1 M1 .|. n <= traces Q2 M2 .|. n  |]
    ==> traces (P1 ;; Q1) M1 .|. n <= traces (P2 ;; Q2) M2 .|. n"
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_rest_domT)
apply (simp add: in_traces)
apply (elim conjE exE disjE)

 (* case 1 *)
 apply (rule disjI1)
 apply (insert trace_last_noTick_or_Tick)
 apply (rotate_tac -1)
 apply (drule_tac x="s" in spec)
 apply (erule disjE)
 apply (rule_tac x="s" in exI, simp)

 apply (elim conjE exE)
 apply (rule_tac x="sa" in exI, simp)
 apply (drule_tac x="sa" in spec, simp)
 apply (drule mp)
 apply (rule memT_prefix_closed, simp_all, simp)

 (* case 2 *)
 apply (case_tac "~ noTick s", simp)
 apply (insert trace_last_nil_or_unnil)
 apply (rotate_tac -1)
 apply (drule_tac x="ta" in spec)
 apply (erule disjE)

  apply (rule disjI1)                (* ta = []t *)
  apply (rule_tac x="s" in exI, simp)
  apply (drule_tac x="s" in spec, simp)
  apply (drule mp)
  apply (rule memT_prefix_closed, simp_all, simp)

  apply (rule disjI2)                (* ta ~= []t *)
  apply (elim conjE exE, simp)

  apply (drule_tac x="s ^^^ <Tick>" in spec)
  apply (drule_tac x=" sa ^^^ <a>" in spec)
  apply (simp)
  apply (rule_tac x="s" in exI)
  apply (rule_tac x="sa ^^^ <a>" in exI)
  apply (simp)
done

(*** rest_domT (equal) ***)

lemma Seq_compo_rest_domT:
   "[| traces P1 M1 .|. n = traces P2 M2 .|. n ;
       traces Q1 M1 .|. n = traces Q2 M2 .|. n  |]
    ==> traces (P1 ;; Q1) M1 .|. n = traces (P2 ;; Q2) M2 .|. n"
apply (rule order_antisym)
by (simp_all add: Seq_compo_rest_domT_sub)

(*** distT lemma ***)

lemma Seq_compo_distT:
"PQs = {(traces P1 M1, traces P2 M2), (traces Q1 M1, traces Q2 M2)}
 ==> (EX PQ. PQ:PQs & 
             distance(traces (P1 ;; Q1) M1, traces (P2 ;; Q2) M2)
          <= distance((fst PQ), (snd PQ)))"
apply (simp only: to_distance_rs)
apply (rule rest_to_dist_pair)
by (auto intro: Seq_compo_rest_domT)

(*** map_alpha T lemma ***)

lemma map_alpha_traces_Seq_compo_lm:
  "[| distance (traces P1 M1, traces P2 M2) <= alpha * distance (x1, x2) ;
      distance (traces Q1 M1, traces Q2 M2) <= alpha * distance (x1, x2) |]
    ==> distance (traces (P1 ;; Q1) M1, traces (P2 ;; Q2) M2)
     <= alpha * distance (x1, x2)"
apply (insert Seq_compo_distT)
apply (insert Seq_compo_distT
       [of "{(traces P1 M1, traces P2 M2), (traces Q1 M1, traces Q2 M2)}" 
           P1 M1 P2 M2 Q1 Q2])
by (auto)

(*** map_alpha ***)

lemma map_alpha_traces_Seq_compo:
 "[| map_alpha (traces P) alpha ; map_alpha (traces Q) alpha |]
  ==> map_alpha (traces (P ;; Q)) alpha"
apply (simp add: map_alpha_def)
apply (intro allI)
apply (erule conjE)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="y" in spec)
by (simp add: map_alpha_traces_Seq_compo_lm)

(*** non_expanding ***)

lemma non_expanding_traces_Seq_compo:
 "[| non_expanding (traces P) ; non_expanding (traces Q) |]
  ==> non_expanding (traces (P ;; Q))"
by (simp add: non_expanding_def map_alpha_traces_Seq_compo)

(*** contraction_alpha ***)

lemma contraction_alpha_traces_Seq_compo:
 "[| contraction_alpha (traces P) alpha ; 
     contraction_alpha (traces Q) alpha|]
  ==> contraction_alpha (traces (P ;; Q)) alpha"
by (simp add: contraction_alpha_def map_alpha_traces_Seq_compo)

(*--------------------------------*
 |       Seq_compo  (gSKIP)       |
 *--------------------------------*)

(*** rest_domT (subset) ***)

lemma gSKIP_Seq_compo_rest_domT_sub:
   "[| traces P1 M1 .|. (Suc n) <= traces P2 M2 .|. (Suc n) ;
       traces Q1 M1 .|. n <= traces Q2 M2 .|. n ;
       <Tick> ~:t traces P1 M1 ;
       <Tick> ~:t traces P2 M2 |]
    ==> traces (P1 ;; Q1) M1 .|. (Suc n) <= traces (P2 ;; Q2) M2 .|. (Suc n)"
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_rest_domT)
apply (simp add: in_traces)
apply (elim conjE exE disjE)

 (* case 1 *)
 apply (rule disjI1)
 apply (insert trace_last_noTick_or_Tick)
 apply (rotate_tac -1)
 apply (drule_tac x="s" in spec)
 apply (erule disjE)
 apply (rule_tac x="s" in exI, simp)

 apply (elim conjE exE)
 apply (rule_tac x="sa" in exI, simp)
 apply (drule_tac x="sa" in spec, simp)
 apply (drule mp)
 apply (rule memT_prefix_closed, simp_all, simp)

 (* case 2 *)
 apply (case_tac "~ noTick s", simp)
 apply (insert trace_last_nil_or_unnil)
 apply (rotate_tac -1)
 apply (drule_tac x="ta" in spec)
 apply (erule disjE)

  apply (rule disjI1)                (* ta = []t *)
  apply (rule_tac x="s" in exI, simp)
  apply (drule_tac x="s" in spec, simp)
  apply (drule mp)
  apply (rule memT_prefix_closed, simp_all, simp)

  apply (rule disjI2)                (* ta ~= []t *)
  apply (elim conjE exE, simp)

  apply (drule_tac x="s ^^^ <Tick>" in spec)
  apply (drule_tac x=" sa ^^^ <a>" in spec)
  apply (simp)
  apply (rule_tac x="s" in exI)
  apply (rule_tac x="sa ^^^ <a>" in exI)
  apply (simp)

 apply (insert trace_last_nil_or_unnil)
 apply (rotate_tac -1)
 apply (drule_tac x="s" in spec)
 apply (erule disjE)
  apply (auto)
done

(*** rest_domT (equal) ***)

lemma gSKIP_Seq_compo_rest_domT:
   "[| traces P1 M1 .|. (Suc n) = traces P2 M2 .|. (Suc n) ;
       traces Q1 M1 .|. n = traces Q2 M2 .|. n ;
       <Tick> ~:t traces P1 M1 ;
       <Tick> ~:t traces P2 M2 |]
    ==> traces (P1 ;; Q1) M1 .|. (Suc n) = traces (P2 ;; Q2) M2 .|. (Suc n)"
apply (rule order_antisym)
by (simp_all add: gSKIP_Seq_compo_rest_domT_sub)

(*** map_alpha T lemma ***)

lemma gSKIP_map_alpha_traces_Seq_compo_lm:
  "[| distance (traces P1 M1, traces P2 M2) * 2 <= (1/2)^n ;
      distance (traces Q1 M1, traces Q2 M2) <= (1/2)^n ;
       <Tick> ~:t traces P1 M1 ;
       <Tick> ~:t traces P2 M2 |]
    ==> distance (traces (P1 ;; Q1) M1, traces (P2 ;; Q2) M2) * 2
     <= (1/2)^n"
apply (insert gSKIP_Seq_compo_rest_domT)
apply (insert gSKIP_Seq_compo_rest_domT[of P1 M1 n P2 M2 Q1 Q2])
apply (simp only: to_distance_rs)
apply (simp add: distance_rs_le_1)
done

(*** map_alpha ***)

lemma gSKIP_contraction_half_traces_Seq_compo:
 "[| contraction_alpha (traces P) (1/2) ; non_expanding (traces Q) ;
     gSKIP P |]
  ==> contraction_alpha (traces (P ;; Q)) (1/2)"
apply (simp add: contraction_alpha_def non_expanding_def map_alpha_def)
apply (intro allI)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="y" in spec)

apply (case_tac "x = y", simp)
apply (simp only: to_distance_rs)
apply (simp add: distance_iff)
apply (insert gSKIP_to_Tick_notin_traces)
apply (frule_tac x="P" in spec)
apply (drule_tac x="P" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (simp)
apply (fold to_distance_rs)
apply (simp add: gSKIP_map_alpha_traces_Seq_compo_lm)
done

(*--------------------------------*
 |          Depth_rest            |
 *--------------------------------*)

(*** rest_domT (equal) ***)

lemma Depth_rest_rest_domT:
   "traces P M1 .|. n = traces Q M2 .|. n
    ==> traces (P |. m) M1 .|. n = traces (Q |. m) M2 .|. n"
apply (simp add: traces.simps)
apply (simp add: min_rs)
apply (rule rest_equal_preserve)
apply (simp)
apply (simp add: min_def)
done

(*** distT lemma ***)

lemma Depth_rest_distT:
     "distance(traces (P |. m) M1, traces (Q |. m) M2) <= 
      distance(traces P M1, traces Q M2)"
apply (simp only: to_distance_rs)
apply (rule rest_distance_subset)
by (auto intro: Depth_rest_rest_domT)

(*** map_alphaT lemma ***)

lemma map_alpha_traces_Depth_rest_lm:
  "distance(traces P M1, traces Q M2) <= alpha * distance (x1, x2)
    ==> distance(traces (P |. m) M1, traces (Q |. m) M2)
     <= alpha * distance(x1, x2)"
apply (insert Depth_rest_distT[of P m M1 Q M2])
by (simp)

(*** map_alpha ***)

lemma map_alpha_traces_Depth_rest:
 "map_alpha (traces P) alpha
  ==> map_alpha (traces (P |. m)) alpha"
apply (simp add: map_alpha_def)
apply (intro allI)
apply (erule conjE)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
by (simp add: map_alpha_traces_Depth_rest_lm)

(*** non_expanding ***)

lemma non_expanding_traces_Depth_rest:
 "non_expanding (traces P)
  ==> non_expanding (traces (P |. m))"
by (simp add: non_expanding_def map_alpha_traces_Depth_rest)

(*** contraction_alpha ***)

lemma contraction_alpha_traces_Depth_rest:
 "contraction_alpha (traces P) alpha
  ==> contraction_alpha (traces (P |. m)) alpha"
by (simp add: contraction_alpha_def map_alpha_traces_Depth_rest)

(*--------------------------------*
 |            variable            |
 *--------------------------------*)

(*** non_expanding ***)

lemma non_expanding_traces_variable: 
   "non_expanding (traces ($p))"
apply (simp add: traces_iff)
apply (simp add: non_expanding_prod_variable)
done



(*--------------------------------*
 |            Procfun             |
 *--------------------------------*)

(*****************************************************************
 |                         non_expanding                         |
 *****************************************************************)

lemma non_expanding_traces_lm: 
  "noHide P --> non_expanding (traces P)"
apply (induct_tac P)
apply (simp add: non_expanding_traces_STOP)
apply (simp add: non_expanding_traces_SKIP)
apply (simp add: non_expanding_traces_DIV)
apply (simp add: non_expanding_traces_Act_prefix)
apply (simp add: non_expanding_traces_Ext_pre_choice)
apply (simp add: non_expanding_traces_Ext_choice)
apply (simp add: non_expanding_traces_Int_choice)
apply (simp add: non_expanding_traces_Rep_int_choice)
apply (simp add: non_expanding_traces_IF)
apply (simp add: non_expanding_traces_Parallel)

(* hiding --> const *)
apply (intro impI)
(* apply (subgoal_tac "EX T. (traces (proc -- fun) = (%M. T))") isabelle 2011 *)
(* apply (subgoal_tac "EX T. (traces (proc -- set) = (%M. T))") *)
apply (subgoal_tac "EX T. (traces (x1 -- x2) = (%M. T))")
apply (erule exE)
apply (simp)
apply (simp add: non_expanding_Constant)
apply (rule traces_noPN_Constant)
apply (simp)

apply (simp add: non_expanding_traces_Renaming)
apply (simp add: non_expanding_traces_Seq_compo)

(* Depth_res *)
apply (simp add: non_expanding_traces_Depth_rest)
apply (simp add: traces_iff)
apply (simp add: zero_rs_domT)
apply (simp add: non_expanding_Constant)

apply (simp add: non_expanding_traces_variable)
done

lemma non_expanding_traces: 
  "noHide P ==> non_expanding (traces P)"
apply (simp add: non_expanding_traces_lm)
done

(*=============================================================*
 |                          [[P]]Tf                            |
 *=============================================================*)

lemma non_expanding_semTf: 
  "noHide P ==> non_expanding [[P]]Tf"
apply (simp add: semTf_def)
apply (simp add: non_expanding_traces)
done

(*=============================================================*
 |                         [[P]]Tfun                           |
 *=============================================================*)

lemma non_expanding_semTfun: 
  "noHidefun Pf ==> non_expanding [[Pf]]Tfun"
apply (simp add: noHidefun_def)
apply (simp add: prod_non_expand)
apply (simp add: semTfun_def)
apply (simp add: proj_fun_def)
apply (simp add: comp_def)
apply (simp add: non_expanding_semTf)
done

(*****************************************************************
 |                         contraction                           |
 *****************************************************************)

lemma contraction_alpha_traces_lm: 
  "guarded P --> contraction_alpha (traces P) (1/2)"
apply (induct_tac P)
apply (simp add: contraction_alpha_traces_STOP)
apply (simp add: contraction_alpha_traces_SKIP)
apply (simp add: contraction_alpha_traces_DIV)
apply (simp add: contraction_half_traces_Act_prefix
                 non_expanding_traces)
apply (simp add: contraction_half_traces_Ext_pre_choice
                 non_expanding_traces)
apply (simp add: contraction_alpha_traces_Ext_choice)
apply (simp add: contraction_alpha_traces_Int_choice)
apply (simp add: contraction_alpha_traces_Rep_int_choice)
apply (simp add: contraction_alpha_traces_IF)
apply (simp add: contraction_alpha_traces_Parallel)

(* hiding --> const *)
apply (intro impI)
(* apply (subgoal_tac "EX T. (traces (proc -- fun) = (%M. T))") isabelle 2011 *)
(* apply (subgoal_tac "EX T. (traces (proc -- set) = (%M. T))") *)
apply (subgoal_tac "EX T. (traces (x1 -- x2) = (%M. T))")
apply (erule exE)
apply (simp add: contraction_alpha_Constant)
apply (rule traces_noPN_Constant)
apply (simp)

apply (simp add: contraction_alpha_traces_Renaming)

(* Seq_compo *)
apply (simp)
apply (intro conjI impI)
apply (simp add: gSKIP_contraction_half_traces_Seq_compo
                 non_expanding_traces)
apply (simp add: contraction_alpha_traces_Seq_compo)

(* Depth_res *)
apply (simp add: contraction_alpha_traces_Depth_rest)
apply (simp add: traces_iff)
apply (simp add: zero_rs_domT)
apply (simp add: contraction_alpha_Constant)

apply (simp)
done

lemma contraction_alpha_traces: 
  "guarded P ==> contraction_alpha (traces P) (1/2)"
by (simp add: contraction_alpha_traces_lm)

(*=============================================================*
 |                          [[P]]Tf                            |
 *=============================================================*)

lemma contraction_alpha_semTf: 
  "guarded P ==> contraction_alpha [[P]]Tf (1/2)"
apply (simp add: semTf_def)
apply (simp add: contraction_alpha_traces)
done

(*=============================================================*
 |                         [[P]]Tfun                           |
 *=============================================================*)

lemma contraction_alpha_semTfun: 
  "guardedfun Pf ==> contraction_alpha [[Pf]]Tfun (1/2)"
apply (simp add: guardedfun_def)
apply (simp add: prod_contra_alpha)
apply (simp add: semTfun_def)
apply (simp add: proj_fun_def)
apply (simp add: comp_def)
apply (simp add: contraction_alpha_semTf)
done

(*=============================================================*
 |                        contraction                          |
 *=============================================================*)

lemma contraction_semTfun: 
  "guardedfun Pf ==> contraction [[Pf]]Tfun"
apply (simp add: contraction_def)
apply (rule_tac x="1/2" in exI)
apply (simp add:contraction_alpha_semTfun)
done

end
