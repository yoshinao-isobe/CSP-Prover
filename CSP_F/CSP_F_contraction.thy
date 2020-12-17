           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005 (modified)    |
            |              September 2005 (modified)    |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
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

theory CSP_F_contraction
imports CSP_F_domain CSP_T.CSP_T_contraction
begin

(*****************************************************************

         1. contraction failuresfun
         2. contraction failuresFun
         3. contraction [[ ]]Ffun
         4. contraction [[ ]]FFun

 *****************************************************************)

(*=============================================================*
 |                      traces fstF                            |
 *=============================================================*)

lemma non_expanding_traces_fstF:
   "noHide P ==> non_expanding (%M. traces P (fstF o M))"
(* apply (subgoal_tac "(%M. traces P (fstF o M)) = (traces P) o (op o fstF)") *)
apply (subgoal_tac "(%M. traces P (fstF o M)) = (traces P) o ((o) fstF)")
apply (simp)
apply (rule compo_non_expand)
apply (simp add: non_expanding_traces)
apply (simp add: non_expanding_op_fstF)
apply (simp add: fun_eq_iff)
done

lemma contraction_alpha_traces_fstF:
   "guarded P ==> contraction_alpha (%M. traces P (fstF o M)) (1/2)"
(* apply (subgoal_tac "(%M. traces P (fstF o M)) = (traces P) o (op o fstF)") *)
apply (subgoal_tac "(%M. traces P (fstF o M)) = (traces P) o ((o) fstF)")
apply (simp)
apply (rule compo_contra_alpha_non_expand)
apply (simp add: contraction_alpha_traces)
apply (simp add: non_expanding_op_fstF)
apply (simp add: fun_eq_iff)
done

(*--------------------------------*
 |        STOP,SKIP,DIV           |
 *--------------------------------*)

(*** STOP ***)

lemma map_alpha_failures_STOP: 
  "0 <= alpha ==> map_alpha (failures (STOP)) alpha"
by (simp add: failures_iff map_alpha_Constant)

lemma non_expanding_failures_STOP: 
  "non_expanding (failures (STOP))"
by (simp add: non_expanding_def map_alpha_failures_STOP)

lemma contraction_alpha_failures_STOP: 
  "[| 0 <= alpha ; 1 > alpha |] ==> contraction_alpha (failures (STOP)) alpha"
by (simp add: failures_iff contraction_alpha_Constant)

(*** SKIP ***)

lemma map_alpha_failures_SKIP: 
  "0 <= alpha ==> map_alpha (failures (SKIP)) alpha"
by (simp add: failures_iff map_alpha_Constant)

lemma non_expanding_failures_SKIP: 
  "non_expanding (failures (SKIP))"
by (simp add: non_expanding_def map_alpha_failures_SKIP)

lemma contraction_alpha_failures_SKIP: 
  "[| 0 <= alpha ; 1 > alpha |] ==> contraction_alpha (failures (SKIP)) alpha"
by (simp add: failures_iff contraction_alpha_Constant)

(*** DIV ***)

lemma map_alpha_failures_DIV: 
  "0 <= alpha ==> map_alpha (failures (DIV)) alpha"
by (simp add: failures_iff map_alpha_Constant)

lemma non_expanding_failures_DIV: 
  "non_expanding (failures (DIV))"
by (simp add: non_expanding_def map_alpha_failures_DIV)

lemma contraction_alpha_failures_DIV: 
  "[| 0 <= alpha ; 1 > alpha |] ==> contraction_alpha (failures (DIV)) alpha"
by (simp add: failures_iff contraction_alpha_Constant)

(*--------------------------------*
 |          Act_prefix            |
 *--------------------------------*)

lemma contraction_half_failures_Act_prefix_lm: 
   "distance (failures (a -> P) M1, failures (a -> Q) M2) * 2
    = distance (failures P M1, failures Q M2)"
apply (rule sym)
apply (simp add: to_distance_rs)
apply (rule rest_Suc_dist_half[simplified])
apply (rule allI)
apply (simp add: rest_setF_eq_iff)
apply (rule iffI)

 (* => *)
 apply (intro allI)
 apply (simp add: in_failures)
 apply (rule iffI)

  (* => *)
  apply (elim conjE exE disjE)
   apply (simp_all)
   apply (drule_tac x="sa" in spec)
   apply (drule_tac x="X" in spec)
   apply (simp)

   apply (drule_tac x="sa" in spec)
   apply (drule_tac x="X" in spec)
   apply (simp)
   apply (erule iffE, simp)
   apply (insert trace_last_nil_or_unnil)
   apply (drule_tac x="sa" in spec)
   apply (erule disjE, simp)
   apply (elim conjE exE)
   apply (simp add: appt_assoc_sym)
   apply (drule mp, fast)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (simp)

  (* <= *)
  apply (elim conjE exE disjE)
   apply (simp_all)
   apply (drule_tac x="sa" in spec)
   apply (drule_tac x="X" in spec)
   apply (simp)

   apply (drule_tac x="sa" in spec)
   apply (drule_tac x="X" in spec)
   apply (simp)
   apply (erule iffE, simp)
   apply (drule_tac x="sa" in spec)
   apply (erule disjE, simp)
   apply (elim conjE exE)
   apply (simp add: appt_assoc_sym)
   apply (drule mp, fast)
   apply (simp)

 (* <= *)
 apply (intro allI)
 apply (drule_tac x="<Ev a> ^^^ s" in spec)
 apply (drule_tac x="X" in spec)
 apply (simp add: in_failures)
 apply (rule iffI)

  (* => *)
  apply (elim conjE exE disjE)
   apply (simp)
   apply (erule iffE, simp)
   apply (simp add: appt_assoc_sym)
   apply (drule mp, force)
   apply (force)

  (* <= *)
  apply (elim conjE exE disjE)
   apply (simp)
   apply (erule iffE, simp)
   apply (simp add: appt_assoc_sym)
   apply (drule mp, force)
   apply (force)
done

(***  contraction_half ***)

lemma contraction_half_failures_Act_prefix: 
 "non_expanding (failures P)
  ==> contraction_alpha (failures (a -> P)) (1 / 2)"
apply (simp add: contraction_alpha_def non_expanding_def map_alpha_def)
apply (intro allI)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (simp add: contraction_half_failures_Act_prefix_lm)
done

(***  contraction ***)

lemma contraction_failures_Act_prefix: 
 "non_expanding (failures P)
  ==> contraction (failures (a -> P))"
apply (simp add: contraction_def)
apply (rule_tac x="1/2" in exI)
by (simp add: contraction_half_failures_Act_prefix)

(*** non_expanding ***)

lemma non_expanding_failures_Act_prefix: 
 "non_expanding (failures P)
  ==> non_expanding (failures (a -> P))"
apply (rule contraction_non_expanding)
by (simp add: contraction_failures_Act_prefix)

(*--------------------------------*
 |        Ext_pre_choice          |
 *--------------------------------*)

(*** rest_setF (subset) ***)

lemma Ext_pre_choice_Act_prefix_rest_setF_sub:
   "[| ALL a : X.
         failures (a -> Pf a) M1 .|. n <= failures (a -> Qf a) M2 .|. n |]
    ==> failures (? a:X -> Pf a) M1 .|. n <=
        failures (? a:X -> Qf a) M2 .|. n"
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (simp add: in_rest_setF)
apply (simp add: in_failures)
apply (elim conjE exE disjE, simp_all)

 apply (drule_tac x="a" in bspec, simp)
 apply (drule_tac x="<Ev a> ^^^ sa" in spec)
 apply (drule_tac x="Xa" in spec)
 apply (simp)

 apply (drule_tac x="a" in bspec, simp)
 apply (drule_tac x="s' ^^^ <Tick>" in spec)
 apply (drule_tac x="Xa" in spec)
 apply (auto)
done

(*** rest_setF (equal) ***)

lemma Ext_pre_choice_Act_prefix_rest_setF:
   "[| ALL a : X.
         failures (a -> Pf a) M1 .|. n = failures (a -> Qf a) M2 .|. n |]
    ==> failures (? a:X -> Pf a) M1 .|. n =
        failures (? a:X -> Qf a) M2 .|. n"
apply (rule order_antisym)
by (simp_all add: Ext_pre_choice_Act_prefix_rest_setF_sub)

(*** distF lemma ***)

lemma Ext_pre_choice_Act_prefix_distF_nonempty:
"[| X ~= {} ; PQs = {(failures (a -> Pf a) M1, failures (a -> Qf a) M2)|a. a : X} |]
 ==> (EX PQ. PQ:PQs & 
             distance(failures (? a:X -> Pf a) M1, failures (? a:X -> Qf a) M2)
          <= distance(fst PQ, snd PQ))"
apply (simp only: to_distance_rs)
apply (rule rest_to_dist_pair)
apply (force)

apply (intro allI impI)
apply (rule Ext_pre_choice_Act_prefix_rest_setF)
apply (rule ballI)
apply (simp)
apply (drule_tac x="failures (a -> Pf a) M1" in spec)
apply (drule_tac x="failures (a -> Qf a) M2" in spec)
by (auto)

(*** contraction lemma ***)

lemma contraction_half_failures_Ext_pre_choice_lm:
  "[| X ~= {} ; ALL a. distance (failures (Pf a) M1, failures (Qf a) M2)
                    <= distance (x1, x2) |]
    ==> distance (failures (? a:X -> Pf a) M1, failures (? a:X -> Qf a) M2) * 2 
     <= distance (x1, x2)"
apply (insert Ext_pre_choice_Act_prefix_distF_nonempty
       [of X "{(failures (a -> Pf a) M1, failures (a -> Qf a) M2) |a. a : X}" 
           Pf M1 Qf M2])
apply (simp)
apply (elim conjE exE)
apply (simp)
apply (subgoal_tac 
    "distance (failures (aa -> Pf aa) M1, failures (aa -> Qf aa) M2) * 2
   = distance (failures (Pf aa) M1, failures (Qf aa) M2)")
apply (drule_tac x="aa" in spec)
apply (force)
by (simp add: contraction_half_failures_Act_prefix_lm)

(*** contraction_half ***)

lemma contraction_half_failures_Ext_pre_choice:
 "ALL a. non_expanding (failures (Pf a))
  ==> contraction_alpha (failures (? a:X -> (Pf a))) (1 / 2)"
apply (simp add: contraction_alpha_def non_expanding_def map_alpha_def)
apply (case_tac "X = {}")
apply (simp add: failures_iff)
by (simp add: contraction_half_failures_Ext_pre_choice_lm)

(*** Ext_pre_choice_evalT_contraction ***)

lemma contraction_failures_Ext_pre_choice:
 "ALL a. non_expanding (failures (Pf a))
  ==> contraction (failures (? a:X -> (Pf a)))"
apply (simp add: contraction_def)
apply (rule_tac x="1/2" in exI)
by (simp add: contraction_half_failures_Ext_pre_choice)

(*** Ext_pre_choice_evalT_non_expanding ***)

lemma non_expanding_failures_Ext_pre_choice:
 "ALL a. non_expanding (failures (Pf a))
  ==> non_expanding (failures (? a:X -> (Pf a)))"
apply (rule contraction_non_expanding)
by (simp add: contraction_failures_Ext_pre_choice)

(*--------------------------------*
 |          Ext_choice            |
 *--------------------------------*)

(*** rest_domT (subset) ***)

lemma Ext_choice_rest_setF_sub:
   "[| traces P1 (fstF o M1) .|. n <= traces P2 (fstF o M2) .|. n ;
       traces Q1 (fstF o M1) .|. n <= traces Q2 (fstF o M2) .|. n ;
       failures P1 M1 .|. n <= failures P2 M2 .|. n ;
       failures Q1 M1 .|. n <= failures Q2 M2 .|. n  |]
    ==> failures (P1 [+] Q1) M1 .|. n <= failures (P2 [+] Q2) M2 .|. n"
apply (simp add: subdomT_iff subsetF_iff)
apply (intro allI impI)
apply (simp add: in_rest_domT)
apply (simp add: in_rest_setF)
apply (simp add: in_failures)
apply (elim conjE exE disjE, simp_all)

 apply (rotate_tac 2)
 apply (drule_tac x="s' ^^^ <Tick>" in spec)
 apply (drule_tac x="X" in spec)
 apply (drule mp, simp, fast)
 apply (simp)

 apply (rotate_tac 3)
 apply (drule_tac x="s' ^^^ <Tick>" in spec)
 apply (drule_tac x="X" in spec)
 apply (drule mp, simp, fast)
 apply (simp)
done

(*** rest_setF (equal) ***)

lemma Ext_choice_rest_setF:
   "[| traces P1 (fstF o M1) .|. n = traces P2 (fstF o M2) .|. n ;
       traces Q1 (fstF o M1) .|. n = traces Q2 (fstF o M2) .|. n ;
       failures P1 M1 .|. n = failures P2 M2 .|. n ;
       failures Q1 M1 .|. n = failures Q2 M2 .|. n  |]
    ==> failures (P1 [+] Q1) M1 .|. n = failures (P2 [+] Q2) M2 .|. n"
apply (rule order_antisym)
by (simp_all add: Ext_choice_rest_setF_sub)

(*** distF lemma ***)

lemma Ext_choice_distF:
"[| PQTs = {(traces P1 (fstF o M1), traces P2 (fstF o M2)), 
            (traces Q1 (fstF o M1), traces Q2 (fstF o M2))} ;
    PQFs = {(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)} |]
 ==> (EX PQ. PQ:PQTs & 
             distance(failures (P1 [+] Q1) M1, failures (P2 [+] Q2) M2)
          <= distance((fst PQ), (snd PQ))) |
     (EX PQ. PQ:PQFs & 
             distance(failures (P1 [+] Q1) M1, failures (P2 [+] Q2) M2)
          <= distance((fst PQ), (snd PQ)))"
apply (simp only: to_distance_rs)
apply (rule rest_to_dist_pair_two)
apply (simp_all)
by (auto intro: Ext_choice_rest_setF)

(*** map_alpha F lemma ***)

lemma map_alpha_failures_Ext_choice_lm:
  "[| distance (traces P1 (fstF o M1), traces P2 (fstF o M2))
       <= alpha * distance (x1, x2) ;
      distance (traces Q1 (fstF o M1), traces Q2 (fstF o M2))
       <= alpha * distance (x1, x2) ;
      distance (failures P1 M1, failures P2 M2) <= alpha * distance (x1, x2) ;
      distance (failures Q1 M1, failures Q2 M2) <= alpha * distance (x1, x2) |]
    ==> distance (failures (P1 [+] Q1) M1, failures (P2 [+] Q2) M2)
     <= alpha * distance (x1, x2)"
apply (insert Ext_choice_distF
       [of "{(traces P1 (fstF o M1), traces P2 (fstF o M2)), 
             (traces Q1 (fstF o M1), traces Q2 (fstF o M2))}"
             P1 M1 P2 M2 Q1 Q2
           "{(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)}"])
by (auto)

(*** map_alpha ***)

lemma map_alpha_failures_Ext_choice:
 "[| map_alpha (%M. traces P (fstF o M)) alpha ; 
     map_alpha (%M. traces Q (fstF o M)) alpha ;
     map_alpha (failures P) alpha ;
     map_alpha (failures Q) alpha |]
  ==> map_alpha (failures (P [+] Q)) alpha"
apply (simp add: map_alpha_def)
apply (intro allI)
apply (erule conjE)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="y" in spec)
by (simp add: map_alpha_failures_Ext_choice_lm)

(*** non_expanding ***)

lemma non_expanding_failures_Ext_choice:
 "[| non_expanding (%M. traces P (fstF o M)) ;
     non_expanding (%M. traces Q (fstF o M)) ;
     non_expanding (failures P) ; non_expanding (failures Q) |]
  ==> non_expanding (failures (P [+] Q))"
by (simp add: non_expanding_def map_alpha_failures_Ext_choice)

(*** contraction ***)

lemma contraction_alpha_failures_Ext_choice:
 "[| contraction_alpha (%M. traces P (fstF o M)) alpha ;
     contraction_alpha (%M. traces Q (fstF o M)) alpha ;
     contraction_alpha (failures P) alpha ; 
     contraction_alpha (failures Q) alpha|]
  ==> contraction_alpha (failures (P [+] Q)) alpha"
by (simp add: contraction_alpha_def map_alpha_failures_Ext_choice)

(*--------------------------------*
 |          Int_choice            |
 *--------------------------------*)

(*** rest_domT (subset) ***)

lemma Int_choice_rest_setF_sub:
   "[| failures P1 M1 .|. n <= failures P2 M2 .|. n ;
       failures Q1 M1 .|. n <= failures Q2 M2 .|. n  |]
    ==> failures (P1 |~| Q1) M1 .|. n <= failures (P2 |~| Q2) M2 .|. n"
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (simp add: in_rest_setF)
apply (simp add: in_failures)
apply (elim disjE conjE exE)
by (force)+

(*** rest_setF (equal) ***)

lemma Int_choice_rest_setF:
   "[| failures P1 M1 .|. n = failures P2 M2 .|. n ;
       failures Q1 M1 .|. n = failures Q2 M2 .|. n  |]
    ==> failures (P1 |~| Q1) M1 .|. n = failures (P2 |~| Q2) M2 .|. n"
apply (rule order_antisym)
by (simp_all add: Int_choice_rest_setF_sub)

(*** distF lemma ***)

lemma Int_choice_distF:
"PQs = {(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)}
 ==> (EX PQ. PQ:PQs & 
             distance(failures (P1 |~| Q1) M1, failures (P2 |~| Q2) M2)
          <= distance((fst PQ), (snd PQ)))"
apply (simp only: to_distance_rs)
apply (rule rest_to_dist_pair)
by (auto intro: Int_choice_rest_setF)

(*** map_alpha F lemma ***)

lemma map_alpha_failures_Int_choice_lm:
  "[| distance (failures P1 M1, failures P2 M2) <= alpha * distance (x1, x2) ;
      distance (failures Q1 M1, failures Q2 M2) <= alpha * distance (x1, x2) |]
    ==> distance (failures (P1 |~| Q1) M1, failures (P2 |~| Q2) M2)
     <= alpha * distance (x1, x2)"
apply (insert Int_choice_distF
       [of "{(failures P1 M1, failures P2 M2), 
             (failures Q1 M1, failures Q2 M2)}" P1 M1 P2 M2 Q1 Q2])
by (auto)

(*** map_alpha ***)

lemma map_alpha_failures_Int_choice:
 "[| map_alpha (failures P) alpha ; map_alpha (failures Q) alpha |]
  ==> map_alpha (failures (P |~| Q)) alpha"
apply (simp add: map_alpha_def)
apply (intro allI)
apply (erule conjE)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="y" in spec)
by (simp add: map_alpha_failures_Int_choice_lm)

(*** non_expanding ***)

lemma non_expanding_failures_Int_choice:
 "[| non_expanding (failures P) ; non_expanding (failures Q) |]
  ==> non_expanding (failures (P |~| Q))"
by (simp add: non_expanding_def map_alpha_failures_Int_choice)

(*** contraction ***)

lemma contraction_alpha_failures_Int_choice:
 "[| contraction_alpha (failures P) alpha ; 
     contraction_alpha (failures Q) alpha|]
  ==> contraction_alpha (failures (P |~| Q)) alpha"
by (simp add: contraction_alpha_def map_alpha_failures_Int_choice)

(*--------------------------------*
 |        Rep_int_choice          |
 *--------------------------------*)

(*** rest_setF (subset) ***)

lemma Rep_int_choice_rest_setF_sub:
   "[| ALL c : sumset C.
         failures (Pf c) M1 .|. n <= failures (Qf c) M2 .|. n |]
    ==> failures (!! :C .. Pf) M1 .|. n <=
        failures (!! :C .. Qf) M2 .|. n"
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (simp add: in_rest_setF)
apply (simp add: in_failures)
apply (elim conjE bexE)
apply (rule_tac x="c" in bexI)
by (auto)

(*** rest_setF (equal) ***)

lemma Rep_int_choice_rest_setF:
   "[| ALL c : sumset C.
         failures (Pf c) M1 .|. n = failures (Qf c) M2 .|. n |]
    ==> failures (!! :C .. Pf) M1 .|. n =
        failures (!! :C .. Qf) M2 .|. n"
apply (rule order_antisym)
by (simp_all add: Rep_int_choice_rest_setF_sub)

(*** distF lemma ***)

lemma Rep_int_choice_distF_nonempty:
"[| sumset C ~= {} ; 
    PQs = {(failures (Pf c) M1, failures (Qf c) M2)|c. c : sumset C} |]
 ==> (EX PQ. PQ:PQs & 
             distance(failures (!! :C .. Pf) M1, failures (!! :C .. Qf) M2)
          <= distance(fst PQ, snd PQ))"
apply (simp only: to_distance_rs)
apply (rule rest_to_dist_pair)
apply (fast)

apply (intro allI impI)
apply (rule Rep_int_choice_rest_setF)
by (auto)

(*** map_alpha F lemma ***)

lemma map_alpha_failures_Rep_int_choice_lm:
"[| sumset C ~= {} ; 
    ALL c. distance (failures (Pf c) M1, failures (Qf c) M2) 
                  <= alpha * distance (x1, x2) |]
 ==> distance(failures (!! :C .. Pf) M1, failures (!! :C .. Qf) M2)
  <= alpha * distance(x1, x2)"
apply (insert Rep_int_choice_distF_nonempty)
apply (insert Rep_int_choice_distF_nonempty
       [of C "{(failures (Pf c) M1, failures (Qf c) M2)|c. c : sumset C}"
           Pf M1 Qf M2])
apply (simp)
apply (elim conjE exE, simp)
apply (drule_tac x="c" in spec)
by (force)

(*** map_alpha ***)

lemma map_alpha_failures_Rep_int_choice:
 "ALL c. map_alpha (failures (Pf c)) alpha
  ==> map_alpha (failures (!! :C .. Pf)) alpha"
apply (simp add: map_alpha_def)
apply (case_tac "sumset C = {}")
 apply (simp add: failures_iff)
(* apply (simp add: real_mult_order_eq) *)
apply (simp add: map_alpha_failures_Rep_int_choice_lm)
done

(*** non_expanding ***)

lemma non_expanding_failures_Rep_int_choice:
 "ALL c. non_expanding (failures (Pf c))
  ==> non_expanding (failures (!! :C .. Pf))"
by (simp add: non_expanding_def map_alpha_failures_Rep_int_choice)

(*** Rep_int_choice_evalT_contraction_alpha ***)

lemma contraction_alpha_failures_Rep_int_choice:
 "ALL c. contraction_alpha (failures (Pf c)) alpha 
     ==> contraction_alpha  (failures (!! :C .. Pf)) alpha"
by (simp add: contraction_alpha_def map_alpha_failures_Rep_int_choice)

(*--------------------------------*
 |              IF                |
 *--------------------------------*)

(*** rest_setF (subset) ***)

lemma IF_rest_setF_sub:
   "[| failures P1 M1 .|. n <= failures P2 M2 .|. n ;
       failures Q1 M1 .|. n <= failures Q2 M2 .|. n  |]
    ==> failures (IF b THEN P1 ELSE Q1) M1 .|. n <= 
        failures (IF b THEN P2 ELSE Q2) M2 .|. n"
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (simp add: in_rest_setF)
apply (simp add: in_failures)
done

(*** rest_setF (equal) ***)

lemma IF_rest_setF:
   "[| failures P1 M1 .|. n = failures P2 M2 .|. n ;
       failures Q1 M1 .|. n = failures Q2 M2 .|. n  |]
    ==> failures (IF b THEN P1 ELSE Q1) M1 .|. n = 
        failures (IF b THEN P2 ELSE Q2) M2 .|. n"
apply (rule order_antisym)
by (simp_all add: IF_rest_setF_sub)

(*** distF lemma ***)

lemma IF_distF:
   "PQs = {(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)}
    ==> (EX PQ. PQ:PQs & 
             distance(failures (IF b THEN P1 ELSE Q1) M1,
                      failures (IF b THEN P2 ELSE Q2) M2)
          <= distance((fst PQ), (snd PQ)))"
apply (simp only: to_distance_rs)
apply (rule rest_to_dist_pair)
by (auto intro: IF_rest_setF)

(*** map_alpha F lemma ***)

lemma map_alpha_failures_IF_lm:
  "[| distance (failures P1 M1, failures P2 M2) <= alpha * distance (x1, x2) ;
      distance (failures Q1 M1, failures Q2 M2) <= alpha * distance (x1, x2) |]
    ==> distance(failures (IF b THEN P1 ELSE Q1) M1,
                 failures (IF b THEN P2 ELSE Q2) M2)
     <= alpha * distance (x1, x2)"
apply (insert IF_distF
       [of "{(failures P1 M1, failures P2 M2), 
             (failures Q1 M1, failures Q2 M2)}"P1 M1 P2 M2 Q1 Q2 b])
by (auto)

(*** map_alpha ***)

lemma map_alpha_failures_IF:
 "[| map_alpha (failures P) alpha ; map_alpha (failures Q) alpha |]
  ==> map_alpha (failures (IF b THEN P ELSE Q)) alpha"
apply (simp add: map_alpha_def)
apply (intro allI)
apply (erule conjE)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="y" in spec)
by (simp add: map_alpha_failures_IF_lm)

(*** non_expanding ***)

lemma non_expanding_failures_IF:
 "[| non_expanding (failures P) ; non_expanding (failures Q) |]
  ==> non_expanding (failures (IF b THEN P ELSE Q))"
by (simp add: non_expanding_def map_alpha_failures_IF)

(*** contraction_alpha ***)

lemma contraction_alpha_failures_IF:
 "[| contraction_alpha (failures P) alpha ; contraction_alpha (failures Q) alpha|]
  ==> contraction_alpha (failures (IF b THEN P ELSE Q)) alpha"
by (simp add: contraction_alpha_def map_alpha_failures_IF)

(*--------------------------------*
 |           Parallel             |
 *--------------------------------*)

(*** rest_setF (subset) ***)

lemma Parallel_rest_setF_sub:
   "[| failures P1 M1 .|. n <= failures P2 M2 .|. n ;
       failures Q1 M1 .|. n <= failures Q2 M2 .|. n  |]
    ==> failures (P1 |[X]| Q1) M1 .|. n <= failures (P2 |[X]| Q2) M2 .|. n"
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (simp add: in_rest_setF)
apply (simp add: in_failures)
apply (elim conjE exE)

apply (rule_tac x="Y" in exI)
apply (rule_tac x="Z" in exI)
apply (simp)
apply (rule_tac x="sa" in exI)
apply (rule_tac x="t" in exI)
apply (simp)
apply (drule_tac x="sa" in spec)
apply (drule_tac x="t" in spec)
apply (drule_tac x="Y" in spec)
apply (drule_tac x="Z" in spec)

apply (erule disjE, simp)    (* lengtht s < n *)
apply (erule par_tr_lengthtE)
apply (simp)

apply (elim conjE exE, simp) (* lengtht s = n *)
apply (simp add: par_tr_last)
apply (elim conjE exE, simp)
apply (erule par_tr_lengthtE)
apply (case_tac "Suc (lengtht s'a) < n", simp)
 apply (case_tac "Suc (lengtht t') < n", simp)
 apply (case_tac "Suc (lengtht t') = n", simp)
 apply (drule mp, force)
 apply (simp)
 apply (force)  (* contradict *)

 apply (case_tac "Suc (lengtht t') < n", simp)
 apply (drule mp)
  apply (rule_tac x="s'a" in exI, simp)
 apply (simp)

 apply (case_tac "Suc (lengtht t') = n", simp)
 apply (drule mp)
  apply (rule_tac x="s'a" in exI, simp)
 apply (drule mp)
  apply (rule_tac x="t'" in exI, simp)
 apply (simp)
 apply (force)  (* contradict *)
done

(*** rest_setF (equal) ***)

lemma Parallel_rest_setF:
   "[| failures P1 M1 .|. n = failures P2 M2 .|. n ;
       failures Q1 M1 .|. n = failures Q2 M2 .|. n  |]
    ==> failures (P1 |[X]| Q1) M1 .|. n = failures (P2 |[X]| Q2) M2 .|. n"
apply (rule order_antisym)
by (simp_all add: Parallel_rest_setF_sub)

(*** distF lemma ***)

lemma Parallel_distF:
"PQs = {(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)}
 ==> (EX PQ. PQ:PQs & 
             distance(failures (P1 |[X]| Q1) M1, failures (P2 |[X]| Q2) M2)
          <= distance((fst PQ), (snd PQ)))"
apply (simp only: to_distance_rs)
apply (rule rest_to_dist_pair)
by (auto intro: Parallel_rest_setF)

(*** map_alpha F lemma ***)

lemma map_alpha_failures_Parallel_lm:
  "[| distance (failures P1 M1, failures P2 M2) <= alpha * distance (x1, x2) ;
      distance (failures Q1 M1, failures Q2 M2) <= alpha * distance (x1, x2) |]
    ==> distance (failures (P1 |[X]| Q1) M1, failures (P2 |[X]| Q2) M2)
     <= alpha * distance (x1, x2)"
apply (insert Parallel_distF
       [of "{(failures P1 M1, failures P2 M2), 
             (failures Q1 M1, failures Q2 M2)}" P1 M1 P2 M2 Q1 Q2 X])
by (auto)

(*** map_alpha ***)

lemma map_alpha_failures_Parallel:
 "[| map_alpha (failures P) alpha ; map_alpha (failures Q) alpha |]
  ==> map_alpha (failures (P |[X]| Q)) alpha"
apply (simp add: map_alpha_def)
apply (intro allI)
apply (erule conjE)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="y" in spec)
by (simp add: map_alpha_failures_Parallel_lm)

(*** non_expanding ***)

lemma non_expanding_failures_Parallel:
 "[| non_expanding (failures P) ; non_expanding (failures Q) |]
  ==> non_expanding (failures (P|[X]| Q))"
by (simp add: non_expanding_def map_alpha_failures_Parallel)

(*** contraction_alpha ***)

lemma contraction_alpha_failures_Parallel:
 "[| contraction_alpha (failures P) alpha ; 
     contraction_alpha (failures Q) alpha |]
  ==> contraction_alpha (failures (P |[X]| Q)) alpha"
by (simp add: contraction_alpha_def map_alpha_failures_Parallel)

(*--------------------------------*
 |            Hiding              |
 *--------------------------------*)

(* cms rules for Hiding is not necessary 
   because processes are guarded. *)

(*--------------------------------*
 |           Renaming             |
 *--------------------------------*)

(*** rest_setF (subset) ***)

lemma Renaming_rest_setF_sub:
   "failures P M1 .|. n <= failures Q M2 .|. n
    ==> failures (P [[r]]) M1 .|. n <= failures (Q [[r]]) M2 .|. n"
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (simp add: in_rest_setF)
apply (simp add: in_failures)
apply (elim conjE exE)

apply (rule_tac x="sa" in exI)
apply (drule_tac x="sa" in spec)
apply (drule_tac x="[[r]]inv X" in spec)
apply (simp)

apply (erule disjE)
apply (simp add: ren_tr_lengtht)

apply (elim conjE exE)
apply (simp add: ren_tr_lengtht)
apply (simp add: ren_tr_appt_decompo_right)
apply (elim conjE exE, simp)
by (fast)

(*** rest_setF (equal) ***)

lemma Renaming_rest_setF:
   "failures P M1 .|. n = failures Q M2 .|. n
    ==> failures (P [[r]]) M1 .|. n = failures (Q [[r]]) M2 .|. n"
apply (rule order_antisym)
by (simp_all add: Renaming_rest_setF_sub)

(*** distF lemma ***)

lemma Renaming_distF:
     "distance(failures (P [[r]]) M1, failures (Q [[r]]) M2) <= 
      distance(failures P M1, failures Q M2)"
apply (simp only: to_distance_rs)
apply (rule rest_distance_subset)
by (auto intro: Renaming_rest_setF)

(*** map_alphaT lemma ***)

lemma map_alpha_failures_Renaming_lm:
  "distance(failures P M1, failures Q M2) <= alpha * distance (x1, x2)
    ==> distance(failures (P [[r]]) M1, failures (Q [[r]]) M2)
     <= alpha * distance(x1, x2)"
apply (insert Renaming_distF[of P r M1 Q M2])
by (simp)

(*** map_alpha ***)

lemma map_alpha_failures_Renaming:
 "map_alpha (failures P) alpha
  ==> map_alpha (failures (P [[r]])) alpha"
apply (simp add: map_alpha_def)
apply (intro allI)
apply (erule conjE)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
by (simp add: map_alpha_failures_Renaming_lm)

(*** non_expanding ***)

lemma non_expanding_failures_Renaming:
 "non_expanding (failures P)
  ==> non_expanding (failures (P [[r]]))"
by (simp add: non_expanding_def map_alpha_failures_Renaming)

(*** contraction_alpha ***)

lemma contraction_alpha_failures_Renaming:
 "contraction_alpha (failures P) alpha
  ==> contraction_alpha (failures (P [[r]])) alpha"
by (simp add: contraction_alpha_def map_alpha_failures_Renaming)

(*--------------------------------*
 |           Seq_compo            |
 *--------------------------------*)

(*** rest_setF (subset) ***)

lemma Seq_compo_rest_setF_sub:
   "[| traces P1 (fstF o M1) .|. n <= traces P2 (fstF o M2) .|. n ;
       failures P1 M1 .|. n <= failures P2 M2 .|. n ;
       failures Q1 M1 .|. n <= failures Q2 M2 .|. n  |]
    ==> failures (P1 ;; Q1) M1 .|. n <= failures (P2 ;; Q2) M2 .|. n"
apply (simp add: subsetF_iff)
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_rest_setF)
apply (simp add: in_rest_domT)
apply (simp add: in_failures)
apply (elim conjE exE disjE)
apply (simp_all)

 (* case 1 *)
 apply (rule disjI2)
 apply (rule_tac x="sa" in exI)
 apply (rule_tac x="t" in exI)
 apply (simp)

 (* case 2 *)
 apply (rule disjI2)
 apply (rule_tac x="sa" in exI)
 apply (rule_tac x="t" in exI)
 apply (simp)
 apply (drule_tac x=" sa ^^^ <Tick>" in spec)
 apply (simp)

 apply (insert trace_last_nil_or_unnil)
 apply (rotate_tac -1)
 apply (drule_tac x="t" in spec)
 apply (erule disjE, simp)
  apply (rotate_tac 2)
  apply (drule sym)
  apply (simp)

  apply (elim conjE exE, simp)
  apply (simp add: appt_assoc_sym)
  apply (rotate_tac 1)
  apply (drule_tac x="sb ^^^ <Tick>" in spec)
  apply (drule_tac x="X" in spec, simp)
  apply (elim conjE)

  apply (case_tac "Suc (lengtht sb) < n", simp)
  apply (case_tac "Suc (lengtht sb) = n", simp)
  apply (drule mp, force)
  apply (simp)
  apply (force)
done

(*** rest_setF (equal) ***)

lemma Seq_compo_rest_setF:
   "[| traces P1 (fstF o M1) .|. n = traces P2 (fstF o M2) .|. n ;
       failures P1 M1 .|. n = failures P2 M2 .|. n ;
       failures Q1 M1 .|. n = failures Q2 M2 .|. n  |]
    ==> failures (P1 ;; Q1) M1 .|. n = failures (P2 ;; Q2) M2 .|. n"
apply (rule order_antisym)
by (simp_all add: Seq_compo_rest_setF_sub)

(*** distF lemma ***)

lemma Seq_compo_distF:
"[| PQTs = {(traces P1 (fstF o M1), traces P2 (fstF o M2))} ;
    PQFs = {(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)} |]
 ==> (EX PQ. PQ:PQTs & 
             distance(failures (P1 ;; Q1) M1, failures (P2 ;; Q2) M2)
          <= distance((fst PQ), (snd PQ))) |
     (EX PQ. PQ:PQFs & 
             distance(failures (P1 ;; Q1) M1, failures (P2 ;; Q2) M2)
          <= distance((fst PQ), (snd PQ)))"
apply (simp only: to_distance_rs)
apply (rule rest_to_dist_pair_two)
by (auto intro: Seq_compo_rest_setF)

(*** map_alpha F lemma ***)

lemma map_alpha_failures_Seq_compo_lm:
  "[| distance (traces P1 (fstF o M1), traces P2 (fstF o M2)) 
      <= alpha * distance (x1, x2) ;
      distance (failures P1 M1, failures P2 M2) <= alpha * distance (x1, x2) ;
      distance (failures Q1 M1, failures Q2 M2) <= alpha * distance (x1, x2) |]
    ==> distance (failures (P1 ;; Q1) M1, failures (P2 ;; Q2) M2)
     <= alpha * distance (x1, x2)"
apply (insert Seq_compo_distF
       [of "{(traces P1 (fstF o M1), traces P2 (fstF o M2))}" P1 M1 P2 M2
           "{(failures P1 M1, failures P2 M2), 
             (failures Q1 M1, failures Q2 M2)}" Q1 Q2])
by (auto)

(*** map_alpha ***)

lemma map_alpha_failures_Seq_compo:
 "[| map_alpha (%M. traces P (fstF o M)) alpha ; 
     map_alpha (failures P) alpha ; map_alpha (failures Q) alpha |]
  ==> map_alpha (failures (P ;; Q)) alpha"
apply (simp add: map_alpha_def)
apply (intro allI)
apply (erule conjE)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="y" in spec)
by (simp add: map_alpha_failures_Seq_compo_lm)

(*** non_expanding ***)

lemma non_expanding_failures_Seq_compo:
 "[| non_expanding (%M. traces P (fstF o M)) ;
     non_expanding (failures P) ; non_expanding (failures Q) |]
  ==> non_expanding (failures (P ;; Q))"
by (simp add: non_expanding_def map_alpha_failures_Seq_compo)

(*** contraction_alpha ***)

lemma contraction_alpha_failures_Seq_compo:
 "[| contraction_alpha (%M. traces P (fstF o M)) alpha ;
     contraction_alpha (failures P) alpha ; 
     contraction_alpha (failures Q) alpha|]
  ==> contraction_alpha (failures (P ;; Q)) alpha"
by (simp add: contraction_alpha_def map_alpha_failures_Seq_compo)

(*--------------------------------*
 |       Seq_compo  (gSKIP)       |
 *--------------------------------*)

(*** rest_setF (subset) ***)

lemma gSKIP_Seq_compo_rest_setF_sub:
   "[| traces P1 (fstF o M1) .|. (Suc n) <= traces P2 (fstF o M2) .|. (Suc n) ;
       failures P1 M1 .|. (Suc n) <= failures P2 M2 .|. (Suc n) ;
       failures Q1 M1 .|. n <= failures Q2 M2 .|. n ;
       <Tick> ~:t traces P1 (fstF o M1) ;
       <Tick> ~:t traces P2 (fstF o M2) |]
    ==> failures (P1 ;; Q1) M1 .|. (Suc n) <= failures (P2 ;; Q2) M2 .|. (Suc n)"
apply (simp add: subsetF_iff)
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_rest_setF)
apply (simp add: in_rest_domT)
apply (simp add: in_failures)
apply (elim conjE exE disjE)
apply (simp_all)

 (* case 1 *)
 apply (insert trace_last_nil_or_unnil)
 apply (rotate_tac -1)
 apply (drule_tac x="sa" in spec)
 apply (erule disjE)
  apply (simp add: gSKIP_to_Tick_notin_traces)   (* sa = []t *)

  apply (rule disjI2)                            (* sa ~= []t *)
  apply (elim conjE exE, simp)
  apply (rule_tac x="(sb ^^^ <a>)" in exI)
  apply (rule_tac x="t" in exI)
  apply (simp)

 (* case 2 *)
 apply (rotate_tac -1)
 apply (drule_tac x="t" in spec)
 apply (erule disjE)   
  apply (simp)           (* t = []t *)
  apply (rotate_tac 5)
  apply (drule sym)
  apply (simp)           (* contradict noTick *)

  apply (rule disjI2)    (* t ~= []t *)
  apply (elim conjE exE, simp)
  apply (simp add: appt_assoc_sym)
  apply (rule_tac x="sa" in exI)
  apply (rule_tac x="sb ^^^ <Tick>" in exI)
  apply (simp add: appt_assoc)

  apply (insert trace_last_nil_or_unnil)
  apply (rotate_tac -1)
  apply (drule_tac x="sa" in spec)
  apply (erule disjE)
   apply (simp add: gSKIP_to_Tick_notin_traces)   (* sa = []t *)
   apply (elim conjE exE, simp)
                                                  (* i.e. lengtht sb < n *)
   apply (rotate_tac 2)
   apply (drule_tac x="sb ^^^ <Tick>" in spec)
   apply (drule_tac x="X" in spec)
   apply (drule mp)
    apply (simp)
    apply (case_tac "Suc (lengtht sb) < n", simp)
    apply (case_tac "Suc (lengtht sb) = n", fast)
    apply (force)
   apply (simp)
done

(*** rest_setF (equal) ***)

lemma gSKIP_Seq_compo_rest_setF:
   "[| traces P1 (fstF o M1) .|. (Suc n) = traces P2 (fstF o M2) .|. (Suc n) ;
       failures P1 M1 .|. (Suc n) = failures P2 M2 .|. (Suc n) ;
       failures Q1 M1 .|. n = failures Q2 M2 .|. n ;
       <Tick> ~:t traces P1 (fstF o M1) ;
       <Tick> ~:t traces P2 (fstF o M2) |]
    ==> failures (P1 ;; Q1) M1 .|. (Suc n) = failures (P2 ;; Q2) M2 .|. (Suc n)"
apply (rule order_antisym)
by (simp_all add: gSKIP_Seq_compo_rest_setF_sub)

(*** map_alpha F lemma ***)

lemma gSKIP_map_alpha_failures_Seq_compo_lm:
  "[| distance (traces P1 (fstF o M1), traces P2 (fstF o M2)) * 2 <= (1/2)^n ;
      distance (failures P1 M1, failures P2 M2) * 2 <= (1/2)^n ;
      distance (failures Q1 M1, failures Q2 M2) <= (1/2)^n ;
       <Tick> ~:t traces P1 (fstF o M1);
       <Tick> ~:t traces P2 (fstF o M2) |]
    ==> distance (failures (P1 ;; Q1) M1, failures (P2 ;; Q2) M2) * 2
     <= (1/2)^n"
apply (insert gSKIP_Seq_compo_rest_setF[of P1 M1 n P2 M2 Q1 Q2])
apply (simp only: to_distance_rs)
apply (simp add: distance_rs_le_1)
done

(*** map_alpha ***)

lemma gSKIP_contraction_half_failures_Seq_compo:
 "[| contraction_alpha (%M. traces P (fstF o M)) (1/2) ;
     contraction_alpha (failures P) (1/2) ; non_expanding (failures Q) ;
     gSKIP P |]
  ==> contraction_alpha (failures (P ;; Q)) (1/2)"
apply (simp add: contraction_alpha_def non_expanding_def map_alpha_def)
apply (intro allI)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="y" in spec)

apply (case_tac "x = y", simp)
apply (simp only: to_distance_rs)
apply (simp add: distance_iff)
apply (insert gSKIP_to_Tick_notin_traces)
apply (frule_tac x="P" in spec)
apply (drule_tac x="P" in spec)
apply (drule_tac x="fstF o x" in spec)
apply (drule_tac x="fstF o y" in spec)
apply (fold to_distance_rs)
apply (simp add: gSKIP_map_alpha_failures_Seq_compo_lm)
done

(*--------------------------------*
 |          Depth_rest            |
 *--------------------------------*)

(*** rest_setF (equal) ***)

lemma Depth_rest_rest_setF:
   "failures P M1 .|. n = failures Q M2 .|. n
    ==> failures (P |. m) M1 .|. n = failures (Q |. m) M2 .|. n"
apply (simp add: failures.simps)
apply (simp add: min_rs)
apply (rule rest_equal_preserve)
apply (simp)
apply (simp add: min_def)
done

(*** distF lemma ***)

lemma Depth_rest_distF:
     "distance(failures (P |. m) M1, failures (Q |. m) M2) <= 
      distance(failures P M1, failures Q M2)"
apply (simp add: to_distance_rs)
apply (rule rest_distance_subset)
by (auto intro: Depth_rest_rest_setF)

(*** map_alphaT lemma ***)

lemma map_alpha_failures_Depth_rest_lm:
  "distance(failures P M1, failures Q M2) <= alpha * distance (x1, x2)
    ==> distance(failures (P |. m) M1, failures (Q |. m) M2)
     <= alpha * distance(x1, x2)"
apply (insert Depth_rest_distF[of P m M1 Q M2])
by (simp)

(*** map_alpha ***)

lemma map_alpha_failures_Depth_rest:
 "map_alpha (failures P) alpha
  ==> map_alpha (failures (P |. n)) alpha"
apply (simp add: map_alpha_def)
apply (intro allI)
apply (erule conjE)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
by (simp add: map_alpha_failures_Depth_rest_lm)

(*** non_expanding ***)

lemma non_expanding_failures_Depth_rest:
 "non_expanding (failures P)
  ==> non_expanding (failures (P |. n))"
by (simp add: non_expanding_def map_alpha_failures_Depth_rest)

(*** contraction_alpha ***)

lemma contraction_alpha_failures_Depth_rest:
 "contraction_alpha (failures P) alpha
  ==> contraction_alpha (failures (P |. n)) alpha"
by (simp add: contraction_alpha_def map_alpha_failures_Depth_rest)

(*--------------------------------*
 |            variable            |
 *--------------------------------*)

(*** non_expanding ***)

lemma continuous_failures_variable_lm:
    "non_expanding (sndF o (%M. M p))"
apply (rule compo_non_expand)
apply (simp add: non_expanding_sndF)
apply (simp add: non_expanding_prod_variable)
done

lemma non_expanding_failures_variable: 
   "non_expanding (failures ($p))"
apply (simp add: failures_iff)
apply (simp add: continuous_failures_variable_lm[simplified comp_def])
done

(*--------------------------------*
 |            Procfun             |
 *--------------------------------*)

(*****************************************************************
 |                         non_expanding                         |
 *****************************************************************)

lemma non_expanding_failures_lm:
  "noHide P --> non_expanding (failures P)"
apply (induct_tac P)
apply (simp add: non_expanding_failures_STOP)
apply (simp add: non_expanding_failures_SKIP)
apply (simp add: non_expanding_failures_DIV)
apply (simp add: non_expanding_failures_Act_prefix)
apply (simp add: non_expanding_failures_Ext_pre_choice)
apply (simp add: non_expanding_failures_Ext_choice non_expanding_traces_fstF)
apply (simp add: non_expanding_failures_Int_choice)
apply (simp add: non_expanding_failures_Rep_int_choice)
apply (simp add: non_expanding_failures_IF)
apply (simp add: non_expanding_failures_Parallel)

(* hiding --> const *)
apply (intro impI)
apply (subgoal_tac "EX F. (failures (x1 -- x2) = (%M. F))")   (* 2012 *)
apply (erule exE)
apply (simp)
apply (simp add: non_expanding_Constant)
apply (rule failures_noPN_Constant)
apply (simp)

apply (simp add: non_expanding_failures_Renaming)
apply (simp add: non_expanding_failures_Seq_compo non_expanding_traces_fstF)

(* Depth_res *)
apply (simp add: non_expanding_failures_Depth_rest)
apply (simp add: failures_iff)
apply (simp add: zero_rs_setF)
apply (simp add: non_expanding_Constant)

apply (simp add: non_expanding_failures_variable)
done

lemma non_expanding_failures: 
  "noHide P ==> non_expanding (failures P)"
by (simp add: non_expanding_failures_lm)

(*=============================================================*
 |                          [[P]]Ff                            |
 *=============================================================*)

lemma non_expanding_semFf:
  "noHide P ==> non_expanding ([[P]]Ff)"
apply (simp add: semFf_def)
apply (simp add: non_expanding_domF_decompo)
apply (simp add: non_expanding_traces_fstF)
apply (simp add: non_expanding_failures)
done

(*=============================================================*
 |                         [[P]]Ffun                           |
 *=============================================================*)

lemma non_expanding_semFfun: 
  "noHidefun Pf ==> non_expanding ([[Pf]]Ffun)"
apply (simp add: semFfun_def)
apply (simp add: prod_non_expand)
apply (simp add: proj_fun_def comp_def)
apply (simp add: noHidefun_def)
apply (simp add: non_expanding_semFf)
done

(*****************************************************************
 |                         contraction                           |
 *****************************************************************)

lemma contraction_alpha_failures_lm: 
  "guarded P --> contraction_alpha (failures P) (1/2)"
apply (induct_tac P)
apply (simp add: contraction_alpha_failures_STOP)
apply (simp add: contraction_alpha_failures_SKIP)
apply (simp add: contraction_alpha_failures_DIV)
apply (simp add: contraction_half_failures_Act_prefix
                 non_expanding_failures)
apply (simp add: contraction_half_failures_Ext_pre_choice
                 non_expanding_failures)
apply (simp add: contraction_alpha_failures_Ext_choice
                 contraction_alpha_traces_fstF)
apply (simp add: contraction_alpha_failures_Int_choice)
apply (simp add: contraction_alpha_failures_Rep_int_choice)
apply (simp add: contraction_alpha_failures_Rep_int_choice)
apply (simp add: contraction_alpha_failures_IF)
apply (simp add: contraction_alpha_failures_Parallel)

(* hiding --> const *)
apply (intro impI)
apply (subgoal_tac "EX F. (failures (x1 -- x2) = (%M. F))")  (* 2012 *)
apply (erule exE)
apply (simp add: contraction_alpha_Constant)
apply (rule failures_noPN_Constant)
apply (simp)

apply (simp add: contraction_alpha_failures_Renaming)

(* Seq_compo *)
apply (simp)
apply (intro conjI impI)
apply (simp add: gSKIP_contraction_half_failures_Seq_compo
                 non_expanding_failures contraction_alpha_traces_fstF)
apply (simp add: contraction_alpha_failures_Seq_compo
                 contraction_alpha_traces_fstF)

(* Depth_res *)
apply (simp add: contraction_alpha_failures_Depth_rest)
apply (simp add: failures_iff)
apply (simp add: zero_rs_setF)
apply (simp add: contraction_alpha_Constant)

apply (simp add: non_expanding_failures_variable)
done

lemma contraction_alpha_failures: 
  "guarded P ==> contraction_alpha (failures P) (1/2)"
apply (simp add: contraction_alpha_failures_lm)
done

(*=============================================================*
 |                          [[P]]Ff                            |
 *=============================================================*)

lemma contraction_alpha_semFf:
  "guarded P ==> contraction_alpha ([[P]]Ff) (1/2)"
apply (simp add: semFf_def)
apply (simp add: contraction_alpha_domF_decompo)
apply (simp add: contraction_alpha_traces_fstF)
apply (simp add: contraction_alpha_failures)
done

(*=============================================================*
 |                         [[P]]Ffun                           |
 *=============================================================*)

lemma contraction_alpha_semFfun: 
  "guardedfun Pf ==> contraction_alpha ([[Pf]]Ffun) (1/2)"
apply (simp add: semFfun_def)
apply (simp add: prod_contra_alpha)
apply (simp add: proj_fun_def comp_def)
apply (simp add: guardedfun_def)
apply (simp add: contraction_alpha_semFf)
done

(*=============================================================*
 |                        contraction                          |
 *=============================================================*)

lemma contraction_semFfun: 
  "guardedfun Pf ==> contraction ([[Pf]]Ffun)"
apply (simp add: contraction_def)
apply (rule_tac x="1/2" in exI)
apply (simp add:contraction_alpha_semFfun)
done

end
