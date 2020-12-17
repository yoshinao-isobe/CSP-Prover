           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Trace_hide
imports Prefix
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite (notick | t = <>)                  *)
(*                                                                     *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*****************************************************************

         1. 
         2. 
         3. 
         4. 

 *****************************************************************)


(* Isablle 2005

consts
  hidex :: "'a set => ('a trace * 'a trace) set"

inductive "hidex X"
intros
hidex_nil:
  "(<>, <>) : hidex X"

hidex_Tick:
  "(<Tick>, <Tick>) : hidex X"

hidex_in: 
  "[| (s, t) : hidex X ; a : X |]
   ==> (<Ev a> ^^^ s, t) : hidex X"

hidex_notin: 
  "[| (s, t) : hidex X ; a ~: X |]
   ==> (<Ev a> ^^^ s, <Ev a> ^^^ t) : hidex X"
*)

inductive_set
  hidex :: "'a set => ('a trace * 'a trace) set"
  for X :: "'a set"

where
hidex_nil:
  "(<>, <>) : hidex X" |

hidex_Tick:
  "(<Tick>, <Tick>) : hidex X" |

hidex_in: 
  "[| (s, t) : hidex X ; a : X |]
   ==> (<Ev a> ^^^ s, t) : hidex X" |

hidex_notin: 
  "[| (s, t) : hidex X ; a ~: X |]
   ==> (<Ev a> ^^^ s, <Ev a> ^^^ t) : hidex X"

definition
  hide_tr :: "'a trace => 'a set => 'a trace"  ("_ --tr _" [84,85] 84)
  where
  hide_tr_def : 
    "s --tr X == THE t. (s, t) : hidex X"

definition
  rest_tr :: "'a trace => 'a set => 'a trace"  ("_ rest-tr _" [84,85] 84)
  where
  rest_tr_def : 
    "s rest-tr X == s --tr (- X)"

(*************************************************************
                       THE hidex 
 *************************************************************)

(*** exists ***)

lemma hidex_exists_lm: 
  "ALL X s. (EX t. (s, t) : hidex X)"
apply (rule allI)
apply (rule allI)
apply (induct_tac s rule: induct_trace)

apply (simp_all)
apply (rule_tac x="<>" in exI, simp add: hidex.intros)
apply (rule_tac x="<Tick>" in exI, simp add: hidex.intros)

apply (elim exE)
apply (case_tac "a : X")
apply (rule_tac x="t" in exI, simp add: hidex.intros)
apply (rule_tac x="<Ev a> ^^^ t" in exI, simp add: hidex.intros)
done

(*** exists !! ***)

lemma hidex_exists: 
  "EX t. (s, t) : hidex X"
by (simp add: hidex_exists_lm)

(*** unique ***)

lemma hidex_unique_lm: 
  "ALL X s t u. ((s, t) : hidex X & (s, u) : hidex X)
    --> t = u"
apply (rule allI)
apply (rule allI)
apply (induct_tac s rule: induct_trace)

(* <> *)
apply (intro allI impI)
apply (erule conjE)
apply (erule hidex.cases, simp_all)    (* hidex.elims --2007--> hidex.cases *)
apply (erule hidex.cases, simp_all)

(* <Tick> *)
apply (intro allI impI)
apply (erule conjE)
apply (erule hidex.cases, simp_all)    (* hidex.elims --2007--> hidex.cases *)
apply (erule hidex.cases, simp_all)


(* step *)
apply (intro allI impI)
apply (erule conjE)
apply (case_tac "a : X")
 apply (erule hidex.cases, simp_all)+    (* hidex.elims --2007--> hidex.cases *)
done

lemma hidex_unique: 
  "[| (s, t) : hidex X ; (s, u) : hidex X |]
   ==> t = u"
apply (insert hidex_unique_lm)
apply (drule_tac x="X" in spec)
apply (drule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
apply (drule_tac x="u" in spec)
apply (simp)
done

(*************************************************************
                       THE hidex 
 *************************************************************)

lemma hidex_to_hide_tr : 
    "(s, t) : hidex X = (t = s --tr X)"
apply (simp add: hide_tr_def)
apply (rule iffI)
apply (rule sym)
apply (rule the_equality)
apply (simp)
apply (simp add: hidex_unique)

apply (simp)
apply (insert hidex_exists[of s X])
apply (erule exE)
apply (rule theI[of "(%x. (s, x) : hidex X)"])
apply (simp)
apply (simp add: hidex_unique)
done

lemma hide_tr_to_hidex : 
    "(s --tr X = t) = ((s, t) : hidex X)"
apply (simp add: hidex_to_hide_tr)
by (fast)

lemma hide_tr_to_hidex_sym : 
    "(t = s --tr X) = ((s, t) : hidex X)"
by (simp add: hidex_to_hide_tr)

lemmas hide_tr_iff = hide_tr_to_hidex hide_tr_to_hidex_sym

(*************************************************************
                         hide_tr
 *************************************************************)

(*------------------*
 |      intros      |
 *------------------*)

lemma hide_tr_nil[simp] : "<> --tr X = <>"
apply (simp add: hide_tr_to_hidex)
by (simp add: hidex.intros)

lemma hide_tr_Tick[simp] : "<Tick> --tr X = <Tick>"
apply (simp add: hide_tr_to_hidex)
by (simp add: hidex.intros)

lemma hide_tr_in_lm : 
  "[| a : X ;  t = s --tr X |]
   ==> (<Ev a> ^^^ s) --tr X = t"
apply (simp add: hide_tr_to_hidex_sym)
apply (simp add: hide_tr_to_hidex)
apply (simp add: hidex.intros)
done

lemma hide_tr_in[simp] : 
  "a : X ==> (<Ev a> ^^^ s) --tr X = s --tr X"
by (simp add: hide_tr_in_lm)

lemma hide_tr_in_one[simp] : 
  "a : X ==> <Ev a> --tr X = <>"
apply (insert hide_tr_in[of a X "<>"])
by (simp)

lemma hide_tr_notin_lm : 
  "[| a ~: X ;  t = s --tr X |]
   ==> (<Ev a> ^^^ s) --tr X = <Ev a> ^^^ t"
apply (simp add: hide_tr_to_hidex_sym)
apply (simp add: hide_tr_to_hidex)
apply (simp add: hidex.intros)
done

lemma hide_tr_notin_appt[simp] : 
  "a ~: X ==> (<Ev a> ^^^ s) --tr X = <Ev a> ^^^ (s --tr X)"
by (simp add: hide_tr_notin_lm)

lemma hide_tr_notin[simp] : 
  "a ~: X ==> <Ev a> --tr X = <Ev a>"
apply (insert hide_tr_notin_appt[of a X "<>"])
by (simp)

(*------------------*
 |      elims       |
 *------------------*)

lemma hide_tr_elims_lm:
  "[| s --tr X = t ;
      (( s = <> & t = <> ) --> P) ;
      (( s = <Tick> & t = <Tick> ) --> P) ;
      ( ALL a s'.
        ((s = <Ev a> ^^^ s' & s' --tr X = t & a : X )
         --> P)) ;
      ( ALL a s' t'.
        ((s = <Ev a> ^^^ s' & t = <Ev a> ^^^ t' & s' --tr X = t' & a ~: X )
         --> P)) |]
   ==> P"
apply (simp add: hide_tr_iff)
apply (erule hidex.cases)
by (auto)

lemma hide_tr_elims:
  "[| s --tr X = t; 
      [| s = <> ; t = <> |] ==> P; 
      [| s = <Tick> ; t = <Tick> |] ==> P; 
   !!a s'.
      [| s = <Ev a> ^^^ s' ; s' --tr X = t; a : X |]
      ==> P;
   !!a s' t'.
      [| s = <Ev a> ^^^ s' ; t = <Ev a> ^^^ t' ; s' --tr X = t' ; a ~: X |]
      ==> P |]
   ==> P"
apply (rule hide_tr_elims_lm[of s X t])
apply (simp_all)
(* for Isabelel 2013
by (force)+
*)
done

(*************************************************************
        a new event is not introduced by HIDE (trace)
 *************************************************************)

lemma hide_tr_in_event[simp]:
  "e : sett (s --tr X) = (e ~: Ev ` X & e : sett s)"
apply (induct_tac s rule: induct_trace)
apply (simp)
apply (simp)
apply (force)

apply (simp)
apply (case_tac "a : X")
apply (simp)
apply (rule iffI, simp, force)
apply (rule iffI, force, force)
done

(*** notick ***)

lemma hide_tr_noTick[simp]: "noTick (s --tr X) = noTick s"
apply (simp add: noTick_def)
by (auto)

(*************************************************************
                  appended traces in hide
 *************************************************************)

lemma hide_tr_appt_noTick_lm:
  "ALL X s e t. noTick s --> ((s ^^^ t) --tr X = (s --tr X) ^^^ (t --tr X))"
apply (rule allI)
apply (rule allI)
apply (induct_tac s rule: induct_trace)
apply (simp_all)

apply (intro allI impI, simp)
apply (case_tac "a : X")
by (simp_all add: appt_assoc)

(*** simp ***)

lemma hide_tr_appt[simp]:
  "noTick s | t = <> ==> (s ^^^ t) --tr X = (s --tr X) ^^^ (t --tr X)"
apply (erule disjE)
apply (simp add: hide_tr_appt_noTick_lm)
by (simp)

(*************************************************************
                 decompose traces in hide
 *************************************************************)

lemma hide_tr_decompo_only_if_lm:
  "ALL X u s t.
      ((noTick s | t = <>) & u --tr X = s ^^^ t)
      --> (EX s' t'. (noTick s' | t' = <>) &
                     u = s' ^^^ t' &
                     s = s' --tr X & t = t' --tr X) "
apply (rule allI)
apply (rule allI)
apply (induct_tac u rule: induct_trace)
apply (intro allI impI)
apply (rule_tac x="<>" in exI)
apply (rule_tac x="<>" in exI)
apply (force)

apply (intro allI impI)
apply (elim conjE disjE)
apply (simp)
apply (elim conjE disjE)
apply (rule_tac x="<Tick>" in exI)
apply (rule_tac x="<>" in exI)
apply (simp)
apply (rule_tac x="<>" in exI)
apply (rule_tac x="<Tick>" in exI)
apply (simp)
apply (rule_tac x="<Tick>" in exI)
apply (rule_tac x="<>" in exI)
apply (drule sym)
apply (simp)

apply (intro allI impI)
apply (erule conjE)
apply (erule hide_tr_elims)
apply (simp_all)

 (* a : X *)
 apply (drule_tac x="sa" in spec)
 apply (drule_tac x="t" in spec)
 apply (simp)
 apply (elim conjE exE)
 apply (simp)

 apply (rule_tac x="<Ev aa> ^^^ s'a" in exI)
 apply (rule_tac x="t'" in exI)
 apply (erule disjE)
 apply (simp add: appt_assoc)
 apply (erule disjE)
 apply (simp add: appt_assoc)
 apply (simp)

 (* a ~: X *)
 apply (insert trace_nil_or_Tick_or_Ev)
 apply (rotate_tac -1)
 apply (drule_tac x="sa" in spec)
 apply (rotate_tac -1)

  (* <> *)
  apply (erule disjE)
  apply (rule_tac x="<>" in exI, simp)

  (* <Tick> *)
  apply (rotate_tac -1)
  apply (erule disjE)
  apply (simp)

  (* <Ev a> ^^^ ... *)
  apply (elim exE)
  apply (simp add: appt_assoc)

  apply (drule_tac x="sb" in spec)
  apply (drule_tac x="t" in spec)
  apply (simp)
  apply (elim conjE exE)

  apply (rule_tac x="<Ev aa> ^^^ s'a" in exI)
  apply (rule_tac x="t'a" in exI)
  apply (simp add: appt_assoc)
done

lemma hide_tr_decompo_only_if:
  "[| noTick s | t = <> ; u --tr X = s ^^^ t |]
   ==> (EX s' t'. (noTick s' | t' = <>) &
                  u = s' ^^^ t' &
                  s = s' --tr X & t = t' --tr X)"
by (simp add: hide_tr_decompo_only_if_lm)

(* if *)

lemma hide_tr_decompo_if:
  "[| noTick s | t = <> ; 
      (EX s' t'. (noTick s' | t' = <>) &
                  u = s' ^^^ t' &
                  s = s' --tr X & t = t' --tr X) |]
   ==> u --tr X = s ^^^ t"
apply (elim conjE exE)
by (simp)

(*** iff ***)

lemma hide_tr_decompo:
  "noTick s | t = <>
   ==> u --tr X = s ^^^ t
    = (EX s' t'. (noTick s' | t' = <>) &
                  u = s' ^^^ t' &
                  s = s' --tr X & t = t' --tr X)"
apply (rule iffI)
apply (simp add: hide_tr_decompo_only_if)
apply (rule hide_tr_decompo_if)
by (simp_all)

(*************************************************************
                  hide trace prefix_closed
 *************************************************************)

lemma hide_tr_prefix_only_if_lm:
 "ALL X s u. (prefix u (s --tr X)) 
    --> (EX t. u = t --tr X & prefix t s)"
apply (rule allI)
apply (rule allI)
apply (induct_tac s rule: induct_trace)
apply (simp_all)

(* Tick *)
apply (force)

(* <Ev a> ^^^ ... *)
apply (intro allI impI)

 apply (case_tac "a : X")
 apply (drule_tac x="u" in spec, simp)
 apply (elim conjE exE)
 apply (rule_tac x="<Ev a> ^^^ t" in exI, simp)

 (* a ~: X *)
 apply (simp)

  (* u = <> *)
  apply (erule disjE)
  apply (drule_tac x="<>" in spec)
  apply (simp)
  apply (elim conjE exE)
  apply (rule_tac x="<>" in exI)
  apply (simp)

  (* u = <Ev a> ^^^ ... *)
  apply (elim conjE exE)
  apply (drule_tac x="v'" in spec, simp)
  apply (elim conjE exE)
  apply (rule_tac x="<Ev a> ^^^ t" in exI, simp)
done

lemma hide_tr_prefix_only_if:
 "prefix u (s --tr X) ==> (EX t. u = t --tr X & prefix t s)"
by (simp add: hide_tr_prefix_only_if_lm)

(*** if ***)

lemma hide_tr_prefix_if:
 "prefix t s ==> prefix (t --tr X) (s --tr X)"
apply (simp add: prefix_def)
apply (erule exE)
apply (simp)
apply (rule_tac x="u --tr X" in exI)
by (auto)

lemma hide_tr_prefix:
 "prefix u (s --tr X) = (EX t. u = t --tr X & prefix t s)"
apply (rule iffI)
apply (simp add: hide_tr_prefix_only_if)
apply (erule exE)
by (simp add: hide_tr_prefix_if)

(*************************************************************
                  hide + alpha lemma
 *************************************************************)

(* rev <> *)

(* only if *)

lemma hide_tr_nilt_sett_only_if_lm:
  "ALL s. s --tr X = <> --> (sett s <= Ev ` X)"
apply (rule allI)
apply (induct_tac s rule: induct_trace)
apply (simp_all)
apply (intro allI impI)
apply (elim conjE exE)
apply (case_tac "a : X")
by (simp_all)

lemma hide_tr_nilt_sett_only_if:
  "s --tr X = <> ==> (sett s <= Ev ` X)"
by (simp add: hide_tr_nilt_sett_only_if_lm)

(* if *)

lemma hide_tr_nilt_sett_if_lm:
  "ALL s. sett s <= Ev ` X --> s --tr X = <>"
apply (rule allI)
apply (induct_tac s rule: induct_trace)
apply (simp_all)
apply (force)
apply (intro allI impI)
apply (elim conjE)
apply (simp)
apply (case_tac "a : X")
by (auto)

lemma hide_tr_nilt_sett_if:
  "sett s <= Ev ` X ==> s --tr X = <>"
by (simp add: hide_tr_nilt_sett_if_lm)

(* iff *)

lemma hide_tr_nilt_sett:
  "(s --tr X = <>) = (sett s <= Ev ` X)"
apply (rule iffI)
apply (simp add: hide_tr_nilt_sett_only_if)
apply (simp add: hide_tr_nilt_sett_if)
done

(*** sett <= sett ***)

lemma hide_tr_sett_subseteq_sett:
  "X <= Y ==> sett (u --tr Y) <= sett (u --tr X)"
apply (induct_tac u rule: induct_trace)
apply (simp_all)
apply (case_tac "a : X")
apply (simp_all)
apply (case_tac "a ~: Y", fast)
apply (simp)

apply (case_tac "a : Y")
apply (auto)
done

(* rev <Tick> *)

(* only if *)

lemma hide_tr_Tick_sett_only_if_lm:
  "ALL s. s --tr X = <Tick>
    --> (EX s'. s = s' ^^^ <Tick> & sett s' <= Ev ` X & noTick s')"
apply (rule allI)
apply (induct_tac s rule: rev_induct_trace)
apply (simp_all)
apply (rule conjI)

 apply (force)

 apply (intro allI impI)
 apply (elim conjE exE)
 apply (rule_tac x="sa" in exI)
 apply (simp)
 apply (insert event_Tick_or_Ev)
 apply (drule_tac x="e" in spec)
 apply (erule disjE)
 apply (simp add: hide_tr_nilt_sett)

 apply (erule exE)
 apply (case_tac "a : X")
 apply (simp_all)
done

lemma hide_tr_Tick_sett_only_if:
  "s --tr X = <Tick>
    ==> (EX s'. s = s' ^^^ <Tick> & sett s' <= Ev ` X & noTick s')"
by (simp add: hide_tr_Tick_sett_only_if_lm)

(* if *)

lemma hide_tr_Tick_sett_if:
  "sett s <= Ev ` X ==> s --tr X = <>"
by (simp add: hide_tr_nilt_sett)

(* iff *)

lemma hide_tr_Tick_sett:
  "(s --tr X = <Tick>)
   = (EX s'. s = s' ^^^ <Tick> & sett s' <= Ev ` X & noTick s')"
apply (rule iffI)
apply (simp add: hide_tr_Tick_sett_only_if)
apply (elim conjE exE)
apply (simp add: hide_tr_Tick_sett_if)
done

(*--------------------------*
 |       commutativity      |
 *--------------------------*)

lemma hide_tr_commute:
  "(u --tr X) --tr Y = (u --tr Y) --tr X"
apply (induct_tac u rule: induct_trace)
apply (simp_all)
apply (case_tac "a:X")
 apply (case_tac "a:Y")
  apply (simp)
  apply (simp)
 apply (case_tac "a:Y")
  apply (simp)
  apply (simp)
done

(*--------------------------------*
 |   used in Inductive_parallel   |
 *--------------------------------*)

lemma hide_tr_of_hide_tr_subset1:
  "X <= Y ==> (u --tr X) --tr Y = u --tr Y"
apply (induct_tac u rule: induct_trace)
apply (simp_all)
apply (case_tac "a:X")
by (auto)

lemma hide_tr_of_hide_tr_subset2:
  "X <= Y ==> (u --tr Y) --tr X = u --tr Y"
apply (simp add: hide_tr_commute)
apply (simp add: hide_tr_of_hide_tr_subset1)
done

lemmas hide_tr_of_hide_tr_subset = hide_tr_of_hide_tr_subset1
                                   hide_tr_of_hide_tr_subset2

lemma hide_tr_UNIV_lm:
  "((u --tr UNIV = <>) | (u --tr UNIV = <Tick>))"
apply (induct_tac u rule: induct_trace)
by (simp_all)

lemma hide_tr_UNIV:
  "((u --tr UNIV = <>) | (u --tr UNIV = <Tick>))"
by (simp add: hide_tr_UNIV_lm)

(*======================================================*
 |                                                      |
 |                        rest-tr                       |
 |                                                      |
 *======================================================*)

(*------------------*
 |      intros      |
 *------------------*)

lemma rest_tr_nil[simp] : "<> rest-tr X = <>"
by (simp add: rest_tr_def)

lemma rest_tr_Tick[simp] : "<Tick> rest-tr X = <Tick>"
by (simp add: rest_tr_def)

lemma rest_tr_notin[simp] : 
  "a ~: X ==> (<Ev a> ^^^ s) rest-tr X = s rest-tr X"
by (simp add: rest_tr_def)

lemma rest_tr_notin_one[simp] : 
  "a ~: X ==> <Ev a> rest-tr X = <>"
by (simp add: rest_tr_def)

lemma rest_tr_in_appt[simp] : 
  "a : X ==> (<Ev a> ^^^ s) rest-tr X = <Ev a> ^^^ (s rest-tr X)"
by (simp add: rest_tr_def)

lemma rest_tr_in[simp] : 
  "a : X ==> <Ev a> rest-tr X = <Ev a>"
by (simp add: rest_tr_def)

(*------------------*
 |      elims       |
 *------------------*)

lemma rest_tr_elims:
  "[| s rest-tr X = t; 
      [| s = <> ; t = <> |] ==> P; 
      [| s = <Tick> ; t = <Tick> |] ==> P; 
   !!a s'.
      [| s = <Ev a> ^^^ s' ; s' rest-tr X = t; a ~: X |]
      ==> P;
   !!a s' t'.
      [| s = <Ev a> ^^^ s' ; t = <Ev a> ^^^ t' ; s' rest-tr X = t' ; a : X |]
      ==> P |]
   ==> P"
apply (simp add: rest_tr_def)
apply (erule hide_tr_elims)
apply (simp)
apply (simp)
apply (blast)
apply (blast)
done

(*************************************************************
        a new event is not introduced by rest (trace)
 *************************************************************)

lemma rest_tr_in_event[simp]:
  "e : sett (s rest-tr X) = ((e : Ev ` X | e = Tick) & e : sett s)"
apply (simp add: rest_tr_def)
apply (insert event_Tick_or_Ev)
apply (drule_tac x="e" in spec)
apply (auto)
done

lemma rest_tr_subset_event[simp]:
  "sett (s rest-tr X) <= insert Tick (Ev ` X)"
apply (auto)
done
(*** notick ***)

lemma rest_tr_noTick[simp]: "noTick (s rest-tr X) = noTick s"
by (simp add: noTick_def)

(*************************************************************
                  appended traces in rest
 *************************************************************)

lemma rest_tr_appt[simp]:
  "noTick s | t = <> ==> (s ^^^ t) rest-tr X = (s rest-tr X) ^^^ (t rest-tr X)"
apply (simp add: rest_tr_def)
done

(*************************************************************
                 decompose traces in rest
 *************************************************************)

lemma rest_tr_decompo:
  "noTick s | t = <>
   ==> u rest-tr X = s ^^^ t
    = (EX s' t'. (noTick s' | t' = <>) &
                  u = s' ^^^ t' &
                  s = s' rest-tr X & t = t' rest-tr X)"
apply (simp add: rest_tr_def)
apply (simp add: hide_tr_decompo)
done

(*************************************************************
                  rest trace prefix_closed
 *************************************************************)

lemma rest_tr_prefix:
 "prefix u (s rest-tr X) = (EX t. u = t rest-tr X & prefix t s)"
apply (simp add: rest_tr_def)
apply (simp add: hide_tr_prefix)
done

(*************************************************************
                  rest + alpha lemma
 *************************************************************)

(* rev <> *)

lemma rest_tr_nilt_sett:
  "(s rest-tr X = <>) = (sett s Int (insert Tick (Ev ` X)) = {})"
apply (simp add: rest_tr_def)
apply (simp add: hide_tr_nilt_sett)
apply (auto)
apply (insert event_Tick_or_Ev)
apply (drule_tac x="x" in spec)
apply (auto)
done

(*** sett <= sett ***)

lemma rest_tr_sett_subseteq_sett:
  "X <= Y ==> sett (u rest-tr X) <= sett (u rest-tr Y)"
apply (simp add: rest_tr_def)
by (simp add: hide_tr_sett_subseteq_sett)

(* rev <Tick> *)

lemma rest_tr_Tick_sett:
  "(s rest-tr X = <Tick>)
   = (EX s'. s = s' ^^^ <Tick> & (sett s' Int (Ev ` X) = {})
      & noTick s')"
apply (simp add: rest_tr_def)
apply (simp add: hide_tr_Tick_sett)
apply (auto)
apply (rule_tac x="s'" in exI)
apply (auto)
apply (insert event_Tick_or_Ev)
apply (drule_tac x="x" in spec)
apply (auto simp add: noTick_def)
done

(*--------------------------*
 |       commutativity      |
 *--------------------------*)

lemma rest_tr_commute:
  "(u rest-tr X) rest-tr Y = (u rest-tr Y) rest-tr X"
apply (simp add: rest_tr_def)
apply (simp add: hide_tr_commute)
done

(*--------------------------------*
 |   used in Inductive_parallel   |
 *--------------------------------*)

lemma rest_tr_of_rest_tr_subset1:
  "X <= Y ==> (u rest-tr X) rest-tr Y = u rest-tr X"
apply (simp add: rest_tr_def)
apply (rule hide_tr_of_hide_tr_subset)
by (auto)

lemma rest_tr_of_rest_tr_subset2:
  "X <= Y ==> (u rest-tr Y) rest-tr X = u rest-tr X"
apply (simp add: rest_tr_commute)
apply (simp add: rest_tr_of_rest_tr_subset1)
done

lemmas rest_tr_of_rest_tr_subset = rest_tr_of_rest_tr_subset1
                                   rest_tr_of_rest_tr_subset2

lemma rest_tr_empty:
  "((u rest-tr {} = <>) | (u rest-tr {} = <Tick>))"
apply (simp add: rest_tr_def)
apply (simp add: hide_tr_UNIV)
done

(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)

(*  rest_tr decompo *)

lemma Ev_rest_tr_decompo:
  "ALL s X a. (a : X &  s rest-tr X = <Ev a>) --> 
   (EX s1 s2. s = s1 ^^^ <Ev a> ^^^ s2 & noTick s1 & noTick s2 &
    s1 rest-tr X = <> &
    s2 rest-tr X = <> )"
apply (rule)
apply (rule)
apply (induct_tac s rule: induct_trace)
apply (simp_all)
apply (intro allI impI)
apply (elim conjE disjE)
apply (simp)
apply (case_tac "a:X")
 apply (simp)
 apply (rule_tac x="<>" in exI)
 apply (rule_tac x="sa" in exI)
 apply (simp)
 apply (subgoal_tac "noTick(sa rest-tr X)")
 apply (simp (no_asm_use))
 apply (simp)
 apply (simp)

apply (simp)
apply (elim conjE exE)
apply (simp)
apply (rule_tac x="<Ev a> ^^^ s1" in exI)
apply (rule_tac x="s2" in exI)
apply (simp)
apply (simp add: appt_assoc)
done

(* --- hide_tr --- *)

lemma hide_tr_rest_tr_sett[rule_format]:
  "sett s <= insert Tick (Ev ` Y)
   --> ((s --tr X) = (s rest-tr (Y-X)))"
apply (induct_tac s rule: induct_trace)
apply (simp_all)
apply (intro impI)
apply (simp add: image_iff)
apply (case_tac "a:X")
apply (auto)
done

lemma hide_tr_id[rule_format]:
  "(sett s <= insert Tick (Ev ` Y) & X Int Y = {})
   --> ((s --tr X) = s)"
apply (induct_tac s rule: induct_trace)
apply (simp_all)
apply (intro impI)
apply (simp add: image_iff)
apply (case_tac "a:X")
apply (auto)
done


(* --------------------------------------------------- *
                   semantics for pipe
 * --------------------------------------------------- *)

(* hide & rest *)

lemma hide_tr_of_rest_tr_empty1:
  "X Int Y = {} ==> s --tr X rest-tr Y = s rest-tr Y"
apply (simp add: rest_tr_def)
apply (rule hide_tr_of_hide_tr_subset1)
apply (auto)
done

lemma hide_tr_of_rest_tr_empty2:
  "X Int Y = {} ==> s rest-tr X --tr Y = s rest-tr X"
apply (simp add: rest_tr_def)
apply (rule hide_tr_of_hide_tr_subset2)
apply (auto)
done

lemma noTick_hide_tr_of_rest_tr_empty:
  "[| noTick s ; X <= Y |] ==> s rest-tr X --tr Y = <>"
apply (rule hide_tr_Tick_sett_if)
apply (auto)
apply (simp add: image_iff)
apply (force)
apply (simp add: noTick_def)
done

lemma hide_tr_nohiden[rule_format]: 
  "sett s Int Ev ` X = {} --> s --tr X = s"
apply (induct_tac s rule: induct_trace)
apply (simp)
apply (simp)
apply (intro allI impI)
apply (simp add: image_iff)
done

(****************** to add it again ******************)

declare disj_not1 [simp] 

end
