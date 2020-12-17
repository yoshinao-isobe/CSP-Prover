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

theory Trace_par
imports Prefix
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite (notick | t = <>)                  *)
(*                                                                     *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*****************************************************************

         1. s |[X]|list t  : lists  --> list set
         2. s |[X]|tr t   : traces --> trace set
         3. 
         4. 

 *****************************************************************)

(* Isabelle 2005
consts
  parx :: "'a set => ('a trace * 'a trace * 'a trace) set"

inductive "parx X"
intros
parx_nil_nil: 
  "(<>, <>, <>) : parx X"

parx_Tick_Tick: 
  "(<Tick>, <Tick>, <Tick>) : parx X"

parx_Ev_nil: 
  "[| (u, s, <>) : parx X ; a ~: X |]
   ==> (<Ev a> ^^^ u, <Ev a> ^^^ s, <>) : parx X"

parx_nil_Ev: 
  "[| (u, <>, t) : parx X ; a ~: X |]
   ==> (<Ev a> ^^^ u, <>, <Ev a> ^^^ t) : parx X"

parx_Ev_sync: 
  "[| (u, s, t) : parx X ; a : X |]
   ==> (<Ev a> ^^^ u, <Ev a> ^^^ s, <Ev a> ^^^ t) : parx X"

parx_Ev_left: 
  "[| (u, s, t) : parx X ; a ~: X |]
   ==> (<Ev a> ^^^ u, <Ev a> ^^^ s, t) : parx X"

parx_Ev_right: 
  "[| (u, s, t) : parx X ; a ~: X |]
   ==> (<Ev a> ^^^ u, s, <Ev a> ^^^ t) : parx X"
*)


inductive_set
  parx :: "'a set => ('a trace * 'a trace * 'a trace) set"
  for X :: "'a set"

where
parx_nil_nil: 
  "(<>, <>, <>) : parx X" |

parx_Tick_Tick: 
  "(<Tick>, <Tick>, <Tick>) : parx X" |

parx_Ev_nil: 
  "[| (u, s, <>) : parx X ; a ~: X |]
   ==> (<Ev a> ^^^ u, <Ev a> ^^^ s, <>) : parx X" |

parx_nil_Ev: 
  "[| (u, <>, t) : parx X ; a ~: X |]
   ==> (<Ev a> ^^^ u, <>, <Ev a> ^^^ t) : parx X" |

parx_Ev_sync: 
  "[| (u, s, t) : parx X ; a : X |]
   ==> (<Ev a> ^^^ u, <Ev a> ^^^ s, <Ev a> ^^^ t) : parx X" |

parx_Ev_left: 
  "[| (u, s, t) : parx X ; a ~: X |]
   ==> (<Ev a> ^^^ u, <Ev a> ^^^ s, t) : parx X" |

parx_Ev_right: 
  "[| (u, s, t) : parx X ; a ~: X |]
   ==> (<Ev a> ^^^ u, s, <Ev a> ^^^ t) : parx X"

definition
  par_tr :: "'a trace => 'a set => 'a trace => 'a trace set"
                                        ("(_ |[_]|tr _)" [76,0,77] 76)
 where
  par_tr_def : "s |[X]|tr t == {u. (u, s, t) : parx X}"

lemma par_tr_defE: "[| u : s |[X]|tr t ; (u, s, t) : parx X ==> R |] ==> R"
by (simp add: par_tr_def)

(*************************************************************
                 par_tr intros and elims
 *************************************************************)

(*-------------------*
 |      intros       |
 *-------------------*)

lemma par_tr_nil_nil: 
  "<> : <> |[X]|tr <>"
apply (simp add: par_tr_def)
by (simp add: parx.intros)

lemma par_tr_Tick_Tick: 
  "<Tick> : <Tick> |[X]|tr <Tick>"
apply (simp add: par_tr_def)
by (simp add: parx.intros)

lemma par_tr_Ev_nil: 
  "[| u : s |[X]|tr <> ; a ~: X |]
   ==> <Ev a> ^^^ u : (<Ev a> ^^^ s) |[X]|tr <>"
apply (simp add: par_tr_def)
by (simp add: parx.intros)

lemma par_tr_nil_Ev: 
  "[| u : <> |[X]|tr t ; a ~: X |]
   ==> <Ev a> ^^^ u : <> |[X]|tr (<Ev a> ^^^ t)"
apply (simp add: par_tr_def)
by (simp add: parx.intros)

lemma par_tr_Ev_sync: 
  "[| u : s |[X]|tr t ; a : X |]
   ==> <Ev a> ^^^ u : (<Ev a> ^^^ s) |[X]|tr (<Ev a> ^^^ t)"
apply (simp add: par_tr_def)
by (simp add: parx.intros)

lemma par_tr_Ev_left: 
  "[| u : s |[X]|tr t ; a ~: X |]
   ==> <Ev a> ^^^ u : (<Ev a> ^^^ s) |[X]|tr t"
apply (simp add: par_tr_def)
by (simp add: parx.intros)

lemma par_tr_Ev_right: 
  "[| u : s |[X]|tr t ; a ~: X |]
   ==> <Ev a> ^^^ u : s |[X]|tr (<Ev a> ^^^ t)"
apply (simp add: par_tr_def)
by (simp add: parx.intros)

(*** intro rule ***)

lemmas par_tr_intros =
       par_tr_nil_nil
       par_tr_Tick_Tick
       par_tr_Ev_nil
       par_tr_nil_Ev
       par_tr_Ev_sync
       par_tr_Ev_left
       par_tr_Ev_right

(*-------------------*
 |       elims       |
 *-------------------*)

lemma par_tr_elims_lm:
 "[| u : s |[X]|tr t ;
     (u = <> & s = <> & t = <>) --> P ;
     (u = <Tick> & s = <Tick> & t = <Tick>) --> P ;
     ALL a s' u'.
        (u = <Ev a> ^^^ u' & s = <Ev a> ^^^ s' & t = <> &
           u' : s' |[X]|tr <> & a ~: X)
        --> P;
     ALL a t' u'.
        (u = <Ev a> ^^^ u' & s = <> & t = <Ev a> ^^^ t' & 
           u' : <> |[X]|tr t' & a ~: X)
        --> P;
     ALL a s' t' u'.
        (u = <Ev a> ^^^ u' & s = <Ev a> ^^^ s' & t = <Ev a> ^^^ t' &
           u' : s' |[X]|tr t' & a : X)
        --> P;
     ALL a s' u'.
        (u = <Ev a> ^^^ u' & s = <Ev a> ^^^ s' &
           u' : s' |[X]|tr t & a ~: X)
        --> P;
     ALL a t' u'.
        (u = <Ev a> ^^^ u' & t = <Ev a> ^^^ t' & 
           u' : s |[X]|tr t' & a ~: X)
        --> P |]
  ==> P"
apply (simp add: par_tr_def)
apply (erule parx.cases)      (* .elims --> .cases *)
apply (simp_all)
done

(*** elim rule ***)

lemma par_tr_elims:
 "[| u : s |[X]|tr t ;
     [| u = <>; s = <>; t = <> |] ==> P ;
     [| u = <Tick>; s = <Tick>; t = <Tick> |] ==> P ;
     !!a s' u'.
        [| u = <Ev a> ^^^ u'; s = <Ev a> ^^^ s'; t = <> ; 
           u' : s' |[X]|tr <>; a ~: X |]
        ==> P;
     !!a t' u'.
        [| u = <Ev a> ^^^ u' ; s = <> ; t = <Ev a> ^^^ t' ; 
           u' : <> |[X]|tr t'; a ~: X |]
        ==> P;
     !!a s' t' u'.
        [| u = <Ev a> ^^^ u' ; s = <Ev a> ^^^ s' ; t = <Ev a> ^^^ t' ;
           u' : s' |[X]|tr t'; a : X |]
        ==> P;
     !!a s' u'.
        [| u = <Ev a> ^^^ u' ; s = <Ev a> ^^^ s' ; 
           u' : s' |[X]|tr t; a ~: X |]
        ==> P;
     !!a t' u'.
        [| u = <Ev a> ^^^ u' ; t = <Ev a> ^^^ t' ; 
           u' : s |[X]|tr t'; a ~: X |]
        ==> P |]
  ==> P"
apply (rule par_tr_elims_lm[of u s X t])
apply (simp_all)
(* for Isabelle 2013
apply (fast)
apply (fast)
apply (fast)    (* this takes 1 min *)
apply (fast)    (* this takes 1 min *)
apply (fast)    (* this takes 1 min *)
*)
done

(*************************************************************
                 par_tr decomposition
 *************************************************************)

(*-------------------*
 |     par nil       |
 *-------------------*)

(*** par_tr ***)

lemma par_tr_nil_only_if:
  "<> : s |[X]|tr t ==> s = <> & t = <>"
apply (erule par_tr_elims)
by (simp_all)

(*** iff ***)

lemma par_tr_nil1[simp]:
  "(<> : s |[X]|tr t) = (s = <> & t = <>)"
apply (rule iffI)
apply (simp add: par_tr_nil_only_if)
by (simp add: par_tr_intros)

lemma par_tr_nil2[simp]:
  "(u : <> |[X]|tr <>) = (u = <>)"
apply (rule iffI)
apply (erule par_tr_elims)
by (simp_all)

(*-------------------*
 |     par Tick      |
 *-------------------*)

(*** only if ***)

lemma par_tr_Tick_only_if:
  "<Tick> : s |[X]|tr t ==> s = <Tick> & t = <Tick>"
apply (erule par_tr_elims)
by (simp_all)

(*** iff ***)

lemma par_tr_Tick1[simp]:
  "<Tick> : s |[X]|tr t = (s = <Tick> & t = <Tick>)"
apply (rule iffI)
apply (simp add: par_tr_Tick_only_if)
by (simp add: par_tr_intros)

lemma par_tr_Tick2[simp]:
  "(u : <Tick> |[X]|tr <Tick>) = (u = <Tick>)"
apply (rule iffI)
apply (erule par_tr_elims)
by (simp_all)

(*-----------------*
 |     par Ev      |
 *-----------------*)

(*** only if ***)

lemma par_tr_Ev_only_if:
 "<Ev a> : s |[X]|tr t
   ==> ((a  : X & s = <Ev a> & t = <Ev a>) |
        (a ~: X & s = <Ev a> & t = <>) |
        (a ~: X & s = <>     & t = <Ev a> ))"
apply (erule par_tr_elims)
by (simp_all)

(*** if ***)

lemma par_tr_Ev_if:
 "((a  : X & s = <Ev a> & t = <Ev a>) |
   (a ~: X & s = <Ev a> & t = <>) |
   (a ~: X & s = <>     & t = <Ev a> ))
   ==> <Ev a> : s |[X]|tr t"
apply (erule disjE)
apply (insert par_tr_Ev_sync[of "<>" "<>" X "<>" a], simp)
apply (erule disjE)
apply (insert par_tr_Ev_left[of "<>" "<>" X "<>" a], simp)
apply (insert par_tr_Ev_right[of "<>" "<>" X "<>" a], simp)
done

lemma par_tr_Ev:
 "<Ev a> : s |[X]|tr t
   = ((a  : X & s = <Ev a> & t = <Ev a>) |
      (a ~: X & s = <Ev a> & t = <>) |
      (a ~: X & s = <>     & t = <Ev a> ))"
apply (rule iffI)
apply (simp add: par_tr_Ev_only_if)
apply (simp add: par_tr_Ev_if)
done

(*--------------------------------------------*
 |                 par one                    |
 *--------------------------------------------*)

lemma par_tr_one:
 "<e> : s |[X]|tr t
   = ((e = Tick & s = <Tick> & t = <Tick>) |
     (EX a. e = Ev a &
       ((a  : X & s = <Ev a> & t = <Ev a>) |
        (a ~: X & s = <Ev a> & t = <>) |
        (a ~: X & s = <>     & t = <Ev a> ))))"
apply (insert event_Tick_or_Ev)
apply (drule_tac x="e" in spec)
apply (erule disjE)
apply (simp)

apply (erule exE)
apply (simp add: par_tr_Ev)
done

(*--------------------------------------------*
 |                par head                    |
 *--------------------------------------------*)

(*** only if ***)

lemma par_tr_head_only_if:
 "<Ev a> ^^^ u : s |[X]|tr t
   ==> (a  : X & (EX s' t'. u : s' |[X]|tr t'
               & s = <Ev a> ^^^ s' & t = <Ev a> ^^^ t')) |
       (a ~: X & (EX s'.    u : s' |[X]|tr t & s = <Ev a> ^^^ s')) |
       (a ~: X & (EX t'.    u : s |[X]|tr t' & t = <Ev a> ^^^ t'))"
apply (erule par_tr_elims)
by (simp_all)

(*** if ***)

lemma par_tr_head_if:
 "(a  : X & (EX s' t'. u : s' |[X]|tr t'
               & s = <Ev a> ^^^ s' & t = <Ev a> ^^^ t')) |
       (a ~: X & (EX s'.    u : s' |[X]|tr t & s = <Ev a> ^^^ s')) |
       (a ~: X & (EX t'.    u : s |[X]|tr t' & t = <Ev a> ^^^ t'))
  ==> <Ev a> ^^^ u : s |[X]|tr t"

 (*** sync ***)
 apply (erule disjE)
 apply (elim conjE exE)
 apply (simp add: par_tr_intros)

 (*** left ***)
 apply (erule disjE)
 apply (elim conjE exE)
 apply (simp add: par_tr_intros)

 (*** right ***)
 apply (elim conjE exE)
 apply (simp add: par_tr_intros)
done

(*** iff ***)

lemma par_tr_head:
 "<Ev a> ^^^ u : s |[X]|tr t
   = ((a  : X & (EX s' t'. u : s' |[X]|tr t'
              & s = <Ev a> ^^^ s' & t = <Ev a> ^^^ t')) |
      (a ~: X & (EX s'.    u : s' |[X]|tr t & s = <Ev a> ^^^ s')) |
      (a ~: X & (EX t'.    u : s |[X]|tr t' & t = <Ev a> ^^^ t')))"
apply (rule iffI)
apply (simp add: par_tr_head_only_if)
apply (simp add: par_tr_head_if)
done

(* erule *)

lemma par_tr_head_ifE:
 "[| <Ev a> ^^^ u : s |[X]|tr t ;
     [| (a  : X & (EX s' t'. u : s' |[X]|tr t'
                & s = <Ev a> ^^^ s' & t = <Ev a> ^^^ t')) |
        (a ~: X & (EX s'.    u : s' |[X]|tr t & s = <Ev a> ^^^ s')) |
        (a ~: X & (EX t'.    u : s |[X]|tr t' & t = <Ev a> ^^^ t')) |] ==> R
  |] ==> R"
by (simp add: par_tr_head)

(* head Ev Ev *)

lemma par_tr_head_Ev_Ev:
   "(u : (<Ev a> ^^^ s) |[X]|tr (<Ev b> ^^^ t))
    = (EX c v. u = <Ev c> ^^^ v &
               (c : X & v : s |[X]|tr t & a = c & b = c |
                c ~: X & v : s |[X]|tr (<Ev b> ^^^ t) & a = c |
                c ~: X & v : (<Ev a> ^^^ s) |[X]|tr t & b = c))"
apply (rule iffI)

 (* => *)
 apply (insert trace_nil_or_Tick_or_Ev)
 apply (drule_tac x="u" in spec)
 apply (elim disjE conjE exE)
 apply (simp_all)
 apply (simp add: par_tr_head)

 (* => *)
 apply (elim conjE exE)
 apply (simp add: par_tr_head)
done

(* step *)

lemma par_tr_step:
   "(u : s |[X]|tr t)
    = ((u = <> & s = <> & t = <>) |
       (u = <Tick> & s = <Tick> & t = <Tick>) |
       (EX a v. u = <Ev a> ^^^ v & 
        ((a  : X & (EX s' t'. v : s' |[X]|tr t'
              & s = <Ev a> ^^^ s' & t = <Ev a> ^^^ t')) |
         (a ~: X & (EX s'.    v : s' |[X]|tr t & s = <Ev a> ^^^ s')) |
         (a ~: X & (EX t'.    v : s |[X]|tr t' & t = <Ev a> ^^^ t')))))"
apply (insert trace_nil_or_Tick_or_Ev)
apply (drule_tac x="u" in spec)
apply (elim disjE)
apply (simp_all)
apply (elim exE)
apply (simp add: par_tr_head)
done

lemma par_tr_stepI:
   "((u = <> & s = <> & t = <>) |
       (u = <Tick> & s = <Tick> & t = <Tick>) |
       (EX a v. u = <Ev a> ^^^ v & 
        ((a  : X & (EX s' t'. v : s' |[X]|tr t'
              & s = <Ev a> ^^^ s' & t = <Ev a> ^^^ t')) |
         (a ~: X & (EX s'.    v : s' |[X]|tr t & s = <Ev a> ^^^ s')) |
         (a ~: X & (EX t'.    v : s |[X]|tr t' & t = <Ev a> ^^^ t')))))
     ==> (u : s |[X]|tr t)"
by (simp add: par_tr_step[THEN sym])

lemma par_tr_stepE:
   "[| u : s |[X]|tr t ;
      ((u = <> & s = <> & t = <>) |
       (u = <Tick> & s = <Tick> & t = <Tick>) |
       (EX a v. u = <Ev a> ^^^ v & 
        ((a  : X & (EX s' t'. v : s' |[X]|tr t'
              & s = <Ev a> ^^^ s' & t = <Ev a> ^^^ t')) |
         (a ~: X & (EX s'.    v : s' |[X]|tr t & s = <Ev a> ^^^ s')) |
         (a ~: X & (EX t'.    v : s |[X]|tr t' & t = <Ev a> ^^^ t')))))
     ==> R |] ==> R"
by (simp add: par_tr_step[THEN sym])

(*--------------------------------------------*
 |                par last                    |
 *--------------------------------------------*)

(*** only if ***)

lemma par_tr_last_only_if_lm:
 "ALL X u s t e.
    (u ^^^ <e> : s |[X]|tr t & noTick u)
   --> (((e  : Ev ` X | e = Tick) &
            (EX s' t'. u : s' |[X]|tr t' & s = s' ^^^ <e> & t = t' ^^^ <e>
                       & noTick s' & noTick t')) |
        (e ~: Ev ` X & e ~= Tick & 
            (EX s'.    u : s' |[X]|tr t & s = s' ^^^ <e> & noTick s' & noTick t)) |
        (e ~: Ev ` X & e ~= Tick & 
            (EX t'.    u : s |[X]|tr t' & t = t' ^^^ <e> & noTick s & noTick t')))" 
apply (rule allI)
apply (rule allI)
apply (induct_tac u rule: induct_trace)

(* base *)
 (* <> *)
 apply (intro allI impI)
 apply (simp add: par_tr_one)
 apply (erule disjE, simp)
 apply (erule exE, force)

 (* <Tick> *)
 apply (simp)

 (* <Ev a> ^^^ ua *)
 apply (intro allI impI)
 apply (elim conjE)
 apply (simp add: appt_assoc)
 apply (simp add: par_tr_head)
 apply (elim disjE conjE exE)

  (* head sync *)
  apply (drule_tac x="s'" in spec)
  apply (drule_tac x="t'" in spec)
  apply (drule_tac x="e" in spec)
  apply (simp)

   (* last sync *)
   apply (erule disjE, simp)
   apply (elim conjE exE)
   apply (rule disjI1)
   apply (rule_tac x="<Ev a> ^^^ s'a" in exI)
   apply (rule_tac x="<Ev a> ^^^ t'a" in exI)
   apply (simp add: appt_assoc)

   (* last left *)
   apply (erule disjE, simp)
   apply (elim conjE exE)
   apply (rule disjI1)
   apply (rule_tac x="<Ev a> ^^^ s'a" in exI, simp)
   apply (simp add: appt_assoc)

   (* last right *)
   apply (simp)
   apply (elim conjE exE)
   apply (rule disjI2)
   apply (rule_tac x="<Ev a> ^^^ t'a" in exI, simp)
   apply (simp add: appt_assoc)

  (* head left *)
  apply (drule_tac x="s'" in spec)
  apply (drule_tac x="t" in spec)
  apply (drule_tac x="e" in spec)
  apply (simp)

   (* last sync *)
   apply (erule disjE, simp)
   apply (elim conjE exE)
   apply (rule disjI1)
   apply (rule_tac x="<Ev a> ^^^ s'a" in exI)
   apply (rule_tac x="t'" in exI)
   apply (simp add: appt_assoc)

   (* last left *)
   apply (erule disjE, simp)
   apply (elim conjE exE)
   apply (rule disjI1)
   apply (rule_tac x="<Ev a> ^^^ s'a" in exI, simp)
   apply (simp add: appt_assoc)

   (* last right *)
   apply (simp)
   apply (elim conjE exE)
   apply (rule disjI2)
   apply (rule_tac x="t'" in exI, simp)

  (* head right *)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="t'" in spec)
  apply (drule_tac x="e" in spec)
  apply (simp)

   (* last sync *)
   apply (erule disjE, simp)
   apply (elim conjE exE)
   apply (rule disjI1)
   apply (rule_tac x="s'" in exI)
   apply (rule_tac x="<Ev a> ^^^ t'a" in exI)
   apply (simp add: appt_assoc)

   (* last left *)
   apply (erule disjE, simp)
   apply (elim conjE exE)
   apply (rule disjI1)
   apply (rule_tac x="s'" in exI, simp)

   (* last right *)
   apply (simp)
   apply (elim conjE exE)
   apply (rule disjI2)
   apply (rule_tac x="<Ev a> ^^^ t'a" in exI)
   apply (simp add: appt_assoc)
done

(*** rule ***)

lemma par_tr_last_only_if:
 "[| u ^^^ <e> : s |[X]|tr t ; noTick u |]
   ==> (((e  : Ev ` X | e = Tick) &
            (EX s' t'. u : s' |[X]|tr t' & s = s' ^^^ <e> & t = t' ^^^ <e>
                       & noTick s' & noTick t')) |
        (e ~: Ev ` X & e ~= Tick & 
            (EX s'.    u : s' |[X]|tr t & s = s' ^^^ <e> & noTick s' & noTick t)) |
        (e ~: Ev ` X & e ~= Tick & 
            (EX t'.    u : s |[X]|tr t' & t = t' ^^^ <e> & noTick s & noTick t')))" 
by (simp add: par_tr_last_only_if_lm)

(*** if ***)

lemma par_tr_last_if_lm:
 "ALL X u s t e. (noTick u &
   (((e  : Ev ` X | e = Tick) &
            (EX s' t'. u : s' |[X]|tr t' & s = s' ^^^ <e> & t = t' ^^^ <e>
                       & noTick s' & noTick t')) |
        (e ~: Ev ` X & e ~= Tick & 
            (EX s'.    u : s' |[X]|tr t & s = s' ^^^ <e> & noTick s' & noTick t)) |
        (e ~: Ev ` X & e ~= Tick & 
            (EX t'.    u : s |[X]|tr t' & t = t' ^^^ <e>  & noTick s & noTick t'))))
   --> u ^^^ <e> : s |[X]|tr t"
apply (rule allI)
apply (rule allI)
apply (induct_tac u rule: induct_trace)

(* base *)
 (* <> *)
 apply (intro allI impI)
 apply (simp add: par_tr_one)
 apply (elim conjE disjE)
 apply (force)
 apply (simp)
 apply (simp add: not_Tick_to_Ev, fast)
 apply (simp add: not_Tick_to_Ev, fast)

 (* <Tick> *)
 apply (simp)

 (* s ^^^ <e> *)
 apply (intro allI impI)
 apply (simp add: par_tr_head)
 apply (simp add: appt_assoc)
 apply (elim conjE)
 apply (elim disjE)

  (* last sync *)
  apply (elim conjE exE)

   (* sync *)
   apply (rotate_tac 3)
   apply (erule disjE)
   apply (elim conjE exE)
   apply (simp add: appt_assoc)
   apply (simp add: par_tr_head)
   apply (drule_tac x="s'a ^^^ <e>" in spec)
   apply (drule_tac x="t'a ^^^ <e>" in spec)
   apply (drule_tac x="e" in spec)
   apply (simp)
   apply (fast)

   (* left *)
   apply (rotate_tac -1)
   apply (erule disjE)
   apply (elim conjE exE)
   apply (simp add: appt_assoc)
   apply (simp add: par_tr_head)
   apply (drule_tac x="s'a ^^^ <e>" in spec)
   apply (drule_tac x="t' ^^^ <e>" in spec)
   apply (drule_tac x="e" in spec)
   apply (simp)
   apply (fast)

   (* right *)
   apply (elim conjE exE)
   apply (simp add: appt_assoc)
   apply (simp add: par_tr_head)
   apply (drule_tac x="s' ^^^ <e>" in spec)
   apply (drule_tac x="t'a ^^^ <e>" in spec)
   apply (drule_tac x="e" in spec)
   apply (simp)
   apply (fast)

  (* last left *)
  apply (elim conjE exE)

   (* sync *)
   apply (rotate_tac 4)
   apply (erule disjE)
   apply (elim conjE exE)
   apply (simp add: appt_assoc)
   apply (simp add: par_tr_head)
   apply (drule_tac x="s'a ^^^ <e>" in spec)
   apply (drule_tac x="t'" in spec)
   apply (drule_tac x="e" in spec)
   apply (simp)
   apply (fast)

   (* left *)
   apply (rotate_tac -1)
   apply (erule disjE)
   apply (elim conjE exE)
   apply (simp add: appt_assoc)
   apply (simp add: par_tr_head)
   apply (drule_tac x="s'a ^^^ <e>" in spec)
   apply (drule_tac x="t" in spec)
   apply (drule_tac x="e" in spec)
   apply (simp)
   apply (fast)

   (* right *)
   apply (elim conjE exE)
   apply (simp add: appt_assoc)
   apply (simp add: par_tr_head)
   apply (drule_tac x="s' ^^^ <e>" in spec)
   apply (drule_tac x="t'" in spec)
   apply (drule_tac x="e" in spec)
   apply (simp)
   apply (fast)

  (* last right *)
  apply (elim conjE exE)

   (* sync *)
   apply (rotate_tac 4)
   apply (erule disjE)
   apply (elim conjE exE)
   apply (simp add: appt_assoc)
   apply (simp add: par_tr_head)
   apply (drule_tac x="s'" in spec)
   apply (drule_tac x="t'a ^^^ <e>" in spec)
   apply (drule_tac x="e" in spec)
   apply (simp)
   apply (fast)

   (* left *)
   apply (rotate_tac -1)
   apply (erule disjE)
   apply (elim conjE exE)
   apply (simp add: appt_assoc)
   apply (simp add: par_tr_head)
   apply (drule_tac x="s'" in spec)
   apply (drule_tac x="t' ^^^ <e>" in spec)
   apply (drule_tac x="e" in spec)
   apply (simp)
   apply (fast)

   (* right *)
   apply (elim conjE exE)
   apply (simp add: appt_assoc)
   apply (simp add: par_tr_head)
   apply (drule_tac x="sa" in spec)
   apply (drule_tac x="t'a ^^^ <e>" in spec)
   apply (drule_tac x="e" in spec)
   apply (simp)
   apply (fast)
done

(*** rule ***)

lemma par_tr_last_if:
 "[| noTick u;
    ((e  : Ev ` X | e = Tick) &
          (EX s' t'. u : s' |[X]|tr t' & s = s' ^^^ <e> & t = t' ^^^ <e>
                      & noTick s' & noTick t')) |
     (e ~: Ev ` X & e ~= Tick & 
          (EX s'.    u : s' |[X]|tr t & s = s' ^^^ <e> & noTick s' & noTick t)) |
     (e ~: Ev ` X & e ~= Tick & 
          (EX t'.    u : s |[X]|tr t' & t = t' ^^^ <e> & noTick s & noTick t')) |]
   ==> u ^^^ <e> : s |[X]|tr t"
apply (insert par_tr_last_if_lm)
apply (drule_tac x="X" in spec)
apply (drule_tac x="u" in spec)
apply (drule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
apply (drule_tac x="e" in spec)
by (simp)

(*** iff ***)

lemma par_tr_last:
 "noTick u ==>
   u ^^^ <e> : s |[X]|tr t 
   = (((e  : Ev ` X | e = Tick) &
            (EX s' t'. u : s' |[X]|tr t' & s = s' ^^^ <e> & t = t' ^^^ <e>
                       & noTick s' & noTick t')) |
      (e ~: Ev ` X & e ~= Tick & 
            (EX s'.    u : s' |[X]|tr t & s = s' ^^^ <e> & noTick s' & noTick t)) |
      (e ~: Ev ` X & e ~= Tick & 
            (EX t'.    u : s |[X]|tr t' & t = t' ^^^ <e> & noTick s & noTick t')))" 
apply (rule iffI)
apply (simp add: par_tr_last_only_if)
apply (simp add: par_tr_last_if)
done

(*************************************************************
                     symmetricity  
 *************************************************************)

lemma par_tr_sym_only_if_lm:
  "ALL u s t. u : (s |[X]|tr t) --> u : (t |[X]|tr s)"
apply (rule allI)
apply (induct_tac u rule: induct_trace)
apply (simp_all)

apply (intro allI impI)
apply (erule par_tr_elims)

 (* <> *)
 apply (simp)

 (* <Tick> *)
 apply (simp)

 (* Ev_nil *)
 apply (drule_tac x="s'" in spec)
 apply (drule_tac x="<>" in spec)
 apply (simp add: par_tr_intros)

 (* nil_Ev *)
 apply (drule_tac x="<>" in spec)
 apply (drule_tac x="t'" in spec)
 apply (simp add: par_tr_intros)

 (* sync *)
 apply (drule_tac x="s'" in spec)
 apply (drule_tac x="t'" in spec)
 apply (simp add: par_tr_intros)

 (* left *)
 apply (drule_tac x="s'" in spec)
 apply (drule_tac x="t" in spec)
 apply (simp add: par_tr_intros)

 (* right *)
 apply (drule_tac x="sa" in spec)
 apply (drule_tac x="t'" in spec)
 apply (simp add: par_tr_intros)
done

lemma par_tr_sym_only_if:
  "u : (s |[X]|tr t) ==> u : (t |[X]|tr s)"
apply (insert par_tr_sym_only_if_lm[of X])
apply (drule_tac x="u" in spec)
apply (drule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
apply (simp)
done

lemma par_tr_sym: "s |[X]|tr t = t |[X]|tr s"
apply (auto)
apply (rule par_tr_sym_only_if, simp_all)
apply (rule par_tr_sym_only_if, simp_all)
done

(*************************************************************
                     prefix_closed
 *************************************************************)

lemma par_tr_prefix_lm:
 "ALL X v u s t. prefix v u & u : s |[X]|tr t
     --> (EX s' t'. v : s' |[X]|tr t' & 
                    prefix s' s & prefix t' t)"
apply (rule allI)
apply (rule allI)
apply (induct_tac v rule: induct_trace)
apply (simp_all add: disj_not1)
apply (simp add: prefix_Tick)

apply (intro allI impI)
apply (elim conjE exE)
apply (simp add: par_tr_head)

 (* sync *)
 apply (erule disjE)
 apply (elim conjE exE)
 apply (drule_tac x="u'" in spec)
 apply (drule_tac x="s'" in spec)
 apply (drule_tac x="t'" in spec)
 apply (force)

 (* left *)
 apply (erule disjE)
 apply (elim conjE exE)
 apply (drule_tac x="u'" in spec)
 apply (drule_tac x="s'" in spec)
 apply (drule_tac x="t" in spec)
 apply (force)

 (* right *)
 apply (elim conjE exE)
 apply (drule_tac x="u'" in spec)
 apply (drule_tac x="sa" in spec)
 apply (drule_tac x="t'" in spec)
 apply (force)
done

(*** rule ***)

lemma par_tr_prefix:
 "[| prefix v u ; u : s |[X]|tr t |]
  ==> (EX s' t'. v : s' |[X]|tr t' & prefix s' s & prefix t' t)"
apply (insert par_tr_prefix_lm)
apply (drule_tac x="X" in spec)
apply (drule_tac x="v" in spec)
apply (drule_tac x="u" in spec)
apply (drule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
by (simp)

lemma par_tr_prefixE:
 "[| prefix v u ; u : s |[X]|tr t ;
     !! s' t'. [| v : s' |[X]|tr t' ; prefix s' s ; prefix t' t |] ==> R
  |] ==> R"
apply (insert par_tr_prefix[of v u s X t])
by (auto)

(*************************************************************
                  parallel lemmas etc.
 *************************************************************)

(*******************************
          par_tr lenght 
 *******************************)

lemma par_tr_lengtht_lm:
 "ALL X u s t. u : s |[X]|tr t
         --> lengtht s <= lengtht u & lengtht t <= lengtht u"
apply (rule allI)
apply (rule allI)
apply (induct_tac u rule: induct_trace)
apply (simp_all)

apply (intro allI impI)
apply (simp add: par_tr_head)

 (* sync *)
 apply (erule disjE)
 apply (elim conjE exE)
 apply (drule_tac x="s'" in spec)
 apply (drule_tac x="t'" in spec)
 apply (simp)

 (* left *)
 apply (erule disjE)
 apply (elim conjE exE)
 apply (drule_tac x="s'" in spec)
 apply (drule_tac x="t" in spec)
 apply (force)

 (* right *)
 apply (elim conjE exE)
 apply (drule_tac x="sa" in spec)
 apply (drule_tac x="t'" in spec)
 apply (force)
done

(*** rule ***)

lemma par_tr_lengtht:
 "u : s |[X]|tr t ==> lengtht s <= lengtht u & lengtht t <= lengtht u"
by (simp add: par_tr_lengtht_lm)

(*** ruleE ***)

lemma par_tr_lengthtE:
 "[| u : s |[X]|tr t ; 
     [| lengtht s <= lengtht u ; lengtht t <= lengtht u|] ==> R |] ==> R"
by (simp add: par_tr_lengtht)

(**************************************************
                    para
 **************************************************)

lemma par_tr_nil_Ev_rev:
  "u : <> |[X]|tr (<Ev a> ^^^ t)
   ==> a ~: X & (EX v. u = <Ev a> ^^^ v & v : <> |[X]|tr t)"
apply (erule par_tr_elims)
by (simp_all add: par_tr_intros)

lemma par_tr_Tick_Ev_rev:
  "u : <Tick> |[X]|tr (<Ev a> ^^^ t)
   ==> a ~: X & (EX v. u = <Ev a> ^^^ v & v : <Tick> |[X]|tr t)"
apply (erule par_tr_elims)
by (simp_all add: par_tr_intros)

(**************************************************
                    noTick
 **************************************************)

(*-----------------*
 |   par noTick    |
 *-----------------*)

(*** only if ***)

lemma par_tr_noTick_only_if_lm:
 "ALL s t. ( u : s |[X]|tr t & noTick s & noTick t ) --> noTick u"
apply (induct_tac u rule: induct_trace)
apply (simp)
apply (intro allI)
apply (case_tac "s ~= <Tick>", simp)
apply (case_tac "t ~= <Tick>", simp)
apply (simp)

apply (intro allI impI)
apply (elim conjE)
apply (simp add: par_tr_head)
apply (elim disjE conjE exE)
apply (auto)
done

lemma par_tr_noTick_only_if:
 "[| u : s |[X]|tr t ; noTick s ; noTick t |] ==> noTick u"
apply (insert par_tr_noTick_only_if_lm[of u X])
apply (drule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
by (simp)

(*** if ***)

lemma par_tr_noTick_if_lm:
 "ALL s t. ( u : s |[X]|tr t & noTick u ) --> ( noTick s & noTick t )"
apply (induct_tac u rule: induct_trace)
apply (simp)
apply (simp)

apply (intro allI impI)
apply (elim conjE)
apply (erule par_tr_head_ifE)
apply (elim conjE exE disjE)

apply (drule_tac x="s'" in spec)
apply (drule_tac x="t'" in spec)
apply (simp)

apply (drule_tac x="s'" in spec)
apply (drule_tac x="t" in spec)
apply (simp)

apply (drule_tac x="sa" in spec)
apply (drule_tac x="t'" in spec)
apply (simp)
done

lemma par_tr_noTick_if:
 "[| u : s |[X]|tr t ; noTick u |] ==> ( noTick s & noTick t )"
apply (insert par_tr_noTick_if_lm[of u X])
apply (drule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
by (simp)

(*** iff ***)

lemma par_tr_noTick:
 "u : s |[X]|tr t ==> (noTick s & noTick t) = noTick u"
apply (rule iffI)
apply (simp add: par_tr_noTick_only_if)
apply (simp add: par_tr_noTick_if)
done

lemmas par_tr_noTick_compo = par_tr_noTick_only_if
lemmas par_tr_noTick_decompo = par_tr_noTick_if

(****** used in Alpha_parallel ******)

(*** nil-Tick ***)

lemma par_tr_nil_Tick[simp]:
  "(u : <> |[X]|tr <Tick>) = False"
apply (induct_tac u rule: induct_trace)
by (simp_all add: par_tr_head)

lemma par_tr_Tick_nil[simp]:
  "(u : <Tick> |[X]|tr <>) = False"
apply (induct_tac u rule: induct_trace)
by (simp_all add: par_tr_head)

(*** nil-Ev ***)

lemma par_tr_nil_Ev_iff:
  "u : <> |[X]|tr (<Ev a> ^^^ t)
   = (a ~: X & (EX v. u = <Ev a> ^^^ v & v : <> |[X]|tr t))"
apply (rule iffI)
apply (rule par_tr_nil_Ev_rev)
apply (simp)

apply (elim conjE exE, simp)
apply (simp add: par_tr_nil_Ev)
done

(*** Tcik-Ev ***)

lemma par_tr_Tick_Ev_iff:
  "u : <Tick> |[X]|tr (<Ev a> ^^^ t)
   = (a ~: X & (EX v. u = <Ev a> ^^^ v & v : <Tick> |[X]|tr t))"
apply (rule iffI)
apply (rule par_tr_Tick_Ev_rev)
apply (simp)

apply (elim conjE exE, simp)
apply (simp add: par_tr_Ev_right)
done

(****** nil ******)

lemma par_tr_nil_left_only_if_imp:
 "ALL u. (u : <> |[X]|tr s)
   --> (u = s & Tick ~: sett u & sett u Int Ev ` X = {})"
apply (induct_tac s rule: induct_trace)
apply (simp_all)

apply (intro allI impI)
apply (simp add: par_tr_nil_Ev_iff)
apply (elim conjE exE)
apply (drule_tac x="v" in spec)
apply (auto)
done

lemma par_tr_nil_left_only_if:
 "(u : <> |[X]|tr s) 
   ==> u = s & Tick ~: sett u & sett u Int Ev ` X = {}"
apply (insert par_tr_nil_left_only_if_imp[of X s])
apply (drule_tac x="u" in spec)
apply (auto)
done

lemma par_tr_nil_left_if_imp:
 "(Tick ~: sett u & sett u Int Ev ` X = {})
  --> (u : <> |[X]|tr u)"
apply (induct_tac u rule: induct_trace)
by (auto simp add: par_tr_head)

lemma par_tr_nil_left_if:
 "[| Tick ~: sett u ; sett u Int Ev ` X = {} |]
  ==> (u : <> |[X]|tr u)"
by (simp add: par_tr_nil_left_if_imp)

(*** nil left ***)

lemma par_tr_nil_left:
 "(u : <> |[X]|tr s) = (u = s & Tick ~: sett u & sett u Int Ev ` X = {})"
apply (rule iffI)
apply (simp add: par_tr_nil_left_only_if)
apply (auto simp add: par_tr_nil_left_if)
done

(*** nil right ***)

lemma par_tr_nil_right:
 "(u : s |[X]|tr <>) = (u = s & Tick ~: sett u & sett u Int Ev ` X = {})"
apply (simp add: par_tr_sym)
apply (simp add: par_tr_nil_left)
done

lemmas par_tr_nil = par_tr_nil_left par_tr_nil_right

(****** Tick ******)

lemma par_tr_Tick_left_only_if_imp:
 "ALL u. u : <Tick> |[X]|tr s 
   --> (u = s & Tick : sett u & sett u Int Ev ` X = {})"
apply (induct_tac s rule: induct_trace)
apply (simp_all)
apply (simp add: image_def)

apply (intro allI impI)
apply (simp add: par_tr_Tick_Ev_iff)
apply (elim conjE exE)
apply (drule_tac x="v" in spec)
apply (auto)
done

lemma par_tr_Tick_left_only_if:
 "(u : <Tick> |[X]|tr s) 
   ==> u = s & Tick : sett u & sett u Int Ev ` X = {}"
apply (insert par_tr_Tick_left_only_if_imp[of X s])
apply (drule_tac x="u" in spec)
apply (auto)
done

lemma par_tr_Tick_left_if_imp:
 "(Tick : sett u & sett u Int Ev ` X = {})
  --> (u : <Tick> |[X]|tr u)"
apply (induct_tac u rule: induct_trace)
by (auto simp add: par_tr_head)

lemma par_tr_Tick_left_if:
 "[| Tick : sett u ; sett u Int Ev ` X = {} |]
  ==> (u : <Tick> |[X]|tr u)"
by (simp add: par_tr_Tick_left_if_imp)

(*** Tick left ***)

lemma par_tr_Tick_left:
 "(u : <Tick> |[X]|tr s) 
= (u = s & Tick : sett u & sett u Int Ev ` X = {})"
apply (rule iffI)
apply (simp add: par_tr_Tick_left_only_if)
apply (auto simp add: par_tr_Tick_left_if)
done

(*** Tick right ***)

lemma par_tr_Tick_right:
 "(u : s |[X]|tr <Tick>) 
= (u = s & Tick : sett u & sett u Int Ev ` X = {})"
apply (simp add: par_tr_sym[of _ _ "<Tick>"])
apply (simp add: par_tr_Tick_left)
done

lemmas par_tr_Tick = par_tr_Tick_left par_tr_Tick_right

(*** par sett ***)

lemma par_tr_sett: "ALL s t. u : s |[X]|tr t --> sett u <= sett s Un sett t"
apply (induct_tac u rule: induct_trace)
apply (simp_all)
apply (intro allI impI)
apply (simp add: par_tr_head)
apply (erule disjE)

(* sync *)
 apply (elim conjE exE)
 apply (drule_tac x="s'" in spec)
 apply (drule_tac x="t'" in spec)
 apply (force)

(* left *)
 apply (erule disjE)
 apply (elim conjE exE)
 apply (drule_tac x="s'" in spec)
 apply (drule_tac x="t" in spec)
 apply (force)

(* right *)
 apply (elim conjE exE)
 apply (drule_tac x="sa" in spec)
 apply (drule_tac x="t'" in spec)
 apply (force)
done

(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)


lemma interleave_appt_left_lm:
  "ALL u s t. 
   (u : s |[{}]|tr t & (noTick v))
     --> v ^^^ u : (v ^^^ s) |[{}]|tr t"
apply (induct_tac v rule: induct_trace)
apply (simp_all)
apply (intro allI impI)
apply (simp)
apply (drule_tac x="u" in spec)
apply (drule_tac x="sa" in spec)
apply (drule_tac x="t" in spec)
apply (erule conjE)
apply (simp add: appt_assoc)
apply (simp add: par_tr_head)
done

lemma interleave_appt_left_step:
  "[| u : s |[{}]|tr t ; noTick v |] ==> v ^^^ u : (v ^^^ s) |[{}]|tr t"
by (simp add: interleave_appt_left_lm)

lemma interleave_appt_right_step:
  "[| u : t |[{}]|tr s ; noTick v |] ==> v ^^^ u : t |[{}]|tr (v ^^^ s)"
apply (simp add: par_tr_sym)
apply (insert interleave_appt_left_step[of u s t v])
apply (simp add: par_tr_sym)
done

lemma interleave_appt_left_nil:
  "[| u : <> |[{}]|tr t ; noTick v |] ==> v ^^^ u : v |[{}]|tr t"
apply (insert interleave_appt_left_step[of u <> t v])
by (simp)

lemma interleave_appt_right_nil:
  "[| u : t |[{}]|tr <> ; noTick v |] ==> v ^^^ u : t |[{}]|tr v"
apply (insert interleave_appt_right_step[of u t <> v])
by (simp)

lemma interleave_appt_left_nil_nil:
  "noTick t ==> t : t |[{}]|tr <>"
apply (insert interleave_appt_left_step[of <> <> <> t])
by (simp)

lemma interleave_appt_right_nil_nil:
  "noTick t ==> t : <> |[{}]|tr t"
apply (insert interleave_appt_right_step[of <> <> <> t])
by (simp)

lemmas interleave_appt_left =
       interleave_appt_left_step
       interleave_appt_left_nil
       interleave_appt_left_nil_nil

lemmas interleave_appt_right =
       interleave_appt_right_step
       interleave_appt_right_nil
       interleave_appt_right_nil_nil

(*  par decompo *)

lemma par_tr_app_right[rule_format]:
  "ALL u v s t.
   (noTick u & sett u Int (Ev ` X) = {} & v : (s |[X]|tr t))
     --> u ^^^ v : (s |[X]|tr (u ^^^ t))"
apply (rule)
apply (induct_tac u rule: induct_trace)
apply (simp_all)
apply (intro allI impI)
apply (elim exE conjE)
apply (drule_tac x="v" in spec)
apply (drule_tac x="sa" in spec)
apply (drule_tac x="t" in spec)
apply (simp)
apply (simp add: appt_assoc)
apply (simp add: par_tr_head)
apply (auto)
done

(****************** to add it again ******************)

declare disj_not1   [simp] 

end
