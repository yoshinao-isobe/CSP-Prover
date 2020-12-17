           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005 (modified)    |
            |                 August 2005 (modified)    |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_domain
imports CSP_T.CSP_T_traces CSP_F_failures
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*********************************************************
                        domF
 *********************************************************)

(*--------------------------------*
 |             STOP               |
 *--------------------------------*)

(* T2 *)

lemma STOP_T2 : "HC_T2 (traces(STOP) (fstF o M), failures(STOP) M)"
by (simp add: HC_T2_def in_traces in_failures)

(* F3 *)

lemma STOP_F3 : "HC_F3 (traces(STOP) (fstF o M), failures(STOP) M)"
by (simp add: HC_F3_def in_traces in_failures)

(* T3_F4 *)

lemma STOP_T3_F4 : "HC_T3_F4 (traces(STOP) (fstF o M), failures(STOP) M)"
by (auto simp add: HC_T3_F4_def in_traces in_failures)

(*** STOP_domF ***)

lemma STOP_domF : "(traces(STOP) (fstF o M), failures(STOP) M) : domF"
apply (simp add: domF_iff)
apply (simp add: STOP_T2)
apply (simp add: STOP_F3)
apply (simp add: STOP_T3_F4)
done

(*--------------------------------*
 |             SKIP               |
 *--------------------------------*)

(* T2 *)

lemma SKIP_T2 : "HC_T2 (traces(SKIP) (fstF o M), failures(SKIP) M)"
by (simp add: HC_T2_def in_traces in_failures)

(* F3 *)

lemma SKIP_F3 : "HC_F3 (traces(SKIP) (fstF o M), failures(SKIP) M)"
apply (simp add: HC_F3_def in_traces in_failures)
by (auto simp add: Evset_def)

(* T3_F4 *)

lemma SKIP_T3_F4 : "HC_T3_F4 (traces(SKIP) (fstF o M), failures(SKIP) M)"
by (auto simp add: HC_T3_F4_def in_traces in_failures)

(*** SKIP_domF ***)

lemma SKIP_domF : "(traces(SKIP) (fstF o M), failures(SKIP) M) : domF"
apply (simp add: domF_iff)
apply (simp add: SKIP_T2)
apply (simp add: SKIP_F3)
apply (simp add: SKIP_T3_F4)
done

(*--------------------------------*
 |              DIV               |
 *--------------------------------*)

(* T2 *)

lemma DIV_T2 : "HC_T2 (traces(DIV) (fstF o M), failures(DIV) M)"
by (simp add: HC_T2_def in_traces in_failures)

(* F3 *)

lemma DIV_F3 : "HC_F3 (traces(DIV) (fstF o M), failures(DIV) M)"
by (simp add: HC_F3_def in_traces in_failures)

(* T3_F4 *)

lemma DIV_T3_F4 : "HC_T3_F4 (traces(DIV) (fstF o M), failures(DIV) M)"
by (auto simp add: HC_T3_F4_def in_traces in_failures)

(*** DIV_domF ***)

lemma DIV_domF : "(traces(DIV) (fstF o M), failures(DIV) M) : domF"
apply (simp add: domF_iff)
apply (simp add: DIV_T2)
apply (simp add: DIV_F3)
apply (simp add: DIV_T3_F4)
done

(*--------------------------------*
 |          Act_prefix            |
 *--------------------------------*)

(* T2 *)

lemma Act_prefix_T2 :
  "(traces(P) (fstF o M), failures(P) M) : domF
    ==> HC_T2 (traces(a -> P) (fstF o M), failures(a -> P) M)"
apply (simp add: HC_T2_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE, simp)

apply (simp add: domF_def HC_T2_def)
apply (elim conjE)
apply (drule_tac x="sa" in spec)
by (force)

(* F3 *)

lemma Act_prefix_F3 :
  "(traces(P) (fstF o M), failures(P) M) : domF
    ==> HC_F3 (traces(a -> P) (fstF o M), failures(a -> P) M)"
apply (simp add: HC_F3_def in_traces in_failures)
apply (intro allI impI)

apply (elim conjE disjE, simp)
apply (case_tac "Ev a ~: Y", simp)  (* show "Ev a : Y --> contradict" *)
apply (drule_tac x="Ev a" in spec, simp)
apply (drule_tac x="<>" in spec, simp)

apply (elim conjE exE, simp)
apply (simp add: domF_def HC_F3_def)
apply (elim conjE)
apply (drule_tac x="sa" in spec)
apply (drule_tac x="X" in spec)
apply (drule_tac x="Y" in spec)
apply (simp)

apply (drule mp)
 apply (intro allI impI)
 apply (drule_tac x="aa" in spec, simp)
 apply (drule_tac x="sa ^^^ <aa>" in spec)
apply (simp add: appt_assoc)
by (simp)

(* T3_F4 *)

lemma Act_prefix_T3_F4 : 
  "(traces(P) (fstF o M), failures(P) M) : domF
    ==> HC_T3_F4 (traces(a -> P) (fstF o M), failures(a -> P) M)"
apply (simp add: HC_T3_F4_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE)
apply (insert trace_nil_or_Tick_or_Ev)
apply (drule_tac x="s" in spec)

apply (erule disjE, simp)   (* s ^^^ <Tick> = <> --> contradict *)
apply (erule disjE, simp)   (* s = <> --> contradict *)
apply (erule disjE, simp)   (* s = <Tick> --> contradict *)

apply (elim conjE exE)      (* s = [Ev a]t ^^^ sb *)

apply (simp add: domF_iff HC_T3_F4_def)
apply (elim conjE exE)
apply (drule_tac x="sb" in spec)
apply (simp add: appt_assoc)
done

(*** Act_prefix_domF ***)

lemma Act_prefix_domF : 
  "(traces(P) (fstF o M), failures(P) M) : domF
    ==> (traces(a -> P) (fstF o M), failures(a -> P) M) : domF"
apply (simp (no_asm) add: domF_iff)
apply (simp add: Act_prefix_T2)
apply (simp add: Act_prefix_F3)
apply (simp add: Act_prefix_T3_F4)
done

(*--------------------------------*
 |        Ext_pre_choice          |
 *--------------------------------*)

(* T2 *)

lemma Ext_pre_choice_T2 :
  "ALL a. (traces(Pf a) (fstF o M), failures(Pf a) M) : domF
     ==> HC_T2 (traces(? :X -> Pf) (fstF o M), failures(? :X -> Pf) M)"
apply (simp add: HC_T2_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE, simp)

apply (drule_tac x="a" in spec)
apply (simp add: domF_def HC_T2_def)
apply (elim conjE)
apply (drule_tac x="sa" in spec)
by (force)

(* F3 *)

lemma Ext_pre_choice_F3 :
  "ALL a. (traces(Pf a) (fstF o M), failures(Pf a) M) : domF
     ==> HC_F3 (traces(? :X -> Pf) (fstF o M), failures(? :X -> Pf) M)"
apply (simp add: HC_F3_def in_traces in_failures)
apply (intro allI impI)

apply (elim conjE disjE, simp)

(* s = <> *)
apply (case_tac "EX a. Ev a :Ev ` X Int (Xa Un Y)")  (* show contradiction" *)
 apply (elim conjE exE)
 apply (drule_tac x="Ev a" in spec)
 apply (drule mp)
  apply (simp)                      (* show "Ev a : Y" *)
  apply (elim conjE disjE)
  apply (fast)                      (* contradict *)
  apply (simp)

 apply (drule_tac x="a" in spec)
 apply (drule_tac x="a" in spec)
 apply (simp)
 apply (drule_tac x="s" in spec)
 apply (simp)
 apply (fast)                      (* contradict *)
apply (fast)                       (* Ev ` X Int (Xa Un Y) = {} *)

(* s ~= <> *)
apply (elim conjE exE, simp)
apply (drule_tac x="a" in spec)
apply (simp add: domF_def HC_F3_def)
apply (elim conjE)
apply (drule_tac x="sa" in spec)
apply (drule_tac x="Xa" in spec)
apply (drule_tac x="Y" in spec)
apply (simp)

apply (drule mp)
 apply (intro allI impI)
 apply (drule_tac x="aa" in spec, simp)
 apply (drule_tac x="a" in spec)
 apply (drule_tac x="sa ^^^ <aa>" in spec)
 apply (simp add: appt_assoc)
by (simp)

(* T3_F4 *)

lemma Ext_pre_choice_T3_F4 : 
  "ALL a. (traces(Pf a) (fstF o M), failures(Pf a) M) : domF
     ==> HC_T3_F4 (traces(? :X -> Pf) (fstF o M), failures(? :X -> Pf) M)"
apply (simp add: HC_T3_F4_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE)
apply (insert trace_nil_or_Tick_or_Ev)
apply (drule_tac x="s" in spec)

apply (erule disjE, simp)   (* contradict *)
apply (erule disjE, simp)   (* s = <> --> contradict *)
apply (erule disjE, simp)   (* s = <Tick> --> contradict *)

apply (elim conjE exE)      (* s = [Ev aa]t ^^^ sb *)
apply (drule_tac x="a" in spec)
apply (simp add: domF_iff HC_T3_F4_def)
apply (elim conjE exE)
apply (drule_tac x="sb" in spec)
apply (simp add: appt_assoc)
done

(*** Ext_pre_choice_domF ***)

lemma Ext_pre_choice_domF : 
  "ALL a. (traces(Pf a) (fstF o M), failures(Pf a) M) : domF
     ==> (traces(? :X -> Pf) (fstF o M), failures(? :X -> Pf) M) : domF"
apply (simp (no_asm) add: domF_iff)
apply (simp add: Ext_pre_choice_T2)
apply (simp add: Ext_pre_choice_F3)
apply (simp add: Ext_pre_choice_T3_F4)
done

(*--------------------------------*
 |          Ext_choice            |
 *--------------------------------*)

(* T2 *)

lemma Ext_choice_T2 :
  "[| (traces(P) (fstF o M), failures(P) M) : domF ; 
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> HC_T2 (traces(P [+] Q) (fstF o M), failures(P [+] Q) M)"
apply (simp add: HC_T2_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE)

apply (simp add: domF_def HC_T2_def)
apply (elim conjE)
apply (drule_tac x="s" in spec)
apply (drule_tac x="s" in spec)
by (fast)

(* F3 *)

lemma Ext_choice_F3 :
  "[| (traces(P) (fstF o M), failures(P) M) : domF ; 
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> HC_F3 (traces(P [+] Q) (fstF o M), failures(P [+] Q) M)"
apply (simp add: HC_F3_def in_traces in_failures)
apply (intro allI impI)

apply (elim conjE disjE)
apply (simp_all add: domF_def HC_F3_def)
by (auto simp add: Evset_def)

(* T3_F4 *)

lemma Ext_choice_T3_F4 : 
  "[| (traces(P) (fstF o M), failures(P) M) : domF ; 
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> HC_T3_F4 (traces(P [+] Q) (fstF o M), failures(P [+] Q) M)"
apply (simp add: HC_T3_F4_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE)

apply (simp add: domF_iff HC_T3_F4_def)
apply (elim conjE)
apply (drule_tac x="s" in spec)
apply (drule_tac x="s" in spec)
by (auto)

(*** Ext_choice_domF ***)

lemma Ext_choice_domF : 
  "[| (traces(P) (fstF o M), failures(P) M) : domF ; 
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> (traces(P [+] Q) (fstF o M), failures(P [+] Q) M) : domF"
apply (simp (no_asm) add: domF_iff)
apply (simp add: Ext_choice_T2)
apply (simp add: Ext_choice_F3)
apply (simp add: Ext_choice_T3_F4)
done

(*--------------------------------*
 |          Int_choice            |
 *--------------------------------*)

(* T2 *)

lemma Int_choice_T2 :
  "[| (traces(P) (fstF o M), failures(P) M) : domF ; 
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> HC_T2 (traces(P |~| Q) (fstF o M), failures(P |~| Q) M)"
apply (simp add: HC_T2_def in_traces in_failures)
apply (simp add: domF_def HC_T2_def)
by (auto)

(* F3 *)

lemma Int_choice_F3 :
  "[| (traces(P) (fstF o M), failures(P) M) : domF ; 
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> HC_F3 (traces(P |~| Q) (fstF o M), failures(P |~| Q) M)"
apply (simp add: HC_F3_def in_traces in_failures)
apply (simp add: domF_def HC_F3_def)
by (auto)

(* T3_F4 *)

lemma Int_choice_T3_F4 : 
  "[| (traces(P) (fstF o M), failures(P) M) : domF ; 
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> HC_T3_F4 (traces(P |~| Q) (fstF o M), failures(P |~| Q) M)"
apply (simp add: HC_T3_F4_def in_traces in_failures)
apply (simp add: domF_iff HC_T3_F4_def)
by (auto)

(*** Int_choice_domF ***)

lemma Int_choice_domF : 
  "[| (traces(P) (fstF o M), failures(P) M) : domF ; 
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> (traces(P |~| Q) (fstF o M), failures(P |~| Q) M) : domF"
apply (simp (no_asm) add: domF_iff)
apply (simp add: Int_choice_T2)
apply (simp add: Int_choice_F3)
apply (simp add: Int_choice_T3_F4)
done

(*--------------------------------*
 |        Rep_int_choice          |
 *--------------------------------*)

(* T2 *)

lemma Union_proc_T2:
  "ALL c. (Tf c, Ff c) : domF
   ==> HC_T2 ({t. t = <> | (EX c:C. t :t Tf c)}t,
                         {f. EX c:C. f :f Ff c}f)"
apply (simp add: HC_T2_def)
apply (simp add: in_traces)
apply (simp add: in_failures)
apply (intro allI impI)
apply (elim conjE bexE exE)
apply (rule disjI2)
apply (drule_tac x="c" in spec)
apply (rule_tac x="c" in bexI)
apply (simp add: domF_def HC_T2_def)
by (auto)

lemma Rep_int_choice_T2 :
  "ALL c. (traces(Pf c) (fstF o M), failures(Pf c) M) : domF
     ==> HC_T2 (traces(!! :C .. Pf) (fstF o M), failures(!! :C .. Pf) M)"
apply (simp add: traces_iff failures_iff)
apply (simp add: Union_proc_T2)
done

(* F3 *)

lemma Union_proc_F3:
  "ALL c. (Tf c, Ff c) : domF
   ==>
   HC_F3 ({t. t = <> | (EX c:C. t :t Tf c)}t,
          {f. EX c:C. f :f Ff c}f)"
apply (simp add: HC_F3_def)
apply (simp add: in_traces)
apply (simp add: in_failures)
apply (intro allI)
apply (intro impI)
apply (elim conjE bexE)
apply (rule_tac x="c" in bexI)
apply (drule_tac x="c" in spec)
apply (rule domF_F3)
apply (auto)
done

lemma Rep_int_choice_nat : 
  "ALL c. (traces(Pf c) (fstF o M), failures(Pf c) M) : domF
     ==> HC_F3 (traces(!! :C .. Pf) (fstF o M), failures(!! :C .. Pf) M)"
apply (simp add: traces_iff failures_iff)
apply (simp add: Union_proc_F3)
done

(* T3_F4 *)

lemma Union_proc_T3_F4:
  "ALL c. (Tf c, Ff c) : domF
   ==>
   HC_T3_F4 ({t. t = <> | (EX c:C. t :t Tf c)}t,
             {f. EX c:C. f :f Ff c}f)"
apply (simp add: HC_T3_F4_def)
apply (simp add: in_traces)
apply (simp add: in_failures)
apply (auto)
apply (rule_tac x="c" in bexI)
apply (rule domF_F4)
apply (simp_all)
apply (rule_tac x="c" in bexI)
apply (rule domF_T3)
apply (simp_all)
done

lemma Rep_int_choice_T3_F4 : 
  "ALL c. (traces(Pf c) (fstF o M), failures(Pf c) M) : domF
     ==> HC_T3_F4 (traces(!! :C .. Pf) (fstF o M),
                   failures(!! :C .. Pf) M)"
apply (simp add: traces_iff failures_iff)
apply (simp add: Union_proc_T3_F4)
done

(*** F ***)

lemma Union_proc_domF:
  "ALL c. (Tf c, Ff c) : domF
   ==> ({t. t = <> | (EX c:C. t :t Tf c)}t,
        {f. EX c:C. f :f Ff c}f) : domF"
apply (simp (no_asm) add: domF_iff)
apply (simp add: Union_proc_T2)
apply (simp add: Union_proc_F3)
apply (simp add: Union_proc_T3_F4)
done

(*** Rep_int_choice_domF ***)

lemma Rep_int_choice_domF : 
  "ALL c. (traces(Pf c) (fstF o M), failures(Pf c) M) : domF
     ==> (traces(!! :C .. Pf) (fstF o M), failures(!! :C .. Pf) M) : domF"
apply (simp add: traces_iff failures_iff)
apply (simp add: Union_proc_domF)
done

(*--------------------------------*
 |               IF               |
 *--------------------------------*)

(* T2 *)

lemma IF_T2 :
  "[| (traces(P) (fstF o M), failures(P) M) : domF ;
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> HC_T2 (traces(IF b THEN P ELSE Q) (fstF o M), 
                failures(IF b THEN P ELSE Q) M)"
by (simp add: HC_T2_def in_traces in_failures domF_def)

(* F3 *)

lemma IF_F3 :
  "[| (traces(P) (fstF o M), failures(P) M) : domF ;
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> HC_F3 (traces(IF b THEN P ELSE Q) (fstF o M), failures(IF b THEN P ELSE Q) M)"
by (simp add: HC_F3_def in_traces in_failures domF_def)

(* T3_F4 *)

lemma IF_T3_F4 : 
  "[| (traces(P) (fstF o M), failures(P) M) : domF ;
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> HC_T3_F4 (traces(IF b THEN P ELSE Q) (fstF o M), 
                   failures(IF b THEN P ELSE Q) M)"
by (simp add: HC_T3_F4_def in_traces in_failures domF_iff)

(*** IF_domF ***)

lemma IF_domF :
  "[| (traces(P) (fstF o M), failures(P) M) : domF ;
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> (traces(IF b THEN P ELSE Q) (fstF o M), 
          failures(IF b THEN P ELSE Q) M) : domF"
apply (simp (no_asm) add: domF_iff)
apply (simp add: IF_T2)
apply (simp add: IF_F3)
apply (simp add: IF_T3_F4)
done

(*--------------------------------*
 |           Parallel             |
 *--------------------------------*)

(*** T2 ***)

lemma Parallel_T2 :
  "[| (traces(P) (fstF o M), failures(P) M) : domF ; 
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> HC_T2 (traces(P |[X]| Q) (fstF o M), failures(P |[X]| Q) M)"
apply (simp add: HC_T2_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE)
apply (rule_tac x="sa" in exI)
apply (rule_tac x="t" in exI)
apply (simp)
apply (simp add: domF_def HC_T2_def)
apply (elim conjE)
apply (drule_tac x="sa" in spec)
apply (drule_tac x="t" in spec)

apply (drule mp, rule_tac x="Y" in exI, simp)
apply (drule mp, rule_tac x="Z" in exI, simp)
by (simp)

(*** F3 ***)

lemma Parallel_F3_lm1: "X1 Un (X2 Un X3) - X = (X1 - X) Un (X2 - X) Un (X3 - X)"
by (auto)

lemma Parallel_F3_lm2: "[| X1 = X2 ; Y1 = Y2 |] ==> X1 Un Y1 = X2 Un Y2"
by (auto)

lemma Parallel_F3 :
  "[| (traces(P) (fstF o M), failures(P) M) : domF ; 
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> HC_F3 (traces(P |[X]| Q) (fstF o M), failures(P |[X]| Q) M)"
apply (simp add: HC_F3_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE)
apply (rename_tac u X12 Y X1 X2 s t)

(* (u, X12) :f [[P |[X]| Q]]F *)
(* (s, X1)  :f [[P]]F         *)
(* (t, X2)  :f [[Q]]F         *)
(*  X12 = X1 Un X2               *)

apply (rule_tac x=
        "X1 Un
         ({a. a : Y & (a = Tick | a : Ev ` X) & s ^^^ <a> ~:t traces(P) (fstF o M)} Un
          {a. a : Y & a ~= Tick & a ~: Ev ` X})" in exI)       (* Z1 *)
apply (rule_tac x=
        "X2 Un
         ({a. a : Y & (a = Tick | a : Ev ` X) & t ^^^ <a> ~:t traces(Q) (fstF o M)} Un
          {a. a : Y & a ~= Tick & a ~: Ev ` X})" in exI)       (* Z2 *)

apply (subgoal_tac "noTick s & noTick t", simp)
apply (rule conjI)

(* show X12 Un Y = X1 Un Z1 Un Z2 *)
apply (rule equalityI)

 (* <= *)
 apply (rule subsetI, simp)
 apply (erule disjE, simp)
 apply (erule disjE, simp)
 apply (simp)

 apply (drule_tac x="x" in spec, simp)
 apply (drule_tac x="s ^^^ <x>" in spec)
 apply (drule_tac x="t ^^^ <x>" in spec)

  (* no sync *)
  apply (case_tac "x ~= Tick & x ~: Ev ` X", simp)
  (* sync *)
  apply (simp add: par_tr_last)
  apply (erule disjE, simp)
  apply (force)

  apply (rotate_tac -2)
  apply (erule disjE, simp)
  apply (force)
  apply (simp)
  apply (force)

 (* => *)
 apply (force)

apply (rule conjI)

 (* show X1 Un ... = X2 Un ... *)
 apply (simp add: Parallel_F3_lm1)
 apply (rule Parallel_F3_lm2)
 apply (rule Parallel_F3_lm2)
 apply (simp)
 apply (force)
 apply (simp)

 (* condition 2 *)
 apply (rule_tac x="s" in exI)
 apply (rule_tac x="t" in exI)
 apply (simp)

 apply (simp add: domF_def HC_F3_def)
 apply (elim conjE)
 apply (drule_tac x="s" in spec)
 apply (drule_tac x="t" in spec)
 apply (drule_tac x="X1" in spec)
 apply (drule_tac x="X2" in spec)
 apply (drule_tac x=
   "{a. a : Y & (a = Tick | a : Ev ` X) & s ^^^ <a> ~:t traces(P) (fstF o M)} Un
    {a. a : Y & a ~= Tick & a ~: Ev ` X}" in spec)
 apply (drule_tac x=
   "{a. a : Y & (a = Tick | a : Ev ` X) & t ^^^ <a> ~:t traces(Q) (fstF o M)} Un
    {a. a : Y & a ~= Tick & a ~: Ev ` X}" in spec)
 apply (simp)

 (* left *)
 apply (drule mp)
  apply (intro allI impI)
  apply (drule_tac x="a" in spec, simp)
  apply (drule_tac x="s ^^^ <a>" in spec)
  apply (drule_tac x="t" in spec)
  apply (erule disjE)
  apply (simp add: par_tr_last)
  apply (fast)

  apply (erule disjE, simp)
  apply (simp add: HC_T2_def)
  apply (drule_tac x="s" in spec)
  apply (drule_tac x="t" in spec)
  apply (force)

 (* right *)
 apply (drule mp)
  apply (intro allI impI)
  apply (drule_tac x="a" in spec, simp)
  apply (drule_tac x="s" in spec)
  apply (drule_tac x="t ^^^ <a>" in spec)
  apply (erule disjE)
  apply (simp add: par_tr_last)
  apply (fast)

  apply (erule disjE)
  apply (simp add: HC_T2_def)
  apply (drule_tac x="s" in spec)
  apply (drule_tac x="t" in spec)
  apply (force)
  apply (simp)
 apply (simp)

(* notick s & notick t *)
apply (simp add: par_tr_noTick_decompo)
done

(* T3_F4 *)

lemma Parallel_T3_F4 :
  "[| (traces(P) (fstF o M), failures(P) M) : domF ; 
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> HC_T3_F4 (traces(P |[X]| Q) (fstF o M), failures(P |[X]| Q) M)"
apply (simp add: HC_T3_F4_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE)
apply (simp add: par_tr_last)
apply (elim conjE exE)
apply (rule conjI)

 (* F4 *)
 apply (rule_tac x="Evset" in exI)
 apply (rule_tac x="Evset" in exI)
 apply (simp)
 apply (rule_tac x="s'" in exI)
 apply (rule_tac x="t'" in exI)
 apply (simp add: domF_def HC_F4_def)

 (* T3 *)
 apply (rule allI)
 apply (rule_tac x="Xa" in exI)
 apply (rule_tac x="Xa" in exI)
 apply (simp)
 apply (rule_tac x="sa" in exI)
 apply (rule_tac x="t" in exI)
 apply (simp add: domF_def HC_T3_def)
 apply (fast)
done

(*** Parallel_domF ***)

lemma Parallel_domF :
  "[| (traces(P) (fstF o M), failures(P) M) : domF ; 
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> (traces(P |[X]| Q) (fstF o M), failures(P |[X]| Q) M) : domF"
apply (simp (no_asm) add: domF_iff)
apply (simp add: Parallel_T2)
apply (simp add: Parallel_F3)
apply (simp add: Parallel_T3_F4)
done

(*--------------------------------*
 |            Hiding              |
 *--------------------------------*)

(*** T2 ***)

lemma Hiding_T2 :
  "(traces(P) (fstF o M), failures(P) M) : domF
   ==> HC_T2 (traces(P -- X) (fstF o M), failures(P -- X) M)"
apply (simp add: HC_T2_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE)
apply (rule_tac x="sa" in exI)
apply (simp add: domF_def HC_T2_def)
apply (elim conjE)
apply (drule_tac x="sa" in spec)
by (force)

(*** F3 ***)

lemma Hiding_F3 :
  "(traces(P) (fstF o M), failures(P) M) : domF
   ==> HC_F3 (traces(P -- X) (fstF o M), failures(P -- X) M)"
apply (simp add: HC_F3_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE)
apply (rename_tac t Y Z s)
apply (rule_tac x="s" in exI, simp)

apply (simp add: domF_def HC_F3_def)
apply (elim conjE)
apply (drule_tac x="s" in spec)
apply (drule_tac x="Ev ` X Un Y" in spec)
apply (drule_tac x="Z - Ev ` X" in spec)
apply (simp)

apply (drule mp)
 apply (intro allI impI)
 apply (drule_tac x="a" in spec)
 apply (simp)

 apply (insert event_Tick_or_Ev)
 apply (drule_tac x="a" in spec)
 apply (erule disjE)
  (* Tick *)
  apply (drule_tac x="s ^^^ <Tick>" in spec)
  apply (simp)
  (* Ev *)
  apply (elim conjE exE)
  apply (drule_tac x="s ^^^ <Ev aa>" in spec)
  apply (simp)
  apply (subgoal_tac "aa ~: X", simp_all)
  apply (force)

apply (subgoal_tac "Ev ` X Un Y Un (Z - Ev ` X) = Ev ` X Un (Y Un Z)", simp)
by (auto)

(* T3_F4 *)

lemma Hiding_T3_F4 :
  "(traces(P) (fstF o M), failures(P) M) : domF
   ==> HC_T3_F4 (traces(P -- X) (fstF o M), failures(P -- X) M)"
apply (simp add: HC_T3_F4_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE)
apply (drule sym)
apply (simp add: hide_tr_decompo)
apply (elim conjE exE)
apply (rotate_tac -1)
apply (drule sym)

apply (subgoal_tac "(EX t''. t' = t'' ^^^ <Tick> & sett t'' <= Ev ` X)")
 apply (elim conjE exE)
 apply (simp)

 (* F4 *)
 apply (rule conjI)
  apply (rule_tac x="s' ^^^ t''" in exI)
  apply (simp)
  apply (subgoal_tac "t'' --tr X = <>", simp)
   apply (simp add: domF_def HC_F4_def)
   apply (elim conjE)
   apply (drule_tac x="s' ^^^ t''" in spec)
   apply (subgoal_tac "noTick t''")
    apply (simp add: appt_assoc)
   apply (simp add: noTick_def)
   apply (force)
  apply (simp add: hide_tr_nilt_sett)

 (* T3 *)
 apply (rule allI)
 apply (rule_tac x="sa" in exI, simp)
 apply (simp add: domF_def HC_T3_def)
 apply (elim conjE)
 apply (drule_tac x="s' ^^^ t''" in spec, simp)
 apply (subgoal_tac "noTick t''")
  apply (simp add: appt_assoc)
 apply (simp add: noTick_def)
 apply (force)

apply (auto simp add: hide_tr_Tick_sett)
done

(*** Hiding_domF ***)

lemma Hiding_domF :
  "(traces(P) (fstF o M), failures(P) M) : domF
   ==> (traces(P -- X) (fstF o M), failures(P -- X) M) : domF"
apply (simp (no_asm) add: domF_iff)
apply (simp add: Hiding_T2)
apply (simp add: Hiding_F3)
apply (simp add: Hiding_T3_F4)
done

(*--------------------------------*
 |           Renaming             |
 *--------------------------------*)

(*** T2 ***)

lemma Renaming_T2 :
  "(traces(P) (fstF o M), failures(P) M) : domF
   ==> HC_T2 (traces(P [[r]]) (fstF o M), failures(P [[r]]) M)"
apply (simp add: HC_T2_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE)
apply (rule_tac x="sa" in exI)
apply (simp add: domF_def HC_T2_def)
apply (elim conjE)
apply (drule_tac x="sa" in spec)
by (force)

(*** F3 ***)

lemma Renaming_F3 :
  "(traces(P) (fstF o M), failures(P) M) : domF
   ==> HC_F3 (traces(P [[r]]) (fstF o M), failures(P [[r]]) M)"
apply (simp add: HC_F3_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE)
apply (rule_tac x="sa" in exI, simp)

apply (simp add: domF_def HC_F3_def)
apply (elim conjE)
apply (drule_tac x="sa" in spec)
apply (drule_tac x="[[r]]inv X" in spec)
apply (drule_tac x="[[r]]inv Y" in spec)

apply (drule mp)
 apply (simp add: ren_tr_noTick_right)
 apply (intro allI impI)
 apply (simp add: ren_inv_def)
 apply (erule bexE)
 apply (fold ren_inv_def)
 apply (drule_tac x="eb" in spec, simp)

  (* Tick *)
  apply (erule disjE)
  apply (drule_tac x=" sa ^^^ <a>" in spec)
  apply (simp add: ren_tr_noTick_right)
  (* Ev *)
  apply (elim conjE exE)
  apply (drule_tac x=" sa ^^^ <Ev aa>" in spec)
  apply (simp add: ren_tr_noTick_right)
by (simp)

(* T3_F4 *)

lemma Renaming_T3_F4 :
  "(traces(P) (fstF o M), failures(P) M) : domF
   ==> HC_T3_F4 (traces(P [[r]]) (fstF o M), failures(P [[r]]) M)"
apply (simp add: HC_T3_F4_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE)
apply (simp add: ren_tr_appt_decompo)
apply (elim conjE exE)
apply (case_tac "~ noTick s1", simp)
apply (simp)

 (* F4 *)
 apply (rule conjI)
 apply (rule_tac x="s1" in exI, simp)
 apply (simp add: domF_def HC_F4_def)
 apply (elim conjE)
 apply (drule_tac x="s1" in spec, simp)
 apply (rule memF_F2, simp, simp)

 (* T3 *)
 apply (rule allI)
 apply (rule_tac x="s1 ^^^ <Tick>" in exI)
 apply (simp add: domF_def HC_T3_def)
 apply (fast)
done

(*** Renaming_domF ***)

lemma Renaming_domF :
  "(traces(P) (fstF o M), failures(P) M) : domF
   ==> (traces(P [[r]]) (fstF o M), failures(P [[r]]) M) : domF"
apply (simp (no_asm) add: domF_iff)
apply (simp add: Renaming_T2)
apply (simp add: Renaming_F3)
apply (simp add: Renaming_T3_F4)
done

(*--------------------------------*
 |           Seq_compo            |
 *--------------------------------*)

(*** T2 ***)

lemma Seq_compo_T2 :
  "[| (traces(P) (fstF o M), failures(P) M) : domF ; 
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> HC_T2 (traces(P ;; Q) (fstF o M), failures(P ;; Q) M)"
apply (simp add: HC_T2_def in_traces in_failures)
apply (intro allI)
apply (rule conjI)

 (* case 1 *)
 apply (intro impI)
 apply (rule disjI1)
 apply (rule_tac x="s" in exI, simp)
 apply (simp add: domF_def HC_T2_def)
 apply (elim conjE)
 apply (drule_tac x="s" in spec)
 apply (force)

 (* case 2 *)
 apply (intro impI)
 apply (elim conjE exE disjE)
 apply (rule disjI2)
 apply (rule_tac x="sa" in exI)
 apply (rule_tac x="t" in exI)
 apply (simp add: domF_def HC_T2_def)
 apply (elim conjE)
 apply (rotate_tac 4)
 apply (drule_tac x="t" in spec)
 apply (force)
done

(*** F3 ***)

lemma Seq_compo_F3 :
  "[| (traces(P) (fstF o M), failures(P) M) : domF ; 
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> HC_F3 (traces(P ;; Q) (fstF o M), failures(P ;; Q) M)"
apply (simp add: HC_F3_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE disjE)

 (* case 1 *)
 apply (simp add: domF_def HC_F3_def)
 apply (elim conjE)
 apply (drule_tac x="s" in spec)
 apply (drule_tac x="insert Tick X" in spec)
 apply (drule_tac x="Y-{Tick}" in spec)
 apply (simp)
 apply (drule mp)
  apply (intro allI impI)
  apply (drule_tac x="a" in spec, simp)
  apply (simp add: not_Tick_to_Ev)
  apply (elim conjE exE, simp)
  apply (rotate_tac -3)
  apply (drule_tac x="s ^^^ <Ev aa>" in spec, simp)
 apply (subgoal_tac 
   "insert Tick (X Un (Y - {Tick})) = insert Tick (X Un Y)", simp)
 apply (force)

 (* case 2 *)
 apply (simp add: domF_def HC_F3_def)
 apply (elim conjE)
 apply (rotate_tac -2)
 apply (drule_tac x="t" in spec)
 apply (drule_tac x="X" in spec)
 apply (drule_tac x="Y" in spec)
 apply (simp)
 apply (drule mp)
  apply (intro allI impI)
  apply (drule_tac x="a" in spec, simp)
  apply (elim conjE)
  apply (rotate_tac -1)
  apply (drule_tac x="sa" in spec)
  apply (rotate_tac -1)
  apply (drule_tac x="t ^^^ <a>" in spec)
  apply (simp add: appt_assoc)
 apply (rule disjI2)
 apply (rule_tac x="sa" in exI)
 apply (rule_tac x="t" in exI)
 apply (simp)
done

(* T3_F4 *)

lemma Seq_compo_T3_F4 :
  "[| (traces(P) (fstF o M), failures(P) M) : domF ; 
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> HC_T3_F4 (traces(P ;; Q) (fstF o M), failures(P ;; Q) M)"
apply (simp add: HC_T3_F4_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE disjE)

 (* case 1 *)
 apply (elim conjE exE)
 apply (subgoal_tac "noTick (s ^^^ <Tick>) ~= noTick (rmTick sa)", simp)
 apply (simp (no_asm_use))
 apply (drule sym)
 apply (simp)

 (* case 2 *)
 apply (elim conjE exE)
 apply (case_tac "~ noTick sa", simp)
 apply (insert trace_last_nil_or_unnil)
 apply (drule_tac x="t" in spec)
 apply (simp)
  (* <> *)
  apply (erule disjE)
  apply (rotate_tac -5)
  apply (drule_tac sym, simp)   (* contradict *)

  (* ... <Tick> *)
  apply (elim conjE exE, simp)
  apply (simp add: appt_assoc_sym)
  apply (erule conjE)
  apply (rule conjI)

   (* F4 *)
   apply (rule disjI2)
   apply (rule_tac x="sa" in exI)
   apply (rule_tac x="sb" in exI)
   apply (simp add: domF_def HC_F4_def)

   (* T3 *)
   apply (rule allI)
   apply (rule_tac x="sa" in exI)
   apply (rule_tac x="t" in exI)
   apply (simp add: appt_assoc_sym domF_def HC_T3_def)
done

(*** Seq_compo_domF ***)

lemma Seq_compo_domF :
  "[| (traces(P) (fstF o M), failures(P) M) : domF ; 
      (traces(Q) (fstF o M), failures(Q) M) : domF |]
     ==> (traces(P ;; Q) (fstF o M), failures(P ;; Q) M) : domF"
apply (simp (no_asm) add: domF_iff)
apply (simp add: Seq_compo_T2)
apply (simp add: Seq_compo_F3)
apply (simp add: Seq_compo_T3_F4)
done

(*--------------------------------*
 |          Depth_rest            |
 *--------------------------------*)

(*** T2 ***)

lemma Depth_rest_T2 :
  "(traces(P) (fstF o M), failures(P) M) : domF
   ==> HC_T2 (traces(P |. n) (fstF o M), failures(P |. n) M)"
apply (simp add: HC_T2_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE)
apply (simp add: domF_def HC_T2_def)
apply (elim conjE)
apply (drule_tac x="s" in spec)
by (force)

(*** F3 ***)

lemma Depth_rest_F3 :
  "(traces(P) (fstF o M), failures(P) M) : domF
   ==> HC_F3 (traces(P |. n) (fstF o M), failures(P |. n) M)"
apply (simp add: HC_F3_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE)

apply (simp add: domF_def HC_F3_def)
apply (elim conjE)
apply (drule_tac x="s" in spec)
apply (drule_tac x="X" in spec)
apply (drule_tac x="Y" in spec)
apply (simp)
apply (erule disjE)
apply (simp)
apply (simp)
apply (elim conjE exE)
apply (simp)
done

(* T3_F4 *)

lemma Depth_rest_T3_F4 :
  "(traces(P) (fstF o M), failures(P) M) : domF
   ==> HC_T3_F4 (traces(P |. n) (fstF o M), failures(P |. n) M)"
apply (simp add: HC_T3_F4_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE exE)
apply (simp)

 (* F4 *)
 apply (rule conjI)
 apply (simp add: domF_def HC_F4_def)

 (* T3 *)
 apply (simp add: domF_def HC_T3_def)
 apply (case_tac "Suc (lengtht s) < n")
 apply (simp)
 apply (simp)
 apply (fast)
done

(*** Depth_rest_domF ***)

lemma Depth_rest_domF :
  "(traces(P) (fstF o M), failures(P) M) : domF
   ==> (traces(P |. n) (fstF o M), failures(P |. n) M) : domF"
apply (simp (no_asm) add: domF_iff)
apply (simp add: Depth_rest_T2)
apply (simp add: Depth_rest_F3)
apply (simp add: Depth_rest_T3_F4)
done

(*--------------------------------*
 |        Proc_name_dom           |
 *--------------------------------*)

(*** T2 ***)

lemma Proc_name_T2 :
  "HC_T2 (traces ($p) (fstF o M), failures ($p) M)"
apply (simp add: HC_T2_def in_traces in_failures)
apply (intro allI impI)
apply (elim exE)
apply (simp add: pairF_domF_T2)
done

(*** F3 ***)

lemma Proc_name_F3 :
  "HC_F3 (traces ($p) (fstF o M), failures ($p) M)"
apply (simp add: HC_F3_def in_traces in_failures)
apply (intro allI impI)
apply (simp add: pairF_domF_F3)
done

(* T3_F4 *)

lemma Proc_name_T3_F4 :
  "HC_T3_F4 (traces ($p) (fstF o M), failures ($p) M)"
apply (simp add: HC_T3_F4_def in_traces in_failures)
apply (intro allI impI)
apply (simp add: pairF_domF_T3)
apply (simp add: pairF_domF_F4)
done

(*** Proc_name_domF ***)

lemma Proc_name_domF :
  "(traces ($p) (fstF o M), failures ($p) M) : domF"
apply (simp (no_asm) add: domF_iff)
apply (simp add: Proc_name_T2)
apply (simp add: Proc_name_F3)
apply (simp add: Proc_name_T3_F4)
done

(*--------------------------------*
 |             proc               |
 *--------------------------------*)

declare o_apply [simp del]

lemma proc_domF[simp]: "(traces(P) (fstF o M), failures(P) M) : domF"
apply (induct_tac P)
apply (simp add: STOP_domF)
apply (simp add: SKIP_domF)
apply (simp add: DIV_domF)
apply (simp add: Act_prefix_domF)
apply (simp add: Ext_pre_choice_domF)
apply (simp add: Ext_choice_domF)
apply (simp add: Int_choice_domF)
apply (simp add: Rep_int_choice_domF)
apply (simp add: IF_domF)
apply (simp add: Parallel_domF)
apply (simp add: Hiding_domF)
apply (simp add: Renaming_domF)
apply (simp add: Seq_compo_domF)
apply (simp add: Depth_rest_domF)
apply (simp add: Proc_name_domF)
done

declare o_apply [simp]

(*--------------------------------*
 |          fstF sndF             |
 *--------------------------------*)

lemma fstF_proc_domF[simp]:
   "fstF (traces(P) (fstF o M),, failures(P) M) = traces(P) (fstF o M)"
by (simp add: pairF)

lemma sndF_proc_domF[simp]:
   "sndF (traces(P) (fstF o M),, failures(P) M) = failures(P) M"
by (simp add: pairF)

lemma fstF_proc_domF2[simp]:
   "fstF (traces(P) (%x. fstF (M x)),, failures(P) M) = traces(P) (fstF o M)"
apply (fold comp_def)
apply (simp)
done

lemma sndF_proc_domF2[simp]:
   "sndF (traces(P) (%x. fstF (M x)),, failures(P) M) = failures(P) M"
apply (fold comp_def)
apply (simp)
done

lemma fstF_proc_domF_fun:
   "fstF o (%p. (traces(f p) (fstF o M),, failures(f p) M))
     = (%p. traces(f p) (fstF o M))"
apply (unfold comp_def)
apply (fold comp_def)
apply (simp add: fun_eq_iff)
done

lemma sndF_proc_domF_fun:
   "sndF o (%p. (traces(f p) (fstF o M),, failures(f p) M))
     = (%p.  failures(f p) M)"
apply (unfold comp_def)
apply (fold comp_def)
apply (simp add: fun_eq_iff)
done

lemma fstF_semFf[simp]: "fstF ([[P]]Ff M) = traces(P) (fstF o M)"
by (simp add: semFf_def)

lemma fstF_semF[simp]: "fstF ([[P]]F) = traces(P) (fstF o MF)"
by (simp add: semF_def)

lemma sndF_semFf[simp]: "sndF ([[P]]Ff M) = failures(P) M"
by (simp add: semFf_def)

lemma sndF_semF[simp]: "sndF ([[P]]F) = failures(P) MF"
by (simp add: semF_def)

(*** decomposition ***)

lemma semFf_decompo:
  "([[P]]Ff M = SF) = ((traces P (fstF o M) = fstF SF) &
                        failures P M = sndF SF)"
apply (simp add: semFf_def)
apply (rule)
apply (drule sym)
apply (simp)
apply (simp)
done

lemma semF_decompo:
  "([[P]]F = SF) = ((traces P (fstF o MF) = fstF SF) &
                     failures P MF = sndF SF)"
apply (simp add: semF_def)
apply (simp add: semFf_decompo)
done

lemma semFf_decompo_fstF:
  "([[P]]Ff M = SF) ==> traces P (fstF o M) = fstF SF"
by (simp add: semFf_decompo)

lemma semF_decompo_fstF:
  "([[P]]F = SF) ==> traces P (fstF o MF) = fstF SF"
by (simp add: semF_decompo)

lemma semFf_decompo_sndF:
  "([[P]]Ff M = SF) ==>  failures P M = sndF SF"
by (simp add: semFf_decompo)

lemma semF_decompo_sndF:
  "([[P]]F = SF) ==>  failures P MF = sndF SF"
by (simp add: semF_decompo)

(*--------------------------------*
 |            [[$p]]Ff            |
 *--------------------------------*)

lemma semFf_Proc_name: "[[$p]]Ff = (%M. M p)"
apply (simp add: semFf_def)
apply (simp add: traces_iff)
apply (simp add: failures_iff)
done

(*--------------------------------*
 |          =F and <=F            |
 *--------------------------------*)

lemma cspF_eqF_semantics:
  "(P =F[M1,M2] Q) = 
       ((traces P (fstF o M1) = traces Q (fstF o M2)) & 
        (failures P M1 = failures Q M2))"
apply (simp add: eqF_def)
apply (simp add: semFf_def)
apply (simp add: eqF_decompo)
done

lemma cspF_refF_semantics:
  "(P <=F[M1,M2] Q) = 
       ((traces Q (fstF o M2) <= traces P (fstF o M1)) & 
        (failures Q M2 <= failures P M1))"
apply (simp add: refF_def)
apply (simp add: semFf_def)
apply (simp add: subdomF_decompo)
done

lemmas cspF_semantics = cspF_eqF_semantics  cspF_refF_semantics

lemma cspF_cspT_eqF_semantics:
  "(P =F[M1,M2] Q) = 
       ((P =T[fstF o M1,fstF o M2] Q) & 
        (failures P M1 = failures Q M2))"
apply (simp add: cspF_eqF_semantics)
apply (simp add: eqT_def)
apply (simp add: semTf_def)
done

lemma cspF_cspT_refF_semantics:
  "(P <=F[M1,M2] Q) = 
       ((P <=T[fstF o M1,fstF o M2] Q) & 
        (failures Q M2 <= failures P M1))"
apply (simp add: cspF_refF_semantics)
apply (simp add: refT_def)
apply (simp add: semTf_def)
done

lemmas cspF_cspT_semantics = cspF_cspT_eqF_semantics  cspF_cspT_refF_semantics

(*--------------------------------*
 |            Timeout             |
 *--------------------------------*)

lemma in_failures_Timeout1: 
  "(f :f failures(P [> Q) M) =
   (f :f failures(Q) M |
   (EX s X. f = (s, X) & s ~= <> & (s, X) :f failures(P) M) |
   (EX X. f = (<>, X) & X <= Evset & <Tick> :t traces(P) (fstF o M)))"
apply (rule)

(* <= *)
 apply (simp add: in_failures)
 apply (elim conjE exE disjE)
 apply (simp_all)
 apply (simp add: in_traces)
 apply (rule disjI1)
 apply (rule domF_F2_F4, simp_all)

 (* <= *)
 apply (simp add: in_failures in_traces)
 apply (elim conjE exE disjE, simp_all)
 apply (auto elim: memF_pairE)
done

lemma in_failures_Timeout2:
  "(f :f failures(P [>def Q) M) =
   (f :f failures(Q) M |
   (EX s X. f = (s, X) & s ~= <> & (s, X) :f failures(P) M) |
   (EX X. f = (<>, X) & X <= Evset & <Tick> :t traces(P) (fstF o M)))"
apply (simp add: Timeout_def)
apply (simp add: in_failures_Timeout1)
done

lemmas in_failures_Timeout = in_failures_Timeout1 in_failures_Timeout2

(*--------------------------------*
 |           Depth rest           |
 *--------------------------------*)

lemma semFf_Depth_rest: "[[P |. n]]Ff M = [[P]]Ff M .|. n"
apply (simp add: semFf_def)
apply (simp add: traces.simps)
apply (simp add: failures.simps)
apply (simp add: rest_domF_def)
apply (simp add: restTF_def)
apply (simp add: pairF_def)
apply (simp add: Abs_domF_inverse)
apply (simp add: pair_restriction_def)
done

lemma semF_Depth_rest: "[[P |. n]]F = [[P]]F .|. n"
apply (simp add: semF_def)
apply (simp add: semFf_Depth_rest)
done

(*---------------------------------------------------*
 |         Healthiness conditions for proc           |
 *---------------------------------------------------*)

lemma proc_T2:
    "(s, X) :f failures(P) M ==> s :t traces(P) (fstF o M)"
apply (insert pairF_domF_T2[of "s" "X" "(traces(P) (fstF o M),, failures(P) M)"])
by (simp)

lemma proc_T3:
  "[| s ^^^ <Tick> :t traces(P) (fstF o M); noTick s |]
   ==> (s ^^^ <Tick>, X) :f failures(P) M"
apply (insert pairF_domF_T3[of "s" "(traces(P) (fstF o M),, failures(P) M)" "X"])
by (simp)

lemma proc_T3_Tick:
  "<Tick> :t traces(P) (fstF o M) ==> (<Tick>, X) :f failures(P) M"
apply (insert proc_T3[of "<>" P M X])
by (simp)

lemma proc_F4:
  "[| s ^^^ <Tick> :t traces(P) (fstF o M) ; noTick s |]
   ==> (s, Evset) :f failures(P) M"
apply (insert pairF_domF_F4[of "s" "(traces(P) (fstF o M),, failures(P) M)"])
by (simp)

lemma proc_F3:
  "[| (s, X) :f failures(P) M ; noTick s ;
      (ALL a. a : Y --> s ^^^ <a> ~:t  traces(P) (fstF o M)) |]
   ==> (s, X Un Y) :f  failures(P) M"
apply (insert pairF_domF_F3[of "s" "X" "(traces(P) (fstF o M),, failures(P) M)" "Y"])
by (simp)

lemma proc_F3I:
  "[| (s, X) :f failures(P) M ; noTick s ;
      (ALL a. a : Y --> s ^^^ <a> ~:t traces(P) (fstF o M)) ;
      Z = X Un Y |]
   ==> (s, Z) :f failures(P) M"
by (simp add: proc_F3)

(*** F2_F4 ***)

lemma proc_F2_F4:
  "[| s ^^^ <Tick> :t traces(P) (fstF o M) ; noTick s ; X <= Evset|]
   ==> (s, X) :f failures(P) M"
apply (insert pairF_domF_F2_F4[of "s" "(traces(P) (fstF o M),, failures(P) M)" "X"])
by (simp)

(*** T2_T3 ***)

lemma proc_T2_T3:
  "[| (s ^^^ <Tick>, X) :f failures(P) M ; noTick s |] 
  ==> (s ^^^ <Tick>, Y) :f failures(P) M"
apply (rule proc_T3)
apply (rule proc_T2)
by (simp_all)

(*------------------------------------------------------*
 |   Union in domF  (used for generic internal choice   |
 *------------------------------------------------------*)

lemma non_empty_UnionT_UnionF_T2:
 "Ps ~= {} ==>
  HC_T2 (UnionT {(traces P (fstF o M)) |P. P : Ps} , 
         UnionF {(failures P M) |P. P : Ps})"
apply (simp add: HC_T2_def)
apply (intro allI impI)
apply (subgoal_tac "{(traces P (fstF o M)) |P. P : Ps} ~= {}")
apply (simp)
apply (elim conjE bexE exE)
apply (simp)
apply (rule_tac x="traces Pa (fstF o M)" in exI)
apply (rule conjI)
apply (rule_tac x="Pa" in exI)
apply (simp)
apply (simp add: proc_T2)
by (auto)

lemma non_empty_UnionT_UnionF_F3:
 "Ps ~= {} ==>
  HC_F3 (UnionT {(traces P (fstF o M)) |P. P : Ps} , 
         UnionF {(failures P M) |P. P : Ps})"
apply (simp add: HC_F3_def)
apply (intro allI impI)
apply (subgoal_tac "{(traces P (fstF o M)) |P. P : Ps} ~= {}")
apply (simp)
apply (elim conjE exE)
apply (simp)
apply (rule_tac x="failures Pa M" in exI)
apply (rule conjI)
apply (rule_tac x="Pa" in exI)
apply (simp)
apply (rule proc_F3)
apply (simp_all)
apply (intro allI impI)
apply (drule_tac x="a" in spec)
apply (simp)
apply (drule_tac x="traces Pa  (fstF o M)" in spec)
apply (erule disjE)
apply (drule_tac x="Pa" in spec)
apply (simp)
apply (simp)
apply (auto)
done

lemma non_empty_UnionT_UnionF_T3_F4:
 "Ps ~= {} ==>
  HC_T3_F4 (UnionT {(traces P (fstF o M)) |P. P : Ps} , 
            UnionF {(failures P M) |P. P : Ps})"
apply (simp add: HC_T3_F4_def)
apply (intro allI impI)
apply (subgoal_tac "{(traces P (fstF o M)) |P. P : Ps} ~= {}")
apply (simp)
apply (elim conjE bexE exE)
apply (simp)
apply (rule conjI)
 apply (rule_tac x="failures Pa M" in exI)
 apply (rule conjI)
 apply (fast)
 apply (rule proc_F4)
 apply (simp_all)

 apply (rule allI)
 apply (rule_tac x="failures Pa M" in exI)
 apply (rule conjI)
 apply (fast)
 apply (rule proc_T3)
 apply (simp_all)
by (auto)

lemma non_empty_UnionT_UnionF_domF:
 "Ps ~= {} ==>
  (UnionT {(traces P (fstF o M)) |P. P : Ps} , 
   UnionF {(failures P M) |P. P : Ps}) : domF"
apply (simp (no_asm) add: domF_iff)
apply (simp add: non_empty_UnionT_UnionF_T2)
apply (simp add: non_empty_UnionT_UnionF_F3)
apply (simp add: non_empty_UnionT_UnionF_T3_F4)
done

(*------------------------------------------------------*
 |   Union in domF  (used for generic internal choice   |
 *------------------------------------------------------*)

lemma UnionT_UnionF_T2:
 "HC_T2 ({t. t = <> | (EX P:Ps. t :t traces(P) (fstF o M)) }t ,
         {f. EX P:Ps. f :f failures(P) M}f )"
apply (simp add: HC_T2_def)
apply (intro allI impI)
apply (simp add: in_traces_Union_proc)
apply (simp add: in_failures_Union_proc)
apply (elim conjE bexE exE)
apply (rule disjI2)
apply (rule_tac x="P" in bexI)
apply (simp add: proc_T2)
apply (simp)
done

lemma UnionT_UnionF_F3:
 "HC_F3 ({t. t = <> | (EX P:Ps. t :t traces(P) (fstF o M)) }t ,
         {f. EX P:Ps. f :f failures(P) M}f )"
apply (simp add: HC_F3_def)
apply (intro allI impI)
apply (simp add: in_traces_Union_proc)
apply (simp add: in_failures_Union_proc)
apply (elim conjE bexE exE)
apply (simp)
apply (rule_tac x="P" in bexI)
apply (rule proc_F3)
apply (simp_all)
done

lemma UnionT_UnionF_T3_F4:
 "HC_T3_F4 ({t. t = <> | (EX P:Ps. t :t traces(P) (fstF o M)) }t ,
            {f. EX P:Ps. f :f failures(P) M}f )"
apply (simp add: HC_T3_F4_def)
apply (intro allI impI)
apply (simp add: in_traces_Union_proc)
apply (simp add: in_failures_Union_proc)
apply (elim conjE bexE exE)
apply (simp)
apply (elim bexE)
apply (rule conjI)
 apply (rule_tac x="P" in bexI)
 apply (rule proc_F4)
 apply (simp_all)

 apply (rule allI)
 apply (rule_tac x="P" in bexI)
 apply (rule proc_T3)
 apply (simp_all)
done

lemma UnionT_UnionF_domF:
 "({t. t = <> | (EX P:Ps. t :t traces(P) (fstF o M)) }t ,
            {f. EX P:Ps. f :f failures(P) M}f) : domF"
apply (simp (no_asm) add: domF_iff)
apply (simp add: UnionT_UnionF_T2)
apply (simp add: UnionT_UnionF_F3)
apply (simp add: UnionT_UnionF_T3_F4)
done

(*-----------------------------------------*
 |              substitution               |
 *-----------------------------------------*)

lemma semF_subst:
  "[[P<<f]]F = [[P]]Ff (%q. [[f q]]F)"
apply (induct_tac P)
apply (simp add: semF_def semFf_def,
       simp add: eqF_decompo,
       simp add: traces_iff failures_iff)+
done

lemma semF_subst_semFfun:
  "(%q. [[ (Pf q)<<f ]]F) = ([[Pf]]Ffun (%q. [[f q]]F))"
apply (simp add: semFfun_def)
apply (simp add: fun_eq_iff)
apply (rule allI)
apply (simp add: semF_subst)
done

lemma failrues_subst:
  "failures(P<<f) M = failures P (%q. [[f q]]Ff M)"
apply (induct_tac P)
apply (simp_all add: semF_def semFf_def traces_iff failures_iff)+
apply (simp add: fstF_proc_domF_fun)
apply (simp add: traces_subst)

apply (simp add: fstF_proc_domF_fun)
apply (simp add: traces_subst)
done

(*-----------------------------------------*
 |               semT -- semF              |
 *-----------------------------------------*)

lemma semTfun_fstF_semFf:
  "[[Pf]]Tfun (fstF o M) p = fstF ([[Pf p]]Ff M)"
apply (simp add: semTfun_def)
apply (simp add: semTf_def)
done

(****************** to add them again ******************)

declare disj_not1   [simp]

end
