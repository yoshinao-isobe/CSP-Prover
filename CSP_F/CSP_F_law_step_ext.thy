           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               December 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_law_step_ext
imports CSP_F_law_basic CSP_T.CSP_T_law_step_ext
begin

(*****************************************************************

         1. step laws
         2.
         3. 
         4. 

 *****************************************************************)

(*********************************************************
              (P1 [> P2) |[X]| (Q1 [> Q2)
 *********************************************************)

(* The following law in p.288 does not hold.                               *)
(*     (P1 [> P2) |[X]| (Q1 [> Q2)                                         *)
(*  =F (P1 |[X]| Q1) [> ((P2 |[X]| (Q1 [> Q2)) |~| ((P1 [> P2) |[X]| Q2))  *)
(*                                                                         *)
(* a counter example:                                                      *)
(*  P1 = a -> STOP, P2 = STOP, Q1 = STOP, Q2 = b -> STOP, X = {}           *)
(*  where (a ~= b)                                                         *)
(*                                                                         *)
(*  check the following lemmas                                             *)

lemma "a ~= b ==>
       (<Ev a>, {(Ev b)}) ~:f 
        failures ((a -> STOP [> STOP) |[{}]| (STOP [> (b -> STOP))) M"
apply (simp add: in_failures in_traces)
apply (intro allI impI)
apply (simp add: par_tr_Ev)
apply (erule disjE)
apply (auto)
done

lemma "(<Ev a>, {(Ev b)}) :f
       failures (((a -> STOP) |[{}]| STOP) [> 
                 ((STOP |[{}]| (STOP [> (b -> STOP))) |~| 
                  (((a -> STOP [> STOP) |[X]| (b -> STOP))))) M"
apply (simp add: in_failures in_traces)
apply (rule disjI1)
apply (rule_tac x="{(Ev b)}" in exI)
apply (rule_tac x="{(Ev b)}" in exI)
apply (simp)
apply (rule_tac x="<Ev a>" in exI)
apply (simp add: par_tr_nil_right)
done

(*********************************************************
              (P [> Q) |[X]| (? :Y -> Rf)
 *********************************************************)

(* The following law in p.289 does not hold.                               *)
(*                                                                         *)
(*     (P [> Q) |[X]| (? :Y -> Rf) =F[M,M]                                      *)
(*     (? x:(Y - X) -> ((P [> Q) |[X]| Rf x))                              *)
(*     [+] ((P |[X]| (? :Y -> Rf)) [> (Q |[X]| (? :Y -> Rf)))              *)
(*                                                                         *)
(* a counter example:                                                      *)
(*  P = STOP, Q = b -> STOP, Y = {a}, Rf = (%x. STOP), X = {}              *)
(*  where (a ~= b)                                                         *)
(*                                                                         *)
(*  check the following lemmas                                             *)

lemma "a ~= b ==>
      (<Ev a>, {(Ev b)}) ~:f  
       failures ((STOP [> (b -> STOP)) |[{}]| (? x:{a} -> STOP)) M"
apply (simp add: in_failures in_traces)
apply (intro allI impI)
apply (simp add: par_tr_Ev)
apply (erule disjE)
apply (auto)
done

lemma "a ~= b ==>
       (<Ev a>, {(Ev b)}) :f 
        failures ((? x:({a} - {}) -> ((STOP [>  (b -> STOP)) |[{}]| STOP))
                  [+] ((STOP |[{}]| (? x:{a} -> STOP)) 
                       [> ((b -> STOP) |[{}]| (? x:{a} -> STOP)))) M"
apply (fold Timeout_def)
apply (simp add: in_failures in_failures_Timeout in_traces)
apply (rule disjI2)
apply (rule disjI2)
apply (rule_tac x="{(Ev b)}" in exI)
apply (rule_tac x="{(Ev b)}" in exI)
apply (simp)
apply (rule_tac x="<Ev a>" in exI)
apply (simp add: par_tr_nil_left)
done

(*********************************************************
              Parallel expansion & distribbution
 *********************************************************)

lemma cspF_Parallel_Timeout_split:
  "((? :Y -> Pf) [> P) |[X]| ((? :Z -> Qf) [> Q) =F[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [> Q))
                                        |~| (((? x:Y -> Pf x) [> P) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [> Q))
               ELSE (((? x:Y -> Pf x) [> P) |[X]| Qf x))
     [> (((P |[X]| ((? :Z -> Qf) [> Q)) |~|
         (((? :Y -> Pf) [> P) |[X]| Q)))"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Parallel_Timeout_split)
apply (fold Timeout_def)
apply (rule order_antisym)

 (* => *)
 apply (rule)
 apply (simp add: in_failures_Timeout in_failures)
 apply (elim disjE conjE exE)
 apply (simp_all)

  apply (force)

  apply (rule disjI1)
  apply (rule_tac x="Y" in exI)
  apply (rule_tac x="Za" in exI)
  apply (simp)
  apply (rule_tac x="sa" in exI)
  apply (rule_tac x="<Ev a> ^^^ sb" in exI)
  apply (simp)

  apply (rule disjI1)
  apply (rule_tac x="Y" in exI)
  apply (rule_tac x="Za" in exI)
  apply (simp)
  apply (rule_tac x="sa" in exI)
  apply (rule_tac x="<>" in exI)
  apply (simp)

  apply (rule disjI2)
  apply (rule disjI1)
  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Z" in exI)
  apply (simp)
  apply (rule_tac x="<Ev a> ^^^ sb" in exI)
  apply (rule_tac x="t" in exI)
  apply (simp)

  apply (rule disjI2)
  apply (rule disjI1)
  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Z" in exI)
  apply (simp)
  apply (rule_tac x="<>" in exI)
  apply (rule_tac x="t" in exI)
  apply (simp)

  (* main part *)

  apply (case_tac "s = <>", simp, simp)
  apply (rule disjI2)
  apply (rule disjI2)
  apply (simp add: par_tr_head_Ev_Ev)
  apply (elim exE disjE)
  apply (rule_tac x="c" in exI)
  apply (rule_tac x="v" in exI)
  apply (elim conjE disjE)

   (* sync *)
   apply (simp)
   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (force)

   (* left *)
   apply (simp)
   apply (case_tac "c:Z")

    apply (simp)
    apply (rule disjI1)
    apply (rule_tac x="Ya" in exI)
    apply (rule_tac x="Za" in exI)
    apply (force)

    apply (simp)
    apply (rule_tac x="Ya" in exI)
    apply (rule_tac x="Za" in exI)
    apply (force)

   (* right *)
   apply (simp)
   apply (case_tac "c:Y")

    apply (simp)
    apply (rule disjI2)
    apply (rule_tac x="Ya" in exI)
    apply (rule_tac x="Za" in exI)
    apply (force)

    apply (simp)
    apply (rule_tac x="Ya" in exI)
    apply (rule_tac x="Za" in exI)
    apply (force)

  (* others *)

  apply (simp add: in_traces)
  apply (simp add: in_traces)
  apply (simp add: in_traces)

(* <= *)
 apply (rule)
 apply (simp add: in_failures_Timeout in_failures)
 apply (elim conjE exE disjE)
 apply (simp_all)

  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Za" in exI)
  apply (force)

  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Za" in exI)
  apply (force)

  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Za" in exI)
  apply (force)

  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Za" in exI)
  apply (force)

  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Za" in exI)
  apply (force)

  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Za" in exI)
  apply (force)

  (* main part *)

  (* sync *)
  apply (simp add: in_failures_Parallel)
  apply (elim disjE conjE exE)
  apply (simp)
  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Za" in exI)
  apply (simp)
  apply (rule_tac x="<Ev a> ^^^ sb" in exI)
  apply (rule_tac x="<Ev a> ^^^ t" in exI)
  apply (simp add: par_tr_head)

  (* no_sync *)
  apply (simp add: in_failures_IF)
  apply (case_tac "a:Z")

  apply (simp add: in_failures_Timeout in_failures)
  apply (elim disjE conjE exE)
  apply (simp_all)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI)
   apply (simp add: par_tr_head)

  (* a ~: Z *)
  apply (simp add: in_failures_Timeout in_failures)
  apply (elim disjE conjE exE)
  apply (simp_all)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="t" in exI)
   apply (simp add: par_tr_head)

  apply (simp add: in_traces)

  (* no_sync *)
  apply (simp add: in_failures_IF)
  apply (case_tac "a:Y")

  apply (simp add: in_failures_Timeout in_failures)
  apply (elim disjE conjE exE)
  apply (simp_all)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI)
   apply (simp add: par_tr_head)

  (* a ~: Y *)
  apply (simp add: in_failures_Timeout in_failures)
  apply (elim disjE conjE exE)
  apply (simp_all)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI)
   apply (simp add: par_tr_head)

 (* others *)

 apply (simp add: in_traces)
done

(*********************************************************
            Parallel expansion & distribbution 2
 *********************************************************)

(*** left ****)

lemma cspF_Parallel_Timeout_input_l: 
  "((? :Y -> Pf) [> P) |[X]| (? :Z -> Qf) =F[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| (? x:Z -> Qf x))
                                        |~| (((? x:Y -> Pf x) [> P) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| (? x:Z -> Qf x))
               ELSE (((? x:Y -> Pf x) [> P) |[X]| Qf x))
     [> (((P |[X]| (? :Z -> Qf))))"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Parallel_Timeout_input)
apply (fold Timeout_def)
apply (rule order_antisym)

 (* => *)
 apply (rule)
 apply (simp add: in_failures_Timeout in_failures)
 apply (elim disjE conjE exE)
 apply (simp_all)

  apply (force)

  apply (rule disjI1)
  apply (rule_tac x="Y" in exI)
  apply (rule_tac x="Za" in exI)
  apply (simp)
  apply (rule_tac x="sa" in exI)
  apply (rule_tac x="<Ev a> ^^^ sb" in exI)
  apply (simp)

  apply (simp add: par_tr_nil_right)
  apply (rule disjI2)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="sb" in exI)
  apply (elim conjE)
  apply (simp add: image_iff)
  apply (case_tac "a : Z")
   apply (simp)
   apply (rule disjI1)
   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<>" in exI)
   apply (simp add: par_tr_nil_right)

   apply (simp)
   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<>" in exI)
   apply (simp add: par_tr_nil_right)

  apply (simp add: in_traces)

  (* main part *)

  apply (case_tac "s = <>", simp, simp)
  apply (rule disjI2)
  apply (simp add: par_tr_head_Ev_Ev)
  apply (elim exE disjE)
  apply (rule_tac x="c" in exI)
  apply (rule_tac x="v" in exI)
  apply (elim conjE disjE)

   (* sync *)
   apply (simp)
   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (force)

   (* left *)
   apply (simp)
   apply (case_tac "c:Z")

    apply (simp)
    apply (rule disjI1)
    apply (rule_tac x="Ya" in exI)
    apply (rule_tac x="Za" in exI)
    apply (force)

    apply (simp)
    apply (rule_tac x="Ya" in exI)
    apply (rule_tac x="Za" in exI)
    apply (force)

   (* right *)
   apply (simp)
   apply (case_tac "c:Y")

    apply (simp)
    apply (rule disjI2)
    apply (rule_tac x="Ya" in exI)
    apply (rule_tac x="Za" in exI)
    apply (force)

    apply (simp)
    apply (rule_tac x="Ya" in exI)
    apply (rule_tac x="Za" in exI)
    apply (force)

  (* others *)

  apply (simp add: in_traces)

(* <= *)
 apply (rule)
 apply (simp add: in_failures_Timeout in_failures)
 apply (elim conjE exE disjE)
 apply (simp_all)

  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Za" in exI)
  apply (simp)
  apply (rule_tac x="sa" in exI)
  apply (rule_tac x="<>" in exI)
  apply (simp)

  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Za" in exI)
  apply (force)

  (* main part *)

  (* sync *)
  apply (simp add: in_failures_Parallel)
  apply (elim disjE conjE exE)
  apply (simp)
  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Za" in exI)
  apply (simp)
  apply (rule_tac x="<Ev a> ^^^ sb" in exI)
  apply (rule_tac x="<Ev a> ^^^ t" in exI)
  apply (simp add: par_tr_head)

  (* no_sync *)
  apply (simp add: in_failures_IF)
  apply (case_tac "a:Z")

  apply (simp add: in_failures_Timeout in_failures)
  apply (elim disjE conjE exE)
  apply (simp_all)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev aa> ^^^ sc" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI)
   apply (simp add: par_tr_head)

   apply (simp add: in_traces)

  (* a ~: Z *)
  apply (simp add: in_failures_Timeout in_failures)
  apply (elim disjE conjE exE)
  apply (simp_all)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="<>" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="t" in exI)
   apply (simp add: par_tr_head)

  apply (simp add: in_traces)

  (* no_sync *)
  apply (simp add: in_failures_IF)
  apply (case_tac "a:Y")

  apply (simp add: in_failures_Timeout in_failures)
  apply (elim disjE conjE exE)
  apply (simp_all)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="<Ev aa> ^^^ sc" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev aa> ^^^ sc" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI)
   apply (simp add: par_tr_head)

   apply (simp add: in_traces)

  (* a ~: Y *)
  apply (simp add: in_failures_Timeout in_failures)
  apply (elim disjE conjE exE)
  apply (simp_all)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev aa> ^^^ sc" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI)
   apply (simp add: par_tr_head)

   apply (simp add: in_traces)

 (* others *)

 apply (simp add: in_traces)
done

(*** right ****)

lemma cspF_Parallel_Timeout_input_r: 
  "(? :Y -> Pf) |[X]| ((? :Z -> Qf) [> Q) =F[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [> Q))
                                        |~| ((? x:Y -> Pf x) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [> Q))
               ELSE ((? x:Y -> Pf x) |[X]| Qf x))
     [> ((? :Y -> Pf) |[X]| Q)"
apply (rule cspF_rw_left)
apply (rule cspF_commut)
apply (rule cspF_rw_left)
apply (rule cspF_Parallel_Timeout_input_l)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (force)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_commut)

apply (case_tac "a : Z & a : Y")
apply (simp)
apply (rule cspF_rw_left)
apply (rule cspF_IF_True)
apply (rule cspF_rw_right)
apply (rule cspF_IF_True)
apply (rule cspF_rw_left)
apply (rule cspF_commut)
apply (rule cspF_decompo)
apply (rule cspF_commut)
apply (rule cspF_commut)

apply (simp (no_asm_simp))
apply (rule cspF_rw_left)
apply (rule cspF_IF_False)
apply (rule cspF_rw_right)
apply (subgoal_tac "~ (a : Y & a : Z)")
apply (simp (no_asm_simp))
apply (rule cspF_IF_False)
apply (force)

apply (case_tac "a : Z")
apply (simp)
apply (rule cspF_rw_left)
apply (rule cspF_IF_True)
apply (rule cspF_rw_right)
apply (rule cspF_IF_False)
apply (rule cspF_commut)
apply (simp)
apply (rule cspF_rw_left)
apply (rule cspF_IF_False)
apply (rule cspF_rw_right)
apply (rule cspF_IF_True)
apply (rule cspF_commut)

apply (rule cspF_reflex)
apply (rule cspF_commut)
done

lemmas cspF_Parallel_Timeout_input
     = cspF_Parallel_Timeout_input_l
       cspF_Parallel_Timeout_input_r

(*** cspF_step_ext ***)

lemmas cspF_step_ext = cspF_Parallel_Timeout_split
                       cspF_Parallel_Timeout_input

end
