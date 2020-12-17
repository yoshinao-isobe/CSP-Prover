           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               December 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_law_step_ext
imports CSP_T_law_basic
begin

(*****************************************************************

         1. step laws
         2.
         3. 
         4. 

 *****************************************************************)

(*********************************************************
             Parallel expansion & distribution
 *********************************************************)

lemma cspT_Parallel_Timeout_split:
  "((? :Y -> Pf) [> P) |[X]| ((? :Z -> Qf) [> Q) =T[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [> Q))
                                        |~| (((? x:Y -> Pf x) [> P) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [> Q))
               ELSE (((? x:Y -> Pf x) [> P) |[X]| Qf x))
     [> (((P |[X]| ((? :Z -> Qf) [> Q)) |~|
         (((? :Y -> Pf) [> P) |[X]| Q)))"
apply (fold Timeout_def)
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces_Timeout in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)
  apply (force)
  apply (force)
  apply (force)
  apply (force)

  apply (simp add: par_tr_head_Ev_Ev)
  apply (elim conjE exE disjE)

   apply (simp)
   apply (rule disjI1)
   apply (rule_tac x="c" in exI)
   apply (rule_tac x="v" in exI)
   apply (force)

   apply (simp)
   apply (rule disjI1)
   apply (rule_tac x="c" in exI)
   apply (rule_tac x="v" in exI)
   apply (force)

   apply (simp)
   apply (rule disjI1)
   apply (rule_tac x="c" in exI)
   apply (rule_tac x="v" in exI)
   apply (force)

  apply (force)
  apply (force)
  apply (force)

(* <= *)
 apply (rule)
 apply (simp add: in_traces_Timeout in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)

  apply (simp add: in_traces)
  apply (elim conjE exE)
  apply (rule_tac x="<Ev a> ^^^ sa" in exI)
  apply (rule_tac x="<Ev a> ^^^ ta" in exI)
  apply (simp add: par_tr_head)

  apply (simp add: in_traces_IF)
  apply (case_tac "a : Z")

  (* a : Z *)
   apply (simp add: in_traces_Timeout in_traces)
   apply (elim conjE exE disjE)
   apply (simp_all)

    apply (simp add: par_tr_nil_right)
    apply (rule_tac x="<Ev a> ^^^ sa" in exI)
    apply (rule_tac x="<>" in exI)
    apply (simp add: par_tr_nil_right)
    apply (force)

    apply (rule_tac x="<Ev a> ^^^ sa" in exI)
    apply (rule_tac x="ta" in exI)
    apply (simp add: par_tr_head)

    apply (rule_tac x="<Ev a> ^^^ sa" in exI)
    apply (rule_tac x="ta" in exI)
    apply (simp add: par_tr_head)

    apply (rule_tac x="sa" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_head)

    apply (rule_tac x="sa" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_head)

    apply (rule_tac x="sa" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_head)

  (* a ~: Z *)
   apply (simp add: in_traces_Timeout in_traces)
   apply (elim conjE exE disjE)

    apply (simp add: par_tr_nil_right)
    apply (rule_tac x="<Ev a> ^^^ sa" in exI)
    apply (rule_tac x="<>" in exI)
    apply (simp add: par_tr_nil_right)
    apply (force)

    apply (rule_tac x="<Ev a> ^^^ sa" in exI)
    apply (rule_tac x="ta" in exI)
    apply (simp add: par_tr_head)

    apply (rule_tac x="<Ev a> ^^^ sa" in exI)
    apply (rule_tac x="ta" in exI)
    apply (simp add: par_tr_head)

  apply (simp add: in_traces_IF)
  apply (case_tac "a : Y")

  (* a : Y *)
   apply (simp add: in_traces_Timeout in_traces)
   apply (elim conjE exE disjE)
   apply (simp_all)

    apply (simp add: par_tr_nil_right)
    apply (rule_tac x="<Ev a> ^^^ sa" in exI)
    apply (rule_tac x="<>" in exI)
    apply (simp add: par_tr_nil_right)
    apply (force)

    apply (rule_tac x="<Ev a> ^^^ sa" in exI)
    apply (rule_tac x="ta" in exI)
    apply (simp add: par_tr_head)

    apply (rule_tac x="<Ev a> ^^^ sa" in exI)
    apply (rule_tac x="ta" in exI)
    apply (simp add: par_tr_head)

    apply (rule_tac x="sa" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_head)

    apply (rule_tac x="sa" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_head)

    apply (rule_tac x="sa" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_head)

  (* a ~:Y *)
   apply (simp add: in_traces_Timeout in_traces)
   apply (elim conjE exE disjE)

    apply (simp add: par_tr_nil_left)
    apply (rule_tac x="<>" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_nil_left)
    apply (force)

    apply (rule_tac x="sa" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_head)

    apply (rule_tac x="sa" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_head)

  (* *)
  apply (force)
  apply (force)
  apply (force)
  apply (force)
  apply (force)
  apply (force)
done

(*********************************************************
            Parallel expansion & distribution 2
 *********************************************************)

lemma cspT_Parallel_Timeout_input_l: 
  "((? :Y -> Pf) [> P) |[X]| (? :Z -> Qf) =T[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| (? x:Z -> Qf x))
                                        |~| (((? x:Y -> Pf x) [> P) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| (? x:Z -> Qf x))
               ELSE (((? x:Y -> Pf x) [> P) |[X]| Qf x))
     [> (((P |[X]| (? :Z -> Qf))))"
apply (fold Timeout_def)
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces_Timeout in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)

  apply (simp add: par_tr_nil_left)
  apply (rule disjI1)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="sa" in exI)
  apply (elim conjE)
  apply (simp add: image_iff)
  apply (case_tac "a:Y")
   apply (simp)
   apply (rule disjI2)
   apply (rule_tac x="<>" in exI)
   apply (rule_tac x="sa" in exI)
   apply (simp add: par_tr_nil_left)

   apply (simp)
   apply (rule_tac x="<>" in exI)
   apply (rule_tac x="sa" in exI)
   apply (simp add: par_tr_nil_left)

  apply (simp add: par_tr_nil_right)
  apply (rule disjI1)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="sa" in exI)
  apply (elim conjE)
  apply (simp add: image_iff)
  apply (case_tac "a:Z")
   apply (simp)
   apply (rule disjI1)
   apply (rule_tac x="sa" in exI)
   apply (rule_tac x="<>" in exI)
   apply (simp add: par_tr_nil_right)

   apply (simp)
   apply (rule_tac x="sa" in exI)
   apply (rule_tac x="<>" in exI)
   apply (simp add: par_tr_nil_right)

  apply (force)

  apply (simp add: par_tr_head_Ev_Ev)
  apply (elim conjE exE disjE)

   apply (simp)
   apply (rule disjI1)
   apply (rule_tac x="c" in exI)
   apply (rule_tac x="v" in exI)
   apply (force)

   apply (simp)
   apply (rule disjI1)
   apply (rule_tac x="c" in exI)
   apply (rule_tac x="v" in exI)
   apply (force)

   apply (simp)
   apply (rule disjI1)
   apply (rule_tac x="c" in exI)
   apply (rule_tac x="v" in exI)
   apply (force)

  apply (force)

(* <= *)
 apply (rule)
 apply (simp add: in_traces_Timeout in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)

  apply (simp add: in_traces)
  apply (elim conjE exE)
  apply (rule_tac x="<Ev a> ^^^ sa" in exI)
  apply (rule_tac x="<Ev a> ^^^ ta" in exI)
  apply (simp add: par_tr_head)

  apply (simp add: in_traces_IF)
  apply (case_tac "a : Z")

  (* a : Z *)
   apply (simp add: in_traces_Timeout in_traces)
   apply (elim conjE exE disjE)
   apply (simp_all)

    apply (simp add: par_tr_nil_right)
    apply (rule_tac x="<Ev a> ^^^ sa" in exI)
    apply (rule_tac x="<>" in exI)
    apply (simp add: par_tr_nil_right)
    apply (force)

    apply (rule_tac x="<Ev a> ^^^ sa" in exI)
    apply (rule_tac x="ta" in exI)
    apply (simp add: par_tr_head)

    apply (rule_tac x="<>" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_head)

    apply (rule_tac x="<Ev aa> ^^^ sb" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_head)

    apply (rule_tac x="sa" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_head)

  (* a ~: Z *)
   apply (simp add: in_traces_Timeout in_traces)
   apply (elim conjE exE disjE)

    apply (simp add: par_tr_nil_right)
    apply (rule_tac x="<Ev a> ^^^ sa" in exI)
    apply (rule_tac x="<>" in exI)
    apply (simp add: par_tr_nil_right)
    apply (force)

    apply (rule_tac x="<Ev a> ^^^ sa" in exI)
    apply (rule_tac x="ta" in exI)
    apply (simp add: par_tr_head)

  apply (simp add: in_traces_IF)
  apply (case_tac "a : Y")

  (* a : Y *)
   apply (simp add: in_traces_Timeout in_traces)
   apply (elim conjE exE disjE)
   apply (simp_all)

    apply (simp add: par_tr_nil_right)
    apply (rule_tac x="<Ev a> ^^^ sa" in exI)
    apply (rule_tac x="<>" in exI)
    apply (simp add: par_tr_nil_right)
    apply (force)

    apply (rule_tac x="<Ev a> ^^^ sa" in exI)
    apply (rule_tac x="ta" in exI)
    apply (simp add: par_tr_head)

    apply (simp add: par_tr_nil_left)
    apply (rule_tac x="<>" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_nil_left)
    apply (force)

    apply (rule_tac x="<Ev aa> ^^^ sb" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_head)

    apply (rule_tac x="sa" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_head)

  (* a ~:Y *)
   apply (simp add: in_traces_Timeout in_traces)
   apply (elim conjE exE disjE)

    apply (simp add: par_tr_nil_left)
    apply (rule_tac x="<>" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_nil_left)
    apply (force)

    apply (rule_tac x="sa" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_head)

    apply (rule_tac x="sa" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_head)

  (* *)
  apply (force)
  apply (force)
done

lemma cspT_Parallel_Timeout_input_r: 
  "(? :Y -> Pf) |[X]| ((? :Z -> Qf) [> Q) =T[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [> Q))
                                        |~| ((? x:Y -> Pf x) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [> Q))
               ELSE ((? x:Y -> Pf x) |[X]| Qf x))
     [> ((((? :Y -> Pf) |[X]| Q)))"
apply (rule cspT_rw_left)
apply (rule cspT_commut)

apply (rule cspT_rw_left)
apply (rule cspT_Parallel_Timeout_input_l)

apply (rule cspT_decompo)
apply (rule cspT_decompo)
apply (rule cspT_decompo)
apply (force)

apply (case_tac "a : X")
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_IF)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (rule cspT_commut)

apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_IF)
apply (rule cspT_rw_right)
apply (rule cspT_IF)

apply (case_tac "(a : Z & a : Y)")
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_IF)
apply (rule cspT_rw_right)
apply (rule cspT_IF)

apply (rule cspT_rw_left)
apply (rule cspT_commut)
apply (rule cspT_decompo)
apply (rule cspT_rw_left)
apply (rule cspT_commut)
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_commut)
apply (simp)

apply (simp (no_asm_simp))
apply (rule cspT_rw_left)
apply (rule cspT_IF)
apply (subgoal_tac "~(a : Y & a : Z)")
apply (simp (no_asm_simp))
apply (rule cspT_rw_right)
apply (rule cspT_IF)

apply (case_tac "a : Z")
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_IF)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (rule cspT_commut)
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_IF)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (rule cspT_commut)

apply (fast)
apply (simp)
apply (rule cspT_commut)
done

lemmas cspT_Parallel_Timeout_input = 
       cspT_Parallel_Timeout_input_l
       cspT_Parallel_Timeout_input_r

(*** cspT_step_ext ***)

lemmas cspT_step_ext = cspT_Parallel_Timeout_split
                       cspT_Parallel_Timeout_input

end
