           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_law_step
imports CSP_T_traces
begin

(*****************************************************************

         1. step laws
         2.
         3. 
         4. 

 *****************************************************************)

(*********************************************************
                    stop expansion
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_STOP_step: "STOP =T[M1,M2] ? :{} -> Pf"
apply (simp add: cspT_semantics)
apply (simp add: traces_iff)
done

(* to avoide producing free variables (Pf) in tactics *)

lemma cspT_STOP_step_DIV: "STOP =T[M1,M2] ? x:{} -> DIV"
apply (simp add: cspT_semantics)
apply (simp add: traces_iff)
done

(*********************************************************
                    Act_prefix expansion
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Act_prefix_step: "a -> P =T[M,M] ? x:{a} -> P"
apply (simp add: cspT_semantics)
apply (simp add: traces_iff)
done

(*********************************************************
                    Ext choice expansion
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Ext_choice_step:
  "(? :X -> Pf) [+] (? :Y -> Qf) =T[M,M]
      ? x:(X Un Y) -> 
                (IF (x : X & x : Y) THEN (Pf x |~| Qf x)
                 ELSE IF (x : X) THEN Pf x
                 ELSE Qf x)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE)
 apply (simp_all)

 apply (rule_tac x="a" in exI)
 apply (rule_tac x="s" in exI)
 apply (simp)

 apply (rule_tac x="a" in exI)
 apply (rule_tac x="s" in exI)
 apply (simp)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE)
 apply (simp_all)

 apply (case_tac "a : Y")
 apply (simp_all add: in_traces)

 apply (case_tac "a : X")
 apply (simp_all add: in_traces)
done

(*********************************************************
                    Parallel expansion
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Parallel_step: 
  "(? :Y -> Pf) |[X]| (? :Z -> Qf) =T[M,M]
      ? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ? x:Z -> Qf x)
                                     |~| (? x:Y -> Pf x |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ? x:Z -> Qf x)
               ELSE (? x:Y -> Pf x |[X]| Qf x)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (insert trace_nil_or_Tick_or_Ev)
 apply (drule_tac x="t" in spec)
 apply (elim disjE conjE exE)

 (* <> *)
  apply (simp)

 (* [Tick]t *)
  apply (simp add: in_traces)

 (* [Ev .]t *)
  apply (simp add: in_traces)
  apply (elim disjE conjE exE)

  (* 1 *)
  apply (simp)

  (* 2 *)
  apply (simp add: par_tr_head)
  apply (elim conjE exE)
  apply (case_tac "a : Y")
   apply (simp)
   apply (rule disjI2)
   apply (rule_tac x="<>" in exI)
   apply (rule_tac x="sb" in exI)
   apply (simp)
   (* a ~: Y *)
   apply (simp)
   apply (rule_tac x="<>" in exI)
   apply (rule_tac x="sb" in exI)
   apply (simp)

  (* 3 *)
  apply (simp add: par_tr_head)
  apply (elim conjE exE)
  apply (case_tac "a : Z")
   apply (simp)
   apply (rule disjI1)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<>" in exI)
   apply (simp)
   (* a ~: Z *)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<>" in exI)
   apply (simp)

  (* 4 *)
  apply (simp add: par_tr_head)
  apply (elim disjE conjE exE)

   (* 4-1 *)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="sc" in exI)
   apply (simp)

   (* 4-2 *)
   apply (case_tac "a : Z")
    apply (simp)
    apply (rule disjI1)
    apply (rule_tac x="sb" in exI)
    apply (rule_tac x="<Ev ab> ^^^ sc" in exI)
    apply (simp)
    (* a ~: Z *)
    apply (simp)
    apply (rule_tac x="sb" in exI)
    apply (rule_tac x="<Ev ab> ^^^ sc" in exI)
    apply (simp)

   (* 4-3 *)
   apply (simp)
   apply (case_tac "a : Y")
    apply (simp)
    apply (rule disjI2)
    apply (rule_tac x="<Ev aa> ^^^ sb" in exI)
    apply (rule_tac x="sc" in exI)
    apply (simp)
    (* a ~: Y *)
    apply (simp)
    apply (rule_tac x="<Ev aa> ^^^ sb" in exI)
    apply (rule_tac x="sc" in exI)
    apply (simp)

(* <= *)
 apply (rule)+
 apply (drule_tac x="t" in spec)
 apply (elim disjE conjE exE)

 (* <> *)
  apply (simp)

 (* [Tick]t *)
  apply (simp add: in_traces)

 (* [Ev .]t *)
  apply (simp add: in_traces)
  apply (elim disjE conjE exE)

  (* 1 *)
  apply (simp add: in_traces)
  apply (elim conjE exE)
  apply (rule_tac x="<Ev a> ^^^ sa" in exI)
  apply (rule_tac x="<Ev a> ^^^ ta" in exI)
  apply (simp add: par_tr_head)

  (* 2 *)
  apply (simp add: in_traces)
  apply (case_tac "a : Z")
   apply (simp add: in_traces)
   apply (erule disjE)

    apply (elim conjE exE)
    apply (rule_tac x="<Ev a> ^^^ sa" in exI)
    apply (rule_tac x="ta" in exI)
    apply (simp add: par_tr_head)

    apply (elim conjE exE)
    apply (rule_tac x="sa" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_head)

  (* 3 *)
  apply (simp add: in_traces)
  apply (elim conjE exE)

   apply (rule_tac x="<Ev a> ^^^ sa" in exI)
   apply (rule_tac x="ta" in exI)
   apply (simp add: par_tr_head)

   apply (simp add: in_traces)
   apply (case_tac "a : Y")

    apply (simp add: in_traces)
    apply (erule disjE)
     apply (elim conjE exE)
     apply (rule_tac x="<Ev a> ^^^ sa" in exI)
     apply (rule_tac x="ta" in exI)
     apply (simp add: par_tr_head)
     (* *)
     apply (elim conjE exE)
     apply (rule_tac x="sa" in exI)
     apply (rule_tac x="<Ev a> ^^^ ta" in exI)
     apply (simp add: par_tr_head)

    apply (simp add: in_traces)
    apply (elim conjE exE)
    apply (rule_tac x="sa" in exI)
    apply (rule_tac x="<Ev a> ^^^ ta" in exI)
    apply (simp add: par_tr_head)
done

(*********************************************************
                      Hide expansion
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Hiding_step: 
  "(? :Y -> Pf) -- X =T[M,M]
      IF (Y Int X = {}) THEN (? x:Y -> (Pf x -- X))
                         ELSE ((? x:(Y-X) -> (Pf x -- X)) 
                               [> (! x:(Y Int X) .. (Pf x -- X)))"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

 (* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE)
 apply (erule disjE, simp)
 apply (elim conjE exE)

 apply (case_tac "Y Int X = {}")
  apply (simp)
  apply (case_tac "a : X", fast)
  apply (simp)
  apply (rule_tac x="sa" in exI)
  apply (simp)

  (* Y Int X ~= {} *)
  apply (simp)
  apply (case_tac "a : X")
   apply (simp)
   apply (fast)
  (* a ~: X *)
   apply (simp)
   apply (fast)

 (* <= *)
 apply (rule)
 apply (case_tac "Y Int X = {}")
  apply (simp add: in_traces)
  apply (erule disjE, simp)
   apply (rule_tac x="<>" in exI)
   apply (simp)

  apply (elim conjE exE)
  apply (case_tac "a : X", fast)
   apply (rule_tac x="<Ev a> ^^^ sa" in exI)
   apply (simp)

 (* Y Int X = {} *)
  apply (simp add: in_traces)
  apply (erule disjE, simp)
   apply (rule_tac x="<>" in exI)
   apply (simp)

  apply (erule disjE)
  (* a~:X *)
   apply (elim conjE exE)
   apply (rule_tac x="<Ev a> ^^^ sa" in exI)
   apply (simp)
  (* a:X *)
   apply (erule disjE, simp)
    apply (rule_tac x="<>" in exI)
    apply (simp)

   apply (elim conjE exE bexE)
   apply (rule_tac x="<Ev a> ^^^ s" in exI)
   apply (simp)
done

(*********************************************************
                    Renaming expansion
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Renaming_step:
  "(? :X -> Pf) [[r]] =T[M,M]
    ? y:(r `` X) -> (! x:{x. x:X & (x,y):r} .. (Pf x)[[r]])"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE)
  (* 1 *)
  apply (simp)

  (* 2 *)
  apply (rule disjI2)
  apply (simp add: ren_tr_decompo)
  apply (elim conjE exE)
  apply (rule_tac x="b" in exI)
  apply (rule_tac x="ta" in exI)
  apply (simp)
  apply (fast)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (erule disjE, simp)
 apply (elim disjE conjE exE)
  apply (simp add: Image_iff)
  apply (erule bexE)
  apply (rule_tac x="<Ev x>" in exI)
  apply (simp)
 (* *)
  apply (rule_tac x="<Ev aa> ^^^ sa" in exI)
  apply (simp)
done

(*********************************************************
            Sequential composition expansion
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Seq_compo_step: 
  "(? :X -> Pf) ;; Q =T[M,M] ? x:X -> (Pf x ;; Q)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)

  (* 1 *)
 apply (fast)

  (* 2 *)
 apply (insert trace_last_nil_or_unnil)
 apply (drule_tac x="sa" in spec)
 apply (erule disjE, simp)
 apply (elim conjE exE, simp)
 apply (simp add: appt_assoc_sym)
 apply (rule_tac x="a" in exI)
 apply (rule_tac x="sb ^^^ ta" in exI)
 apply (simp add: appt_assoc)
 apply (fast)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (erule disjE, simp)
 apply (rule disjI1)
 apply (rule_tac x="<>" in exI)
 apply (simp)
 apply (elim disjE conjE exE)

 (* 1 *)
  apply (rule disjI1)
  apply (rule_tac x="<Ev a> ^^^ sa" in exI, simp)

 (* 2 *)
  apply (rule disjI2)
  apply (rule_tac x="<Ev a> ^^^ sa" in exI)
  apply (rule_tac x="ta" in exI)
  apply (simp add: appt_assoc)
done

(*********************************************************
                    Depth_rest expansion
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Depth_rest_step:
  "(? :X -> Pf) |. (Suc n) =T[M,M] ? x:X -> (Pf x |. n)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE)
 apply (simp_all)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE)
 apply (simp_all)
done

(*********************************************************)

lemmas cspT_step = cspT_STOP_step       cspT_Act_prefix_step 
                   cspT_Ext_choice_step cspT_Parallel_step
                   cspT_Hiding_step     cspT_Renaming_step
                   cspT_Seq_compo_step  cspT_Depth_rest_step

lemmas cspT_light_step = cspT_STOP_step  cspT_Act_prefix_step 

lemmas cspT_step_rw = cspT_STOP_step_DIV       cspT_Act_prefix_step 
                   cspT_Ext_choice_step cspT_Parallel_step
                   cspT_Hiding_step     cspT_Renaming_step
                   cspT_Seq_compo_step  cspT_Depth_rest_step

lemmas cspT_light_step_rw = cspT_STOP_step_DIV  cspT_Act_prefix_step 

end
