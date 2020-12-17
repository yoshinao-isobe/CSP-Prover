           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_law_SKIP
imports CSP_T_law_basic
begin

(*****************************************************************

         1. SKIP |[X]| SKIP
         2. SKIP |[X]| P
         3. P |[X]| SKIP
         4. SKIP -- X
         5. SKIP [[r]]
         6. SKIP ;; P
         7. P ;; SKIP
         8. SKIP |. n

 *****************************************************************)

(*********************************************************
                    SKIP |[X]| SKIP
 *********************************************************)

lemma cspT_Parallel_term:
   "SKIP |[X]| SKIP =T[M1,M2] SKIP"
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

(*********************************************************
                      SKIP |[X]| P
 *********************************************************)

lemma cspT_Parallel_preterm_l: 
   "SKIP |[X]| (? :Y -> Qf) =T[M,M] ? x:(Y-X) -> (SKIP |[X]| Qf x)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (insert trace_nil_or_Tick_or_Ev)
 apply (elim disjE conjE exE)
  apply (simp_all)

  apply (drule_tac x="t" in spec)
  apply (erule disjE, simp)
  apply (erule disjE, simp)
  apply (elim conjE exE, simp)
  apply (simp add: par_tr_head)
  apply (rule_tac x="<>" in exI)
  apply (rule_tac x="sa" in exI, simp)

  apply (drule_tac x="t" in spec)
  apply (erule disjE, simp)
  apply (erule disjE, simp)
  apply (elim conjE exE, simp)
  apply (simp add: par_tr_head)
  apply (rule_tac x="<Tick>" in exI)
  apply (rule_tac x="sa" in exI, simp)

(* <= *)

 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE)
  apply (simp_all)

  apply (rule_tac x="<>" in exI)
  apply (rule_tac x="<Ev a> ^^^ ta" in exI, simp)
  apply (simp add: par_tr_head)

  apply (rule_tac x="<Tick>" in exI)
  apply (rule_tac x="<Ev a> ^^^ ta" in exI, simp)
  apply (simp add: par_tr_head)
done

(*********************************************************
                      P |[X]| SKIP
 *********************************************************)

lemma cspT_Parallel_preterm_r: 
   "(? :Y -> Pf) |[X]| SKIP
     =T[M,M] ? x:(Y-X) -> (Pf x |[X]| SKIP)"
apply (rule cspT_trans)
apply (rule cspT_Parallel_commut)
apply (rule cspT_trans)
apply (rule cspT_Parallel_preterm_l)
apply (rule cspT_rm_head, simp)
apply (rule cspT_Parallel_commut)
done

lemmas cspT_Parallel_preterm = cspT_Parallel_preterm_l cspT_Parallel_preterm_r

(*********************************************************
                      SKIP and Parallel
 *********************************************************)

(* p.288 *)

lemma cspT_SKIP_Parallel_Ext_choice_SKIP_l:
  "((? :Y -> Pf) [+] SKIP) |[X]| SKIP =T[M,M] 
   (? x:(Y - X) -> (Pf x |[X]| SKIP)) [+] SKIP"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)

  apply (rule disjI2)
  apply (rule disjI1)
  apply (simp add: par_tr_nil_right)
  apply (elim conjE)
  apply (simp add: image_iff)
  apply (rule_tac x="sa" in exI)
  apply (rule_tac x="<>" in exI)
  apply (simp add: par_tr_nil_right)

  apply (rule disjI2)
  apply (rule disjI1)
  apply (simp add: par_tr_Tick_right)
  apply (elim conjE)
  apply (simp add: image_iff)
  apply (rule_tac x="sa" in exI)
  apply (rule_tac x="<Tick>" in exI)
  apply (simp add: par_tr_Tick_right)

(* <= *)
 apply (rule, simp add: in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)

  apply (simp add: par_tr_nil_right)
  apply (elim conjE)
  apply (rule_tac x="<Ev a> ^^^ sa" in exI)
  apply (rule_tac x="<>" in exI)
  apply (simp add: par_tr_nil_right)
  apply (simp add: image_iff)

  apply (simp add: par_tr_Tick_right)
  apply (elim conjE)
  apply (rule_tac x="<Ev a> ^^^ sa" in exI)
  apply (rule_tac x="<Tick>" in exI)
  apply (simp add: par_tr_Tick_right)
  apply (simp add: image_iff)
done

lemma cspT_SKIP_Parallel_Ext_choice_SKIP_r:
  "SKIP |[X]| ((? :Y -> Pf) [+] SKIP)  =T[M,M] 
   (? x:(Y - X) -> (SKIP |[X]| Pf x)) [+] SKIP"
apply (rule cspT_rw_left)
apply (rule cspT_commut)
apply (rule cspT_rw_left)
apply (rule cspT_SKIP_Parallel_Ext_choice_SKIP_l)
apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_commut)
apply (rule cspT_reflex)
apply (rule cspT_reflex)
done

lemmas cspT_SKIP_Parallel_Ext_choice_SKIP =
       cspT_SKIP_Parallel_Ext_choice_SKIP_l
       cspT_SKIP_Parallel_Ext_choice_SKIP_r

(*********************************************************
                      SKIP -- X
 *********************************************************)

lemma cspT_SKIP_Hiding_Id: 
   "SKIP -- X =T[M1,M2] SKIP"
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
 apply (rule_tac x="<>" in exI)
 apply (simp)
 apply (rule_tac x="<Tick>" in exI)
 apply (simp)
done

(*********************************************************
                      SKIP and Hiding
 *********************************************************)

(*           p.288 version 

  "((? :Y -> Pf) [+] SKIP) -- X =T[M1,M2] 
       IF (Y Int X = {}) THEN ((? x:Y -> (Pf x -- X)) [+] SKIP)
                         ELSE (((? x:(Y-X) -> (Pf x -- X)) [+] SKIP)
                               |~| (! x:(Y Int X) .. (Pf x -- X)))"
*)

lemma cspT_SKIP_Hiding_step:
  "((? :Y -> Pf) [+] SKIP) -- X =T[M,M] 
   ((? x:(Y-X) -> (Pf x -- X)) [+] SKIP) |~| (! x:(Y Int X) .. (Pf x -- X))"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)

  apply (case_tac "a : X", force)
  apply (force)

(* <= *)
 apply (rule)

  apply (simp add: in_traces)
  apply (elim conjE exE bexE disjE)
  apply (simp_all)

   apply (force)

   apply (rule_tac x="<Ev a> ^^^ sa" in exI)
   apply (simp)

   apply (force)

   apply (rule_tac x="<Tick>" in exI)
   apply (simp)

   apply (force)

   apply (rule_tac x="<Ev a> ^^^ s" in exI)
   apply (simp)
done

(*********************************************************
                      SKIP [[r]]
 *********************************************************)

lemma cspT_SKIP_Renaming_Id: 
   "SKIP [[r]] =T[M1,M2] SKIP"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (force)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (force)
done

(*********************************************************
                       SKIP ;; P
 *********************************************************)

lemma cspT_Seq_compo_unit_l: "SKIP ;; P =T[M,M] P"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces)
 apply (force)

(* <= *)
 apply (rule, simp add: in_traces)
 apply (rule disjI2)
 apply (rule_tac x="<>" in exI)
 apply (rule_tac x="t" in exI)
 apply (simp)
done

(*********************************************************
                       P ;; SKIP
 *********************************************************)

lemma cspT_Seq_compo_unit_r: "P ;; SKIP =T[M,M] P"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)
 apply (rule memT_prefix_closed, simp)
 apply (simp add: rmTick_prefix_rev)
 apply (rule memT_prefix_closed, simp, simp)

(* <= *)
 apply (rule, simp add: in_traces)
 apply (insert trace_last_noTick_or_Tick)
 apply (drule_tac x="t" in spec)
 apply (erule disjE)
  apply (rule disjI1)
  apply (rule_tac x="t" in exI, simp)
  (* *)
  apply (rule disjI2)
  apply (elim conjE exE)
  apply (rule_tac x="s" in exI)
  apply (rule_tac x="<Tick>" in exI)
  apply (simp)
done

lemmas cspT_Seq_compo_unit = cspT_Seq_compo_unit_l cspT_Seq_compo_unit_r

(*********************************************************
               SKIP and Sequential composition
 *********************************************************)

(* p.141 *)

lemma cspT_SKIP_Seq_compo_step:
  "((? :X -> Pf) [> SKIP) ;; Q =T[M,M] (? x:X -> (Pf x ;; Q)) [> Q"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces)

 apply (elim conjE exE disjE)
 apply (simp_all)

  apply (rule disjI1)
  apply (fast)

  apply (rule disjI2)
  apply (rule disjI1)
  apply (insert trace_nil_or_Tick_or_Ev)
  apply (drule_tac x="s" in spec)

  apply (elim disjE conjE exE)
  apply (simp_all)

  apply (simp add: appt_assoc)
  apply (rule disjI2)

  apply (rule_tac x="sb" in exI)
  apply (rule_tac x="ta" in exI)
  apply (simp)

(* <= *)
 apply (rule, simp add: in_traces)

 apply (elim conjE exE disjE)
 apply (simp_all)

 apply (rule disjI1)
 apply (rule_tac x="<>" in exI)
 apply (simp)

 apply (rule disjI1)
 apply (rule_tac x="<Ev a> ^^^ sa" in exI)
 apply (simp)

 apply (rule disjI2)
 apply (rule_tac x="<Ev a> ^^^ sa" in exI)
 apply (rule_tac x="ta" in exI)
 apply (simp add: appt_assoc)

 apply (rule disjI1)
 apply (rule_tac x="<>" in exI)
 apply (simp)

 apply (rule disjI2)
 apply (rule_tac x="<>" in exI)
 apply (rule_tac x="t" in exI)
 apply (simp)
done

(*********************************************************
                      SKIP |. n
 *********************************************************)

lemma cspT_SKIP_Depth_rest: 
   "SKIP |. (Suc n) =T[M1,M2] SKIP"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (force)
done

(*********************************************************
                      cspT_SKIP
 *********************************************************)

lemmas cspT_SKIP =
       cspT_Parallel_term
       cspT_Parallel_preterm
       cspT_SKIP_Parallel_Ext_choice_SKIP
       cspT_SKIP_Hiding_Id
       cspT_SKIP_Hiding_step
       cspT_SKIP_Renaming_Id
       cspT_Seq_compo_unit
       cspT_SKIP_Seq_compo_step
       cspT_SKIP_Depth_rest

(*********************************************************
                       P [+] SKIP
 *********************************************************)

(* p.141 *)

lemma cspT_Ext_choice_SKIP_resolve: "P [+] SKIP =T[M,M] P [> SKIP"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces)

(* <= *)
 apply (rule, simp add: in_traces)
done

lemma cspT_Ext_choice_SKIP_resolve_sym: "P [> SKIP =T[M,M] P [+] SKIP"
apply (rule cspT_sym)
apply (simp add: cspT_Ext_choice_SKIP_resolve)
done

(*********************************************************
                    SKIP ||| P
 *********************************************************)

lemma cspT_Interleave_unit_l: 
  "SKIP ||| P =T[M,M] P"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE)
 apply (simp add: par_tr_nil_left)
 apply (simp add: par_tr_Tick_left)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (case_tac "noTick t")

  apply (rule_tac x="<>" in exI)
  apply (rule_tac x="t" in exI)
  apply (simp)
  apply (simp add: par_tr_nil_left) 
  apply (simp add: noTick_def)

  apply (rule_tac x="<Tick>" in exI)
  apply (rule_tac x="t" in exI)
  apply (simp)
  apply (simp add: par_tr_Tick_left)
  apply (simp add: noTick_def)

done

(*********************************************************
                    P ||| SKIP
 *********************************************************)

lemma cspT_Interleave_unit_r: 
  "P ||| SKIP =T[M,M] P"
apply (rule cspT_rw_left)
apply (rule cspT_commut)
apply (simp add: cspT_Interleave_unit_l)
done

lemmas cspT_Interleave_unit =
       cspT_Interleave_unit_l
       cspT_Interleave_unit_r


end
