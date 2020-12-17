           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_law_SKIP
imports CSP_F_law_basic CSP_T.CSP_T_law_SKIP
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

lemma cspF_Parallel_term:
   "SKIP |[X]| SKIP =F[M1,M2] SKIP"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Parallel_term)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE exE)
 apply (simp_all)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (erule disjE)
  apply (simp)
  apply (fast)

  apply (simp)
  apply (fast)
done

(*********************************************************
                      SKIP |[X]| P
 *********************************************************)

lemma cspF_Parallel_preterm_l_set1: 
  "[| Ya - insert Tick (Ev ` X) = Z - insert Tick (Ev ` X) ; Ev ` Y Int Z = {} |]
   ==> Ev ` (Y - X) Int (Ya Un Z) = {}"
by (auto)

lemma cspF_Parallel_preterm_l: 
   "SKIP |[X]| (? :Y -> Qf) =F[M,M] ? x:(Y-X) -> (SKIP |[X]| Qf x)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Parallel_preterm_l)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (insert trace_nil_or_Tick_or_Ev)
 apply (elim disjE conjE exE)
  apply (simp_all)

  apply (simp add: cspF_Parallel_preterm_l_set1)

  apply (drule_tac x="s" in spec)
  apply (erule disjE, simp)
  apply (erule disjE, simp)
  apply (elim conjE exE, simp)
  apply (simp add: par_tr_head)
  apply (fast)

      (* automatized by "par_tr_nil_Tick" *)

  apply (drule_tac x="s" in spec)
  apply (erule disjE, simp)
  apply (erule disjE, simp)
  apply (elim conjE exE, simp)
  apply (simp add: par_tr_head)
  apply (fast)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (erule disjE, simp)
  apply (rule_tac x="Xa - {Tick}" in exI)
  apply (rule_tac x="Xa - (Ev ` X)" in exI)
  apply (rule conjI, fast)
  apply (rule conjI, fast)

  apply (rule conjI)
  apply (simp add: Evset_def, fast)
  apply (fast)

 (* *)
  apply (elim disjE conjE exE)
  apply (simp_all)
   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Z" in exI, simp)
   apply (rule_tac x="<>" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI, simp)
   apply (simp add: par_tr_head)

   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Z" in exI, simp)
   apply (rule_tac x="<Tick>" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI, simp)
   apply (simp add: par_tr_head)
done

(*********************************************************
                      P |[X]| SKIP
 *********************************************************)

lemma cspF_Parallel_preterm_r: 
   "(? :Y -> Pf) |[X]| SKIP
     =F[M,M] ? x:(Y-X) -> (Pf x |[X]| SKIP)"
apply (rule cspF_trans)
apply (rule cspF_Parallel_commut)
apply (rule cspF_trans)
apply (rule cspF_Parallel_preterm_l)
apply (rule cspF_rm_head, simp)
apply (rule cspF_Parallel_commut)
done

lemmas cspF_Parallel_preterm = cspF_Parallel_preterm_l cspF_Parallel_preterm_r

(*********************************************************
                      SKIP and Parallel
 *********************************************************)

(* p.288 *)

lemma cspF_SKIP_Parallel_Ext_choice_SKIP_l:
  "((? :Y -> Pf) [+] SKIP) |[X]| SKIP =F[M,M] 
   (? x:(Y - X) -> (Pf x |[X]| SKIP)) [+] SKIP"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_SKIP_Parallel_Ext_choice_SKIP_l)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_failures)
 apply (elim conjE exE disjE)
 apply (simp_all)

  apply (rule disjI1)
  apply (blast)

  apply (simp add: par_tr_nil_right)
  apply (elim conjE)
  apply (simp add: image_iff)
  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Z" in exI)
  apply (simp)
  apply (rule_tac x="sb" in exI)
  apply (rule_tac x="<>" in exI)
  apply (simp add: par_tr_nil_right)

  apply (rule, simp add: in_traces)

  apply (simp add: par_tr_Tick_right)
  apply (elim conjE)
  apply (simp add: image_iff)
  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Z" in exI)
  apply (simp)
  apply (rule_tac x="sb" in exI)
  apply (rule_tac x="<Tick>" in exI)
  apply (simp add: par_tr_Tick_right)

(* <= *)
 apply (rule, simp add: in_failures)
 apply (elim conjE exE disjE)
 apply (simp_all)

  apply (simp add: in_traces)
  apply (rule_tac x="Xa" in exI)
  apply (rule_tac x="Xa" in exI)
  apply (simp)

  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Z" in exI)
  apply (simp add: par_tr_nil_right)
  apply (rule_tac x="<Ev a> ^^^ sb" in exI)
  apply (rule_tac x="<>" in exI)
  apply (simp add: par_tr_nil_right)
  apply (simp add: image_iff)
  apply (fast)

  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Z" in exI)
  apply (simp add: par_tr_Tick_right)
  apply (rule_tac x="<Ev a> ^^^ sb" in exI)
  apply (rule_tac x="<Tick>" in exI)
  apply (simp add: par_tr_Tick_right)
  apply (simp add: image_iff)
  apply (fast)

  apply (rule_tac x="Xa" in exI)
  apply (rule_tac x="Xa" in exI)
  apply (simp)

  apply (simp add: in_traces)

  apply (rule_tac x="Xa" in exI)
  apply (rule_tac x="Xa" in exI)
  apply (simp)
done

lemma cspF_SKIP_Parallel_Ext_choice_SKIP_r:
  "SKIP |[X]| ((? :Y -> Pf) [+] SKIP)  =F[M,M]
    (? x:(Y - X) -> (SKIP |[X]| Pf x)) [+] SKIP"
apply (rule cspF_rw_left)
apply (rule cspF_commut)
apply (rule cspF_rw_left)
apply (rule cspF_SKIP_Parallel_Ext_choice_SKIP_l)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_commut)
apply (rule cspF_reflex)
apply (rule cspF_reflex)
done

lemmas cspF_SKIP_Parallel_Ext_choice_SKIP =
       cspF_SKIP_Parallel_Ext_choice_SKIP_l
       cspF_SKIP_Parallel_Ext_choice_SKIP_r

(*********************************************************
                      SKIP -- X
 *********************************************************)

lemma cspF_SKIP_Hiding_Id: 
   "SKIP -- X =F[M,M] SKIP"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_SKIP_Hiding_Id)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE exE)
 apply (simp_all)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE exE)
 apply (simp_all)
  apply (rule_tac x="<>" in exI)
  apply (simp add: Evset_def)
  apply (fast)
  apply (rule_tac x="<Tick>" in exI)
  apply (simp)
done

(*********************************************************
                      SKIP and Hiding
 *********************************************************)

(* p.288 version
  "((? :Y -> Pf) [+] SKIP) -- X =F[M,M]
       IF (Y Int X = {}) THEN ((? x:Y -> (Pf x -- X)) [+] SKIP)
                         ELSE (((? x:(Y-X) -> (Pf x -- X)) [+] SKIP)
                               |~| (! x:(Y Int X) .. (Pf x -- X)))"
*)

lemma cspF_SKIP_Hiding_step:
  "((? :Y -> Pf) [+] SKIP) -- X =F[M,M]
   (((? x:(Y-X) -> (Pf x -- X)) [+] SKIP) |~| (! x:(Y Int X) .. (Pf x -- X)))"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_SKIP_Hiding_step)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_failures)
 apply (elim conjE exE disjE)
 apply (simp_all)
 apply (simp_all add: in_traces)

  apply (case_tac "a : X")
  apply (simp)
  apply (blast)
  apply (force)

(* <= *)
 apply (rule)

  apply (simp add: in_failures)
  apply (elim conjE exE bexE disjE)
  apply (simp_all)

   apply (rule_tac x="<>" in exI)
   apply (simp add: in_traces)
   apply (simp add: Evset_def)
   apply (fast)

   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (simp)

   apply (rule_tac x="<Tick>" in exI)
   apply (simp)

   apply (simp add: in_traces)

   apply (rule_tac x="<>" in exI)
   apply (simp add: Evset_def)
   apply (fast)

   apply (rule_tac x="<Ev a> ^^^ sa" in exI)
   apply (simp)
done

(*********************************************************
                      SKIP [[r]]
 *********************************************************)

lemma cspF_SKIP_Renaming_Id: 
   "SKIP [[r]] =F[M1,M2] SKIP"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_SKIP_Renaming_Id)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (force)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (force)
done

(*********************************************************
                       SKIP ;; P
 *********************************************************)

lemma cspF_Seq_compo_unit_l: "SKIP ;; P =F[M,M] P"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Seq_compo_unit_l)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_failures)
 apply (elim conjE disjE)
 apply (simp_all add: Evset_def)
 apply (elim conjE exE)
 apply (simp add: in_traces)

(* <= *)
 apply (rule, simp add: in_failures)
 apply (rule disjI2)
 apply (rule_tac x="<>" in exI)
 apply (rule_tac x="s" in exI)
 apply (simp add: in_traces)
done

(*********************************************************
                       P ;; SKIP
 *********************************************************)

lemma cspF_Seq_compo_unit_r: "P ;; SKIP =F[M,M] P"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Seq_compo_unit_r)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim conjE exE disjE)
 apply (rule memF_F2, simp, fast)
 apply (rule domF_F2_F4, simp_all)
 apply (fold comp_def, simp)
 apply (rule domF_T3, simp_all)
 apply (fold comp_def, simp)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (insert trace_last_noTick_or_Tick)
 apply (drule_tac x="s" in spec)
 apply (erule disjE)
  apply (case_tac "Tick : X")
   apply (rule disjI1, simp)
   apply (subgoal_tac "insert Tick X = X", simp, fast)
   (* Tick ~: X *)
   apply (case_tac "s ^^^ <Tick> ~:t [[P]]Tf (fstF o M)")
    apply (rule disjI1, simp)
    apply (rule domF_F3[of "[[P]]Tf (fstF o M)" "failures P M" _ _ "{Tick}", simplified])
    apply (simp_all add: semTf_def)
    (* *)
    apply (rule disjI2)
    apply (rule_tac x="s" in exI)
    apply (rule_tac x="<>" in exI, simp)
    apply (simp add: Evset_def, fast)
  (* *)
  apply (elim conjE exE, simp)
  apply (rule_tac x="sa" in exI)
  apply (rule_tac x="<Tick>" in exI)
  apply (simp)
  apply (rule domF_T2[of _ "failures P M"], simp_all)
done

lemmas cspF_Seq_compo_unit = cspF_Seq_compo_unit_l cspF_Seq_compo_unit_r

(*********************************************************
               SKIP and Sequential composition
 *********************************************************)

(* p.141 *)

lemma cspF_SKIP_Seq_compo_step:
  "((? :X -> Pf) [> SKIP) ;; Q =F[M,M] (? x:X -> (Pf x ;; Q)) [> Q"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_SKIP_Seq_compo_step)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_failures in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)
 apply (simp add: Evset_def)
 apply (simp add: Evset_def)
 apply (simp add: Evset_def)

 apply (rule disjI2)
 apply (rule disjI1)
 apply (insert trace_nil_or_Tick_or_Ev)
 apply (drule_tac x="sa" in spec)

 apply (elim disjE conjE exE)
  apply (simp_all)
  apply (simp add: appt_assoc)
  apply (rule disjI2)
  apply (rule disjI1)
  apply (rule_tac x="sc" in exI)
  apply (rule_tac x="t" in exI)
  apply (simp)

(* <= *)
 apply (rule, simp add: in_failures in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)

  apply (rule disjI2)
  apply (rule_tac x="<>" in exI)
  apply (rule_tac x="<>" in exI)
  apply (simp)

  apply (rule disjI2)
  apply (rule_tac x="<>" in exI)
  apply (rule_tac x="<>" in exI)
  apply (simp)

  apply (rule disjI2)
  apply (rule_tac x="<Ev a> ^^^ sb" in exI)
  apply (rule_tac x="t" in exI)
  apply (simp add: appt_assoc)

  apply (rule disjI2)
  apply (rule_tac x="<>" in exI)
  apply (rule_tac x="s" in exI)
  apply (simp)

  apply (rule disjI2)
  apply (rule_tac x="<>" in exI)
  apply (rule_tac x="<>" in exI)
  apply (simp)
  apply (rule proc_F2_F4)
  apply (simp_all)
done

(*********************************************************
                      SKIP |. n
 *********************************************************)

lemma cspF_SKIP_Depth_rest: 
   "SKIP |. Suc n =F[M1,M2] SKIP"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_SKIP_Depth_rest)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim conjE disjE)
 apply (simp)
 apply (simp)
 apply (case_tac "0 < n", simp)
 apply (simp)
 apply (rule_tac x="<>" in exI)
 apply (simp)
done

(*********************************************************
                      cspF_SKIP
 *********************************************************)

lemmas cspF_SKIP =
       cspF_Parallel_term
       cspF_Parallel_preterm
       cspF_SKIP_Parallel_Ext_choice_SKIP
       cspF_SKIP_Hiding_Id
       cspF_SKIP_Hiding_step
       cspF_SKIP_Renaming_Id
       cspF_Seq_compo_unit
       cspF_SKIP_Seq_compo_step
       cspF_SKIP_Depth_rest

(*********************************************************
                       P [+] SKIP
 *********************************************************)

(* p.141 *)

lemma cspF_Ext_choice_SKIP_resolve: "P [+] SKIP =F[M,M] P [> SKIP"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Ext_choice_SKIP_resolve)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_failures)
 apply (force)

(* <= *)
 apply (rule, simp add: in_traces in_failures)
 apply (force)
done

(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)


(*********************************************************
                    SKIP ||| P   (--> SKIP)
 *********************************************************)

lemma cspF_Interleave_unit_l: 
  "SKIP ||| P =F[M,M] P"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Interleave_unit_l)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE exE)
 apply (simp_all)
  apply (simp add: par_tr_nil_left) 
  apply (subgoal_tac "Y Un Z = Z")
  apply (simp)
  apply (simp add: Evset_def)
  apply (force)

  apply (simp add: par_tr_Tick_left)
  apply (simp add: Tick_in_sett)
  apply (elim conjE exE)
  apply (rotate_tac -3)
  apply (drule sym)
  apply (simp)
  apply (rule proc_T2_T3)
  apply (simp_all)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (rule_tac x="X-{Tick}" in exI)
 apply (rule_tac x="X" in exI)
 apply (simp)
  apply (rule conjI)
  apply (force)

 apply (case_tac "noTick s")

  apply (rule_tac x="<>" in exI)
  apply (rule_tac x="s" in exI)
  apply (simp add: par_tr_nil_left) 
  apply (simp add: noTick_def)
  apply (simp add: Evset_def)
  apply (force)

  apply (rule_tac x="<Tick>" in exI)
  apply (rule_tac x="s" in exI)
  apply (simp)
  apply (simp add: par_tr_Tick_left)
  apply (simp add: noTick_def)
done


(*********************************************************
                    P ||| SKIP (SKIP)
 *********************************************************)

lemma cspF_Interleave_unit_r: 
  "P ||| SKIP =F[M,M] P"
apply (rule cspF_rw_left)
apply (rule cspF_commut)
apply (simp add: cspF_Interleave_unit_l)
done

lemmas cspF_Interleave_unit =
       cspF_Interleave_unit_l
       cspF_Interleave_unit_r

end
