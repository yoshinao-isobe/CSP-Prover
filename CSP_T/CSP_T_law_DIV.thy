           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               December 2005               |
            |                  April 2006  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_law_DIV
imports CSP_T_law_basic
begin

(*****************************************************************

         1. DIV |[X]| DIV
         2. DIV |[X]| P
         3. P |[X]| DIV
         4. DIV -- X
         5. DIV [[r]]
         6. DIV ;; P
         7. P ;; DIV
         8. DIV |. n

 *****************************************************************)

(*********************************************************
                       DIV |[X]| DIV
 *********************************************************)

(* T *)

lemma cspT_DIV_Parallel:
   "DIV |[X]| DIV =T[M1,M2] DIV"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces)+
done

(*********************************************************
                       DIV |[X]| P
 *********************************************************)

lemma cspT_DIV_Parallel_step_l:
   "DIV |[X]| (? :Y -> Qf) =T[M,M] (? x:(Y-X) -> (DIV |[X]| Qf x)) [+] DIV"
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
  apply (rule_tac x="s" in exI, simp)

(* <= *)

 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE)
  apply (simp_all)

  apply (rule_tac x="<Ev a> ^^^ ta" in exI, simp)
  apply (simp add: par_tr_head)
done

(*** r ***)

lemma cspT_DIV_Parallel_step_r:
  "(? :Y -> Pf) |[X]| DIV =T[M,M] 
   (? x:(Y - X) -> (Pf x |[X]| DIV)) [+] DIV"
apply (rule cspT_rw_left)
apply (rule cspT_commut)
apply (rule cspT_rw_left)
apply (rule cspT_DIV_Parallel_step_l)
apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_commut)
apply (rule cspT_reflex)
apply (rule cspT_reflex)
done

lemmas cspT_DIV_Parallel_step = 
       cspT_DIV_Parallel_step_l cspT_DIV_Parallel_step_r

(*********************************************************
                      DIV and Parallel
 *********************************************************)

lemma cspT_DIV_Parallel_Ext_choice_DIV_l:
  "(P [+] DIV) |[X]| DIV =T[M,M] (P |[X]| DIV)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)
 apply (fast)

(* <= *)
 apply (rule, simp add: in_traces)
 apply (fast)
done

lemma cspT_DIV_Parallel_Ext_choice_DIV_r:
  "DIV |[X]| (P [+] DIV) =T[M,M] (DIV |[X]| P)"
apply (rule cspT_rw_left)
apply (rule cspT_commut)
apply (rule cspT_rw_left)
apply (rule cspT_DIV_Parallel_Ext_choice_DIV_l)
apply (rule cspT_commut)
done

lemmas cspT_DIV_Parallel_Ext_choice_DIV =
       cspT_DIV_Parallel_Ext_choice_DIV_l
       cspT_DIV_Parallel_Ext_choice_DIV_r

(*********************************************************
                      DIV -- X
 *********************************************************)

lemma cspT_DIV_Hiding_Id: 
   "DIV -- X =T[M1,M2] DIV"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
done

(*** div-hide-step ***)

lemma cspT_DIV_Hiding_step:
  "((? :Y -> Pf) [+] DIV) -- X =T[M,M] 
   (((? x:(Y-X) -> (Pf x -- X)) [+] DIV) |~| (! x:(Y Int X) .. (Pf x -- X)))"
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

   apply (rule_tac x="<Ev a> ^^^ s" in exI)
   apply (simp)
done

(*********************************************************
                      DIV [[r]]
 *********************************************************)

lemma cspT_DIV_Renaming_Id: 
   "DIV [[r]] =T[M1,M2] DIV"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
done

(*********************************************************
                       DIV ;; P
 *********************************************************)

lemma cspT_DIV_Seq_compo: "DIV ;; P =T[M1,M2] DIV"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces)
 apply (force)

(* <= *)
 apply (rule, simp add: in_traces)
done

(*********************************************************
               DIV and Sequential composition
 *********************************************************)

lemma cspT_DIV_Seq_compo_step:
  "((? :X -> Pf) [> DIV) ;; Q =T[M,M] (? x:X -> (Pf x ;; Q)) [> DIV"
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
done


(*********************************************************
                      DIV |. n
 *********************************************************)

lemma cspT_DIV_Depth_rest: 
   "DIV |. n =T[M1,M2] DIV"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
done

(*********************************************************
                      cspT_DIV
 *********************************************************)

lemmas cspT_DIV =
       cspT_DIV_Parallel
       cspT_DIV_Parallel_step
       cspT_DIV_Parallel_Ext_choice_DIV
       cspT_DIV_Hiding_Id
       cspT_DIV_Hiding_step
       cspT_DIV_Renaming_Id
       cspT_DIV_Seq_compo
       cspT_DIV_Seq_compo_step
       cspT_DIV_Depth_rest

(*********************************************************
                       P [+] DIV
 *********************************************************)

lemma cspT_Ext_choice_DIV_resolve: "P [+] DIV =T[M,M] P [> DIV"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces)

(* <= *)
 apply (rule, simp add: in_traces)
done

end
