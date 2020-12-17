           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               December 2005               |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_law_DIV
imports CSP_F_law_basic CSP_T.CSP_T_law_DIV
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

lemma cspF_DIV_Parallel: 
   "DIV |[X]| DIV =F[M1,M2] DIV"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_DIV_Parallel)
apply (rule order_antisym)
apply (rule, simp add: in_failures)+
done

(*********************************************************
                       DIV |[X]| P
 *********************************************************)

lemma cspF_DIV_Parallel_step_l:
   "DIV |[X]| (? :Y -> Qf) =F[M,M] (? x:(Y-X) -> (DIV |[X]| Qf x)) [+] DIV"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_DIV_Parallel_step_l)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim conjE exE disjE)
 apply (simp_all add: in_traces)
done

lemma cspF_DIV_Parallel_step_r:
   "(? :Y -> Qf) |[X]| DIV =F[M,M] (? x:(Y-X) -> (Qf x |[X]| DIV)) [+] DIV"
apply (rule cspF_rw_left)
apply (rule cspF_commut)
apply (rule cspF_rw_right)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_commut)
apply (rule cspF_reflex)
apply (rule cspF_DIV_Parallel_step_l)
done

lemmas cspF_DIV_Parallel_step = 
       cspF_DIV_Parallel_step_l cspF_DIV_Parallel_step_r

(*********************************************************
                      DIV and Parallel
 *********************************************************)

lemma cspF_DIV_Parallel_Ext_choice_DIV_l:
  "(P [+] DIV) |[X]| DIV =F[M,M] (P |[X]| DIV)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_DIV_Parallel_Ext_choice_DIV_l)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_failures)

(* <= *)
 apply (rule, simp add: in_failures)
done

lemma cspF_DIV_Parallel_Ext_choice_DIV_r:
  "DIV |[X]| (P [+] DIV) =F[M,M] (DIV |[X]| P)"
apply (rule cspF_rw_left)
apply (rule cspF_commut)
apply (rule cspF_rw_left)
apply (rule cspF_DIV_Parallel_Ext_choice_DIV_l)
apply (rule cspF_commut)
done

lemmas cspF_DIV_Parallel_Ext_choice_DIV =
       cspF_DIV_Parallel_Ext_choice_DIV_l
       cspF_DIV_Parallel_Ext_choice_DIV_r

(*********************************************************
                      DIV -- X
 *********************************************************)

lemma cspF_DIV_Hiding_Id: 
   "DIV -- X =F[M1,M2] DIV"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_DIV_Hiding_Id)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
done

(*** div-hide-step ***)

lemma cspF_DIV_Hiding_step:
  "((? :Y -> Pf) [+] DIV) -- X =F[M,M]
   (((? x:(Y-X) -> (Pf x -- X)) [+] DIV) |~| (! x:(Y Int X) .. (Pf x -- X)))"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_DIV_Hiding_step)
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

   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (simp)

   apply (simp add: in_traces)

   apply (rule_tac x="<>" in exI)
   apply (simp add: Evset_def)
   apply (fast)

   apply (rule_tac x="<Ev a> ^^^ sa" in exI)
   apply (simp)
done

(*********************************************************
                      DIV [[r]]
 *********************************************************)

lemma cspF_DIV_Renaming_Id: 
   "DIV [[r]] =F[M1,M2] DIV"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_DIV_Renaming_Id)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
done

(*********************************************************
                       DIV ;; P
 *********************************************************)

lemma cspF_DIV_Seq_compo: "DIV ;; P =F[M1,M2] DIV"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_DIV_Seq_compo)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_failures)
 apply (elim conjE exE)
 apply (simp add: in_traces)

(* <= *)
 apply (rule, simp add: in_failures)
done

(*********************************************************
               DIV and Sequential composition
 *********************************************************)

lemma cspF_DIV_Seq_compo_step:
  "((? :X -> Pf) [> DIV) ;; Q =F[M,M] (? x:X -> (Pf x ;; Q)) [> DIV"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_DIV_Seq_compo_step)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_failures in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)

 apply (insert trace_nil_or_Tick_or_Ev)
 apply (drule_tac x="sa" in spec)

 apply (elim disjE conjE exE)
  apply (simp_all)
  apply (simp add: appt_assoc)
  apply (rule disjI2)
  apply (rule_tac x="sc" in exI)
  apply (rule_tac x="t" in exI)
  apply (simp)

(* <= *)
 apply (rule, simp add: in_failures in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)

  apply (rule disjI2)
  apply (rule_tac x="<Ev a> ^^^ sb" in exI)
  apply (rule_tac x="t" in exI)
  apply (simp add: appt_assoc)
done

(*********************************************************
                      DIV |. n
 *********************************************************)

lemma cspF_DIV_Depth_rest: 
   "DIV |. n =F[M1,M2] DIV"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_DIV_Depth_rest)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
done

(*********************************************************
                      cspF_DIV
 *********************************************************)

lemmas cspF_DIV =
       cspF_DIV_Parallel
       cspF_DIV_Parallel_step
       cspF_DIV_Parallel_Ext_choice_DIV
       cspF_DIV_Hiding_Id
       cspF_DIV_Hiding_step
       cspF_DIV_Renaming_Id
       cspF_DIV_Seq_compo
       cspF_DIV_Seq_compo_step
       cspF_DIV_Depth_rest

(*********************************************************
                       P [+] DIV
 *********************************************************)

lemma cspF_Ext_choice_DIV_resolve: "P [+] DIV =F[M,M] P [> DIV"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Ext_choice_DIV_resolve)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_failures)
 apply (simp add: in_traces)
 apply (force)

(* <= *)
 apply (rule, simp add: in_traces in_failures)
 apply (force)
done

end
