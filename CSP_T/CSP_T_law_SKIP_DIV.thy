           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               December 2005               |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_law_SKIP_DIV
imports CSP_T_law_SKIP CSP_T_law_DIV
begin

(*********************************************************
                   (SKIP [+] DIV)
 *********************************************************)

lemma cspT_SKIP_DIV_Ext_choice1: "(SKIP [+] DIV) =T[M1,M2] SKIP"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces)
 apply (force)

(* <= *)
 apply (rule, simp add: in_traces)
done

lemma cspT_SKIP_DIV_Ext_choice2: "(DIV [+] SKIP) =T[M1,M2] SKIP"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces)+
done

lemmas cspT_SKIP_DIV_Ext_choice =
       cspT_SKIP_DIV_Ext_choice1
       cspT_SKIP_DIV_Ext_choice2

(*********************************************************
                    SKIP |[X]| DIV
 *********************************************************)

lemma cspT_SKIP_DIV_Parallel1:
   "SKIP |[X]| DIV =T[M1,M2] DIV"
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
done

lemma cspT_SKIP_DIV_Parallel2:
   "DIV |[X]| SKIP =T[M1,M2] DIV"
apply (rule cspT_rw_left)
apply (rule cspT_commut)
apply (rule cspT_rw_left)
apply (rule cspT_SKIP_DIV_Parallel1)
apply (rule cspT_reflex)
done

lemmas cspT_SKIP_DIV_Parallel =
       cspT_SKIP_DIV_Parallel1
       cspT_SKIP_DIV_Parallel2
       cspT_Parallel_term
       cspT_DIV_Parallel

(*********************************************************
                 DIV and Parallel-SKIP
 *********************************************************)

(*** SKIP and DIV ***)

lemma cspT_DIV_Parallel_Ext_choice_SKIP_l:
  "(P [+] SKIP) |[X]| DIV =T[M,M] (P |[X]| DIV)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)
  apply (simp add: par_tr_nil_right)
  apply (elim conjE)
  apply (simp add: image_iff)

(* <= *)
 apply (rule, simp add: in_traces)
 apply (elim conjE exE disjE)
  apply (simp add: par_tr_nil_right)
  apply (elim conjE)
  apply (simp add: image_iff)
done

lemma cspT_DIV_Parallel_Ext_choice_SKIP_r:
  "DIV |[X]| (P [+] SKIP) =T[M,M] (DIV |[X]| P)"
apply (rule cspT_rw_left)
apply (rule cspT_commut)
apply (rule cspT_rw_left)
apply (rule cspT_DIV_Parallel_Ext_choice_SKIP_l)
apply (rule cspT_commut)
done

lemmas cspT_DIV_Parallel_Ext_choice_SKIP =
       cspT_DIV_Parallel_Ext_choice_SKIP_l
       cspT_DIV_Parallel_Ext_choice_SKIP_r

lemmas cspT_DIV_Parallel_Ext_choice =
       cspT_DIV_Parallel_Ext_choice_SKIP
       cspT_DIV_Parallel_Ext_choice_DIV

(*********************************************************
                 SKIP and Parallel-DIV
 *********************************************************)

(*** DIV and SKIP ***)

lemma cspT_SKIP_Parallel_Ext_choice_DIV_l:
  "((? :Y -> Pf) [+] DIV) |[X]| SKIP =T[M,M] 
   (? x:(Y - X) -> (Pf x |[X]| SKIP)) [+] DIV"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)

  apply (rule disjI2)
  apply (simp add: par_tr_nil_right)
  apply (elim conjE)
  apply (simp add: image_iff)
  apply (rule_tac x="sa" in exI)
  apply (rule_tac x="<>" in exI)
  apply (simp add: par_tr_nil_right)

  apply (rule disjI2)
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

lemma cspT_SKIP_Parallel_Ext_choice_DIV_r:
  "SKIP |[X]| ((? :Y -> Pf) [+] DIV) =T[M,M]
   (? x:(Y - X) -> (SKIP |[X]| Pf x)) [+] DIV"
apply (rule cspT_rw_left)
apply (rule cspT_commut)
apply (rule cspT_rw_left)
apply (rule cspT_SKIP_Parallel_Ext_choice_DIV_l)
apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_commut)
apply (rule cspT_reflex)
apply (rule cspT_reflex)
done

lemmas cspT_SKIP_Parallel_Ext_choice_DIV =
       cspT_SKIP_Parallel_Ext_choice_DIV_l
       cspT_SKIP_Parallel_Ext_choice_DIV_r

lemmas cspT_SKIP_Parallel_Ext_choice =
       cspT_SKIP_Parallel_Ext_choice_SKIP
       cspT_SKIP_Parallel_Ext_choice_DIV

(*---------------------------------------------*
 |                 SKIP , DIV                  |
 *---------------------------------------------*)

lemmas cspT_SKIP_DIV_Parallel_step =
       cspT_Parallel_preterm
       cspT_DIV_Parallel_step

lemmas cspT_SKIP_DIV_Parallel_Ext_choice =
       cspT_SKIP_Parallel_Ext_choice
       cspT_DIV_Parallel_Ext_choice

lemmas cspT_SKIP_DIV_Hiding_Id =
       cspT_SKIP_Hiding_Id
       cspT_DIV_Hiding_Id

lemmas cspT_SKIP_DIV_Hiding_step =
       cspT_DIV_Hiding_step
       cspT_SKIP_Hiding_step

lemmas cspT_SKIP_DIV_Renaming_Id =
       cspT_SKIP_Renaming_Id
       cspT_DIV_Renaming_Id

lemmas cspT_SKIP_DIV_Seq_compo =
       cspT_Seq_compo_unit
       cspT_DIV_Seq_compo

lemmas cspT_SKIP_DIV_Seq_compo_step =
       cspT_SKIP_Seq_compo_step
       cspT_DIV_Seq_compo_step

lemmas cspT_SKIP_DIV_Depth_rest =
       cspT_SKIP_Depth_rest
       cspT_DIV_Depth_rest

lemmas cspT_SKIP_DIV =
       cspT_SKIP_DIV_Parallel_step
       cspT_SKIP_DIV_Ext_choice
       cspT_SKIP_DIV_Parallel
       cspT_SKIP_DIV_Parallel_Ext_choice
       cspT_SKIP_DIV_Hiding_Id
       cspT_SKIP_DIV_Hiding_step
       cspT_SKIP_DIV_Renaming_Id
       cspT_SKIP_DIV_Seq_compo
       cspT_SKIP_DIV_Seq_compo_step
       cspT_SKIP_DIV_Depth_rest

(*** resolve ***)

lemmas cspT_Ext_choice_SKIP_DIV_resolve =
       cspT_Ext_choice_SKIP_resolve
       cspT_Ext_choice_DIV_resolve

(*----------------------------------------------*
 |                                              |
 |        for convenienve  (SKIP or DIV)        |
 |                                              |
 *----------------------------------------------*)

(*********************************************************
            (SKIP or DIV [+] SKIP or DIV)
 *********************************************************)

lemma cspT_SKIP_or_DIV_Ext_choice:
  "[| P = SKIP | P = DIV ; Q = SKIP | Q = DIV |] ==>
   (P [+] Q) =T[M1,M2] (if (P = SKIP | Q = SKIP) then SKIP else DIV)"
apply (elim disjE)
apply (simp_all)
apply (rule cspT_rw_left)
apply (rule cspT_Ext_choice_idem)
apply (simp)
apply (simp add: cspT_SKIP_DIV)
apply (simp add: cspT_SKIP_DIV)
apply (rule cspT_rw_left)
apply (rule cspT_Ext_choice_idem)
apply (simp)
done

(*********************************************************
            (SKIP or DIV |[X]| SKIP or DIV)
 *********************************************************)

lemma cspT_SKIP_or_DIV_Parallel:
  "[| P = SKIP | P = DIV ; Q = SKIP | Q = DIV |] ==>
   (P |[X]| Q) =T[M1,M2] (if (P = SKIP & Q = SKIP) then SKIP else DIV)"
apply (elim disjE)
apply (simp_all add: cspT_SKIP_DIV)
done

(*********************************************************
                  (SKIP or DIV) and Hiding
 *********************************************************)

lemma cspT_SKIP_or_DIV_Hiding_step:
  "Q = SKIP | Q = DIV ==>
   ((? :Y -> Pf) [+] Q) -- X =T[M,M] 
   (((? x:(Y-X) -> (Pf x -- X)) [+] Q) |~| (! x:(Y Int X) .. (Pf x -- X)))"
apply (erule disjE)
apply (simp_all add: cspT_SKIP_DIV)
done

(*********************************************************
                  SKIP or DIV |. Suc n
 *********************************************************)

lemma cspT_SKIP_or_DIV_Depth_rest: 
   "Q = SKIP | Q = DIV ==> Q |. (Suc n) =T[M1,M2] Q"
apply (erule disjE)
apply (simp_all add: cspT_SKIP_DIV)
done

(*********************************************************
                    P [+] (SKIP or DIV)
 *********************************************************)

lemma cspT_Ext_choice_SKIP_or_DIV_resolve:
  "Q = SKIP | Q = DIV ==> P [+] Q =T[M,M] P [> Q"
apply (erule disjE)
apply (simp_all add: cspT_Ext_choice_SKIP_DIV_resolve)
done

lemmas cspT_SKIP_or_DIV =
       cspT_SKIP_or_DIV_Ext_choice
       cspT_SKIP_or_DIV_Parallel
       cspT_SKIP_or_DIV_Hiding_step
       cspT_SKIP_or_DIV_Depth_rest

       (* no resolve *)

end
