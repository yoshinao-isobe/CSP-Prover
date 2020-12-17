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
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_law_SKIP_DIV
imports CSP_F_law_SKIP CSP_F_law_DIV CSP_T.CSP_T_law_SKIP_DIV
begin

(*********************************************************
                   (SKIP [+] DIV)
 *********************************************************)

lemma cspF_SKIP_DIV_Ext_choice1: "(SKIP [+] DIV) =F[M1,M2] SKIP"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_SKIP_DIV_Ext_choice)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces in_failures)
 apply (force)

(* <= *)
 apply (rule, simp add: in_traces in_failures)
 apply (force)
done

(*********************************************************
                   (DIV [+] SKIP)
 *********************************************************)

lemma cspF_SKIP_DIV_Ext_choice2: "(DIV [+] SKIP) =F[M1,M2] SKIP"
apply (rule cspF_rw_left)
apply (rule cspF_commut)
apply (rule cspF_SKIP_DIV_Ext_choice1)
done

lemmas cspF_SKIP_DIV_Ext_choice =
       cspF_SKIP_DIV_Ext_choice1
       cspF_SKIP_DIV_Ext_choice2

(*********************************************************
                    SKIP |[X]| DIV
 *********************************************************)

lemma cspF_SKIP_DIV_Parallel1:
   "SKIP |[X]| DIV =F[M1,M2] DIV"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_SKIP_DIV_Parallel1)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
done

lemma cspF_SKIP_DIV_Parallel2:
   "DIV |[X]| SKIP =F[M1,M2] DIV"
apply (rule cspF_rw_left)
apply (rule cspF_commut)
apply (rule cspF_rw_left)
apply (rule cspF_SKIP_DIV_Parallel1)
apply (rule cspF_reflex)
done

lemmas cspF_SKIP_DIV_Parallel =
       cspF_SKIP_DIV_Parallel1
       cspF_SKIP_DIV_Parallel2
       cspF_Parallel_term
       cspF_DIV_Parallel

(*********************************************************
                 DIV and Parallel-SKIP
 *********************************************************)

(*********************************************************
                      SKIP and Parallel
 *********************************************************)

(*** SKIP and DIV ***)

lemma cspF_DIV_Parallel_Ext_choice_SKIP_l:
  "(P [+] SKIP) |[X]| DIV =F[M,M] (P |[X]| DIV)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_DIV_Parallel_Ext_choice_SKIP_l)
apply (rule order_antisym)
apply (rule, simp add: in_failures)+
done

lemma cspF_DIV_Parallel_Ext_choice_SKIP_r:
  "DIV |[X]| (P [+] SKIP) =F[M,M] (DIV |[X]| P)"
apply (rule cspF_rw_left)
apply (rule cspF_commut)
apply (rule cspF_rw_left)
apply (rule cspF_DIV_Parallel_Ext_choice_SKIP_l)
apply (rule cspF_commut)
done

lemmas cspF_DIV_Parallel_Ext_choice_SKIP =
       cspF_DIV_Parallel_Ext_choice_SKIP_l
       cspF_DIV_Parallel_Ext_choice_SKIP_r

lemmas cspF_DIV_Parallel_Ext_choice =
       cspF_DIV_Parallel_Ext_choice_SKIP
       cspF_DIV_Parallel_Ext_choice_DIV

(*********************************************************
                 SKIP and Parallel-DIV
 *********************************************************)

(*** DIV and SKIP ***)

lemma cspF_SKIP_Parallel_Ext_choice_DIV_l:
  "((? :Y -> Pf) [+] DIV) |[X]| SKIP =F[M,M]
   (? x:(Y - X) -> (Pf x |[X]| SKIP)) [+] DIV"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_SKIP_Parallel_Ext_choice_DIV_l)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_failures)
 apply (elim conjE exE disjE)
 apply (simp_all)

  apply (simp add: par_tr_nil_right)
  apply (elim conjE)
  apply (simp add: image_iff)
  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Z" in exI)
  apply (simp)
  apply (rule_tac x="sb" in exI)
  apply (rule_tac x="<>" in exI)
  apply (simp add: par_tr_nil_right)

  apply (simp add: par_tr_Tick_right)
  apply (elim conjE)
  apply (simp add: image_iff)
  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Z" in exI)
  apply (simp)
  apply (rule_tac x="sb" in exI)
  apply (rule_tac x="<Tick>" in exI)
  apply (simp add: par_tr_Tick_right)

  apply (simp add: in_traces)

(* <= *)
 apply (rule, simp add: in_failures)
 apply (elim conjE exE disjE)
 apply (simp_all)

  apply (simp add: in_traces)
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

  apply (simp add: in_traces)
  apply (simp add: in_traces)
done

lemma cspF_SKIP_Parallel_Ext_choice_DIV_r:
  "SKIP |[X]| ((? :Y -> Pf) [+] DIV) =F[M,M]
   (? x:(Y - X) -> (SKIP |[X]| Pf x)) [+] DIV"
apply (rule cspF_rw_left)
apply (rule cspF_commut)
apply (rule cspF_rw_left)
apply (rule cspF_SKIP_Parallel_Ext_choice_DIV_l)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_commut)
apply (rule cspF_reflex)
apply (rule cspF_reflex)
done

lemmas cspF_SKIP_Parallel_Ext_choice_DIV =
       cspF_SKIP_Parallel_Ext_choice_DIV_l
       cspF_SKIP_Parallel_Ext_choice_DIV_r

lemmas cspF_SKIP_Parallel_Ext_choice =
       cspF_SKIP_Parallel_Ext_choice_SKIP
       cspF_SKIP_Parallel_Ext_choice_DIV

(*---------------------------------------------*
 |                 SKIP , DIV                  |
 *---------------------------------------------*)

lemmas cspF_SKIP_DIV_Parallel_step =
       cspF_Parallel_preterm
       cspF_DIV_Parallel_step

lemmas cspF_SKIP_DIV_Parallel_Ext_choice =
       cspF_SKIP_Parallel_Ext_choice
       cspF_DIV_Parallel_Ext_choice

lemmas cspF_SKIP_DIV_Hiding_Id =
       cspF_SKIP_Hiding_Id
       cspF_DIV_Hiding_Id

lemmas cspF_SKIP_DIV_Hiding_step =
       cspF_DIV_Hiding_step
       cspF_SKIP_Hiding_step

lemmas cspF_SKIP_DIV_Renaming_Id =
       cspF_SKIP_Renaming_Id
       cspF_DIV_Renaming_Id

lemmas cspF_SKIP_DIV_Seq_compo =
       cspF_Seq_compo_unit
       cspF_DIV_Seq_compo

lemmas cspF_SKIP_DIV_Seq_compo_step =
       cspF_SKIP_Seq_compo_step
       cspF_DIV_Seq_compo_step

lemmas cspF_SKIP_DIV_Depth_rest =
       cspF_SKIP_Depth_rest
       cspF_DIV_Depth_rest

lemmas cspF_SKIP_DIV =
       cspF_SKIP_DIV_Parallel_step
       cspF_SKIP_DIV_Ext_choice
       cspF_SKIP_DIV_Parallel
       cspF_SKIP_DIV_Parallel_Ext_choice
       cspF_SKIP_DIV_Hiding_Id
       cspF_SKIP_DIV_Hiding_step
       cspF_SKIP_DIV_Renaming_Id
       cspF_SKIP_DIV_Seq_compo
       cspF_SKIP_DIV_Seq_compo_step
       cspF_SKIP_DIV_Depth_rest

(*** resolve ***)

lemmas cspF_Ext_choice_SKIP_DIV_resolve =
       cspF_Ext_choice_SKIP_resolve
       cspF_Ext_choice_DIV_resolve

(*----------------------------------------------*
 |                                              |
 |        for convenienve  (SKIP or DIV)        |
 |                                              |
 *----------------------------------------------*)

(*********************************************************
            (SKIP or DIV [+] SKIP or DIV)
 *********************************************************)

lemma cspF_SKIP_or_DIV_Ext_choice:
  "[| P = SKIP | P = DIV ; Q = SKIP | Q = DIV |] ==>
   (P [+] Q) =F[M1,M2] (if (P = SKIP | Q = SKIP) then SKIP else DIV)"
apply (elim disjE)
apply (simp_all)
apply (rule cspF_rw_left)
apply (rule cspF_Ext_choice_idem)
apply (simp)
apply (simp add: cspF_SKIP_DIV)
apply (simp add: cspF_SKIP_DIV)
apply (rule cspF_rw_left)
apply (rule cspF_Ext_choice_idem)
apply (simp)
done

(*********************************************************
            (SKIP or DIV |[X]| SKIP or DIV)
 *********************************************************)

lemma cspF_SKIP_or_DIV_Parallel:
  "[| P = SKIP | P = DIV ; Q = SKIP | Q = DIV |] ==>
   (P |[X]| Q) =F[M1,M2] (if (P = SKIP & Q = SKIP) then SKIP else DIV)"
apply (elim disjE)
apply (simp_all add: cspF_SKIP_DIV)
done

(*********************************************************
                  (SKIP or DIV) and Hiding
 *********************************************************)

lemma cspF_SKIP_or_DIV_Hiding_step:
  "Q = SKIP | Q = DIV ==>
   ((? :Y -> Pf) [+] Q) -- X =F[M,M] 
   (((? x:(Y-X) -> (Pf x -- X)) [+] Q) |~| (! x:(Y Int X) .. (Pf x -- X)))"
apply (erule disjE)
apply (simp_all add: cspF_SKIP_DIV)
done

(*********************************************************
                  SKIP or DIV |. Suc n
 *********************************************************)

lemma cspF_SKIP_or_DIV_Depth_rest: 
   "Q = SKIP | Q = DIV ==> Q |. (Suc n) =F[M1,M2] Q"
apply (erule disjE)
apply (simp_all add: cspF_SKIP_DIV)
done

(*********************************************************
                    P [+] (SKIP or DIV)
 *********************************************************)

lemma cspF_Ext_choice_SKIP_or_DIV_resolve:
  "Q = SKIP | Q = DIV ==> P [+] Q =F[M,M] P [> Q"
apply (erule disjE)
apply (simp_all add: cspF_Ext_choice_SKIP_DIV_resolve)
done

lemmas cspF_SKIP_or_DIV =
       cspF_SKIP_or_DIV_Ext_choice
       cspF_SKIP_or_DIV_Parallel
       cspF_SKIP_or_DIV_Hiding_step
       cspF_SKIP_or_DIV_Depth_rest

       (* no resolv *)

end
