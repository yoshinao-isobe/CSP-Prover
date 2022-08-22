           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory CSP_F_law_step
imports CSP_F_domain CSP_F_law_basic CSP_T.CSP_T_law_step
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

lemma cspF_STOP_step: "STOP =F[M1,M2] ? :{} -> Pf"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_STOP_step)
apply (simp add: failures_iff)
done

(* to avoide producing free variables in tactics *)

lemma cspF_STOP_step_DIV: "STOP =F[M1,M2] ? x:{} -> DIV"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_STOP_step)
apply (simp add: failures_iff)
done


(*********************************************************
                    Act_prefix expansion
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Act_prefix_step: "a -> P =F[M,M] ? x:{a} -> P"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Act_prefix_step)
apply (simp add: failures_iff)
done

(*********************************************************
                    Ext choice expansion
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Ext_choice_step:
  "(? :X -> Pf) [+] (? :Y -> Qf) =F[M,M]
      ? x:(X Un Y) -> 
                (IF (x : X & x : Y) THEN (Pf x |~| Qf x)
                 ELSE IF (x : X) THEN Pf x
                 ELSE Qf x)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Ext_choice_step)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE exE)
 apply (simp_all)
 apply (force)
 apply (rule_tac x="a" in exI)
 apply (rule_tac x="sa" in exI)
 apply (simp)
 apply (rule_tac x="a" in exI)
 apply (rule_tac x="sa" in exI)
 apply (simp)
 apply (simp add: in_traces)
 apply (simp add: in_traces)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE exE)
 apply (simp_all)
 apply (force)

 apply (case_tac "a : Y")
 apply (simp_all add: in_failures)

 apply (case_tac "a : X")
 apply (simp_all add: in_failures)
done


lemma cspF_Ext_choice_step_disjnt :
    "P =F[M,M] (? :X -> Pf) \<Longrightarrow>
     Q =F[M,M] (? :Y -> Qf) \<Longrightarrow>
     disjnt X Y \<Longrightarrow>
     P [+] Q =F[M,M] ? x:(X \<union> Y) -> (IF (x \<in> X) THEN Pf x
                                     ELSE Qf x)"
  apply (rule cspF_rw_left, rule cspF_decompo, simp, simp)
  apply (rule cspF_rw_left, rule cspF_Ext_choice_step)
  apply (simp add: disjnt_def Int_def)
  apply (rule cspF_decompo, force, auto)
  apply (erule_tac x="a" in allE, auto)
  apply (rule cspF_rw_left, rule cspF_IF)+
  apply (rule cspF_rw_right, rule cspF_IF)+
  apply (simp)
  apply (erule_tac x="a" in allE, auto)
  apply (rule cspF_rw_left, rule cspF_IF)+
  apply (rule cspF_rw_right, rule cspF_IF)+
  by (simp)


lemma cspF_Ext_choice_step_disjnt_Ext_pre_choice :
    "disjnt X Y \<Longrightarrow>
     (? :X -> Pf) [+] (? :Y -> Qf) =F[M,M] ? x:(X \<union> Y) -> (IF (x \<in> X) THEN Pf x
                                                           ELSE Qf x)"
by (rule cspF_Ext_choice_step_disjnt, simp_all)


lemma cspF_Ext_choice_step_choice:
    "P =F[M,M] (? :X -> Pf) \<Longrightarrow>
     Q =F[M,M] (? :Y -> Qf) \<Longrightarrow>
     P [+] Q =F[M,M] ? x:(X \<inter> Y) -> (Pf x |~| Qf x)
                     [+] ? x:(X - Y) -> Pf x
                     [+] ? x:(Y - X) -> Qf x"
  apply (rule cspF_rw_left, rule cspF_decompo, simp, simp)
  apply (rule cspF_rw_left, rule cspF_Ext_choice_step)
  apply (rule cspF_rw_right)
  apply (rule cspF_rw_left, rule cspF_decompo)
  apply (rule cspF_Ext_choice_step, rule cspF_reflex)
  apply (rule cspF_Ext_choice_step)
  apply (rule cspF_decompo, force)
  apply (auto)
  apply (rule cspF_rw_left, rule cspF_IF)
  apply (rule cspF_rw_right, rule cspF_IF)+
  apply (rule cspF_decompo, simp_all)
  apply (rule cspF_rw_left, rule cspF_IF)+
  apply (rule cspF_rw_right, rule cspF_IF)+
  apply (simp)
  apply (rule cspF_rw_left, rule cspF_IF)+
  apply (rule cspF_rw_right, rule cspF_IF)+
  apply (simp)
  done

(*********************************************************
                    Parallel expansion
 *********************************************************)

(* set 1 *)

lemma cspF_Parallel_step_set1:
  "[| Ya - insert Tick (Ev ` X) = Za - insert Tick (Ev ` X) ;
       Ev ` Y Int Ya = {}; Ev ` Z Int Za = {} |]
   ==> Ev ` (X Int Y Int Z) Int (Ya Un Za) = {}"
by (auto)

(* set 2 *)

lemma cspF_Parallel_step_set2:
  "[| Ya - insert Tick (Ev ` X) = Za - insert Tick (Ev ` X) ;
       Ev ` Y Int Ya = {}; Ev ` Z Int Za = {} |]
   ==> Ev ` (Y - X) Int (Ya Un Za) = {}"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add: image_set_diff)
 apply (simp add: in_Ev_set)
 apply (elim conjE exE)

 apply (erule disjE)
  apply (fast)
    (* *)
  apply (simp)
   apply (case_tac "Ev a : Ya")
   apply (fast)
   apply (rotate_tac 1)
   apply (erule equalityE)
   apply (rotate_tac -1)
   apply (erule subsetE)
   apply (drule_tac x="Ev a" in bspec, fast)
   apply (simp)
  apply (fast)
done

(* set 3 *)

lemma cspF_Parallel_step_set3:
  "[| Ya - insert Tick (Ev ` X) = Za - insert Tick (Ev ` X) ;
       Ev ` Y Int Ya = {}; Ev ` Z Int Za = {} |]
   ==> Ev ` (Z - X) Int (Ya Un Za) = {}"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add: image_set_diff)
 apply (simp add: in_Ev_set)
 apply (elim conjE exE)
 apply (erule disjE)
  apply (simp)
   apply (case_tac "Ev a : Za")
   apply (fast)
   apply (rotate_tac 1)
   apply (erule equalityE)
   apply (erule subsetE)
   apply (drule_tac x="Ev a" in bspec, fast)
   apply (simp)
  apply (fast)
    (* *)
  apply (simp)
done

(* set 4 *)

lemma cspF_Parallel_step_set4:
  "Ev ` (X Int Y Int Z Un (Y - X) Un (Z - X)) Int Xa = {} 
   ==> Xa =
       Xa - insert Tick (Ev ` X) Un (Xa Int insert Tick (Ev ` X) - Ev ` Y) Un
      (Xa - insert Tick (Ev ` X) Un (Xa Int insert Tick (Ev ` X) - Ev ` Z))"
by (auto)

(* set 5 *)

lemma cspF_Parallel_step_set5:
  "Ev ` (X Int Y Int Z Un (Y - X) Un (Z - X)) Int Xa = {} 
   ==> Ev ` Y Int
      (Xa - insert Tick (Ev ` X) Un (Xa Int insert Tick (Ev ` X) - Ev ` Y)) = {} &
       Ev ` Z Int
      (Xa - insert Tick (Ev ` X) Un (Xa Int insert Tick (Ev ` X) - Ev ` Z)) = {}"
by (auto)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Parallel_step: 
  "(? :Y -> Pf) |[X]| (? :Z -> Qf) =F[M,M]
      ? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ? x:Z -> Qf x)
                                     |~| (? x:Y -> Pf x |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ? x:Z -> Qf x)
               ELSE (? x:Y -> Pf x |[X]| Qf x)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Parallel_step)
apply (rule order_antisym)

(* => *)
apply (rule)
apply (simp add: in_failures)
apply (elim disjE conjE exE)

 (* (nil,nil) *)
 apply (simp add: image_Un Int_Un_distrib2)
 apply (simp add: cspF_Parallel_step_set1
                  cspF_Parallel_step_set2
                  cspF_Parallel_step_set3)

 (* (nil,Ev) *)
 apply (simp)
 apply (insert trace_nil_or_Tick_or_Ev)
 apply (drule_tac x="s" in spec)

 apply (erule disjE, simp)
 apply (erule disjE, simp)
 apply (elim conjE exE, simp)
 apply (simp add: par_tr_head)
 
 apply (rule_tac x="a" in exI)
 apply (rule_tac x="sc" in exI)
 apply (simp)

 apply (case_tac "a : Y")
  apply (simp)
  apply (rule disjI2)
  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Za" in exI)
  apply (simp)
  apply (rule_tac x="<>" in exI)
  apply (rule_tac x="sb" in exI)
  apply (simp)
  (* "aa ~: Y" *)
  apply (simp)
  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Za" in exI)
  apply (simp)
  apply (rule_tac x="<>" in exI)
  apply (rule_tac x="sb" in exI)
  apply (simp)

 (* (Ev,nil) *)
 apply (simp)
 apply (drule_tac x="s" in spec)

 apply (erule disjE, simp)
 apply (erule disjE, simp)
 apply (elim conjE exE, simp)
 apply (simp add: par_tr_head)
 
 apply (rule_tac x="a" in exI)
 apply (rule_tac x="sc" in exI)
 apply (simp)

 apply (case_tac "a : Z")
  apply (simp)
  apply (rule disjI1)
  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Za" in exI)
  apply (simp)
  apply (rule_tac x="sb" in exI)
  apply (rule_tac x="<>" in exI)
  apply (simp)
  (* "a ~: Z" *)
  apply (simp)
  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Za" in exI)
  apply (simp)
  apply (rule_tac x="sb" in exI)
  apply (rule_tac x="<>" in exI)
  apply (simp)

 (* (Ev,Ev) *)
 apply (drule_tac x="s" in spec)
 apply (erule disjE, simp)
 apply (erule disjE, simp)
 apply (elim conjE exE, simp)
 apply (simp add: par_tr_head)
 apply (elim disjE conjE exE, simp)

  (* sync *)
  apply (rule_tac x="aa" in exI)
  apply (rule_tac x="sd" in exI)
  apply (simp)
  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Za" in exI)
  apply (simp)
  apply (rule_tac x="sb" in exI)
  apply (rule_tac x="sc" in exI)
  apply (simp)

  (* left *)
  apply (simp)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="sd" in exI)
  apply (simp)

  apply (case_tac "a : Z")
   apply (simp)
   apply (rule disjI1)
   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<Ev aa> ^^^ sc" in exI)
   apply (simp)
   (* "a ~: Z" *)
   apply (simp)
   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<Ev aa> ^^^ sc" in exI)
   apply (simp)

  (* right *)
  apply (simp)
  apply (rule_tac x="aa" in exI)
  apply (rule_tac x="sd" in exI)
  apply (simp)

  apply (case_tac "aa : Y")
   apply (simp)
   apply (rule disjI2)
   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="sc" in exI)
   apply (simp)
   (* "aa ~: Y" *)
   apply (simp)
   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="sc" in exI)
   apply (simp)

(* <= *)

apply (rule)
apply (simp add: in_failures)
apply (elim disjE conjE exE)

 (* nil *)
 apply (simp)
 apply (rule_tac x="(Xa - insert Tick (Ev ` X)) Un
                   ((Xa Int insert Tick (Ev ` X)) - Ev ` Y)" in exI)
 apply (rule_tac x="(Xa - insert Tick (Ev ` X)) Un
                   ((Xa Int insert Tick (Ev ` X)) - Ev ` Z)" in exI)
 apply (simp add: cspF_Parallel_step_set4)
 apply (rule conjI, force)
 apply (simp add: cspF_Parallel_step_set5)

 (* sync *)
 apply (simp add: in_failures)
 apply (elim conjE exE, simp)
 apply (rule_tac x="Ya" in exI)
 apply (rule_tac x="Za" in exI)
 apply (simp)
 apply (rule_tac x="<Ev a> ^^^ sb" in exI)
 apply (rule_tac x="<Ev a> ^^^ t" in exI)
 apply (simp add: par_tr_head)

 (* left *)
 apply (case_tac "a : Z")
  apply (simp add: in_failures)
  apply (erule disjE)
   apply (elim conjE exE, simp)
   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="t" in exI)
   apply (simp add: par_tr_head)
   (* *)
   apply (elim conjE exE, simp)
   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI)
   apply (simp add: par_tr_head)
  (* "a ~: Z" *)
  apply (simp add: in_failures)
  apply (elim conjE exE, simp)
  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Za" in exI)
  apply (simp)
  apply (rule_tac x="<Ev a> ^^^ sb" in exI)
  apply (rule_tac x="t" in exI)
  apply (simp add: par_tr_head)

 (* right *)
 apply (case_tac "a : Y")
  apply (simp add: in_failures)
  apply (erule disjE)
   apply (elim conjE exE, simp)
   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="t" in exI)
   apply (simp add: par_tr_head)
   (* *)
   apply (elim conjE exE, simp)
   apply (rule_tac x="Ya" in exI)
   apply (rule_tac x="Za" in exI)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<Ev a> ^^^ t" in exI)
   apply (simp add: par_tr_head)
  (* "a ~: Y" *)
  apply (simp add: in_failures)
  apply (elim conjE exE, simp)
  apply (rule_tac x="Ya" in exI)
  apply (rule_tac x="Za" in exI)
  apply (simp)
  apply (rule_tac x="sb" in exI)
  apply (rule_tac x="<Ev a> ^^^ t" in exI)
  apply (simp add: par_tr_head)
done


(*** Parallel ***)

lemma cspF_Parallel_step_choice:
    "P =F[M,M] (? :Y -> Pf) \<Longrightarrow>
     Q =F[M,M] (? :Z -> Qf) \<Longrightarrow>
     P |[X]| Q =F[M,M] ? x:(X Int Y Int Z) -> (Pf x |[X]| Qf x)
                       [+] ? x:(Y-X) -> (Pf x |[X]| ? x:Z -> Qf x)
                       [+] ? x:(Z-X) -> (? x:Y -> Pf x |[X]| Qf x)"
  apply (rule cspF_rw_left, rule cspF_decompo, simp, simp, simp)
  apply (rule cspF_rw_left, rule cspF_Parallel_step)
  apply (rule cspF_rw_right, rule cspF_decompo)
  apply (rule cspF_Ext_choice_step, rule cspF_reflex)
  apply (rule cspF_rw_right)
  apply (rule cspF_Ext_choice_step)
  apply (rule cspF_decompo, simp)
  apply (auto)
  apply (rule cspF_rw_left, rule cspF_IF)+
  apply (rule cspF_rw_right, rule cspF_IF)+
  apply (simp)
  apply (rule cspF_rw_left, rule cspF_IF)+
  apply (rule cspF_decompo, simp)
  apply (rule cspF_decompo)
  apply (rule cspF_rw_right, rule cspF_IF)+
  apply (simp)
  apply (simp)
  apply (rule cspF_rw_left, rule cspF_IF)+
  apply (rule cspF_rw_right, rule cspF_IF)+
  apply (simp)
  apply (rule cspF_rw_left, rule cspF_IF)+
  apply (rule cspF_decompo, simp)
  apply (rule cspF_decompo)
  apply (rule cspF_rw_right, rule cspF_IF)+
  apply (simp)
  apply (simp)
  apply (rule cspF_decompo, simp)
  apply (rule cspF_rw_right, rule cspF_IF)+
  apply (simp)
  apply (simp)
  done

lemma cspF_Parallel_to_Ext_choice:
     "(? :Y -> Pf) |[X]| ? :Z -> Qf =F[M,M] ? x:(X Int Y Int Z) -> (Pf x |[X]| Qf x)
                                            [+] ? x:(Y-X) -> (Pf x |[X]| ? x:Z -> Qf x)
                                            [+] ? x:(Z-X) -> (? x:Y -> Pf x |[X]| Qf x)"
  by (simp add: cspF_Parallel_step_choice)


lemma cspF_Parallel_step_left :
    "P =F[M,M] ? x:X -> Pf x \<Longrightarrow> X \<inter> Y = {} \<Longrightarrow> Z \<subseteq> Y \<Longrightarrow>
     P |[Y]| (? :Z -> Qf) =F[M,M] ? x:X -> ((Pf x) |[Y]| ? :Z -> Qf)"
  apply (rule cspF_rw_left, rule cspF_decompo, simp, simp, rule cspF_reflex)
  apply (rule cspF_rw_left, rule cspF_Parallel_step)
  apply (rule cspF_decompo, force, simp add: Int_commute disjoint_iff)
  apply (simp add: contra_subsetD)
  apply (rule cspF_rw_left, rule cspF_IF)+
  by (rule cspF_decompo, simp_all)

lemma cspF_Parallel_step_disjoint_range_left :
    "disjoint_range h f \<Longrightarrow> disjoint_range h g \<Longrightarrow>
     (? x:{| h |}\<^sub>c -> Pf x) |[{| f, g |}\<^sub>c]| (? y:{| g |}\<^sub>c -> Qf y) =F[M,M]
     (? x:{| h |}\<^sub>c -> ((Pf x) |[{| f, g |}\<^sub>c]| ? y:{| g |}\<^sub>c -> Qf y))"
  apply (rule cspF_rw_left, rule cspF_Parallel_step)
  apply (auto simp add: disjoint_range_simps)
  apply (rule cspF_decompo, force)
  apply (auto simp add: disjoint_range_simps)
  apply (rule cspF_rw_left, rule cspF_IF)+
  by (simp)


lemma cspF_Parallel_step_disjoint_range_right :
    "disjoint_range h f \<Longrightarrow> disjoint_range h g \<Longrightarrow>
     (? x:{| g |}\<^sub>c -> Pf x) |[{| f, g |}\<^sub>c]| (? y:{| h |}\<^sub>c -> Qf y) =F[M,M]
     (? y:{| h |}\<^sub>c -> ((? x:{| g |}\<^sub>c -> Pf x) |[{| f, g |}\<^sub>c]| Qf y))"
  apply (rule cspF_rw_left, rule cspF_Parallel_step)
  apply (auto simp add: disjoint_range_simps)
  apply (rule cspF_decompo, force)
  apply (auto simp add: disjoint_range_simps)
  apply (rule cspF_rw_left, rule cspF_IF)+
  by (simp)


(*** Interleave ***)

lemma cspF_Interleave_step: 
  "(? :Y -> Pf) ||| (? :Z -> Qf) =F[M,M]
      ? x:(Y Un Z)
         -> IF (x : Y & x : Z) THEN ((Pf x ||| ? x:Z -> Qf x) |~| (? x:Y -> Pf x ||| Qf x))
            ELSE IF (x : Y) THEN (Pf x ||| ? x:Z -> Qf x)
                 ELSE (? x:Y -> Pf x ||| Qf x)"
  apply (rule cspF_rw_left, rule cspF_Parallel_step, simp)
  apply (rule cspF_decompo, simp)
  by (rule cspF_rw_left, rule cspF_IF, simp)

lemma cspF_Interleave_step_choice :
  "P =F[M,M] (? :Y -> Pf) \<Longrightarrow>
     Q =F[M,M] (? :Z -> Qf) \<Longrightarrow>
     P ||| Q =F[M,M] ? x:Y -> (Pf x ||| ? x:Z -> Qf x)
                     [+] ? x:Z -> (? x:Y -> Pf x ||| Qf x)"
  apply (rule cspF_rw_left, rule cspF_Parallel_step_choice, simp_all)
  apply (rule cspF_rw_left, rule cspF_Ext_choice_assoc_sym)
  apply (rule cspF_rw_left, rule cspF_decompo)
    apply (rule cspF_STOP_step[THEN cspF_sym])
    apply (rule cspF_reflex)
  apply (rule cspF_rw_left, rule cspF_unit)
  by (simp)


(*********************************************************
                      Hide expansion
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Hiding_step: 
  "(? :Y -> Pf) -- X =F[M,M] 
      IF (Y Int X = {}) THEN (? x:Y -> (Pf x -- X))
                         ELSE ((? x:(Y-X) -> (Pf x -- X)) 
                               [> (! x:(Y Int X) .. (Pf x -- X)))"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Hiding_step)
apply (rule order_antisym)

 (* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim conjE exE)
 apply (erule disjE)
  (* not hidden *)
  apply (simp)
  apply (case_tac "Y Int X ~= {}", fast)
  apply (simp)
  apply (fast)
  (* hidden *)
  apply (elim conjE exE)
   apply (simp)

  apply (case_tac "a : X")
  apply (case_tac "Y Int X = {}", fast)
   apply (simp)
   apply (case_tac "sb --tr X = <>")
   apply (rule disjI1)
   apply (simp)
   apply (rule_tac x="a" in bexI)
   apply (rule_tac x="sb" in exI)
   apply (simp)
   apply (simp)

   apply (rule disjI2)
   apply (simp)
   apply (rule disjI2)
   apply (rule_tac x="a" in bexI)
   apply (rule_tac x="sb" in exI)
   apply (simp)
   apply (simp)

  (* a ~: X *)
   apply (case_tac "Y Int X = {}")
    apply (simp)
    apply (fast)
   (* Y Int X ~= {} *)
    apply (simp)
    apply (fast)

 (* <= *)
 apply (rule)
 apply (case_tac "Y Int X = {}")
  apply (simp add: in_failures)
  apply (erule disjE)
   apply (rule_tac x="<>" in exI)
   apply (simp)
   apply (fast)
  (* *)
   apply (elim conjE exE)
   apply (case_tac "a : X", fast)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (simp)

 (* Y Int X ~= {} *)
 apply (simp add: in_failures_IF)
 apply (simp add: in_failures_Timeout)
 apply (elim disjE)
  (* 1 *)
  apply (simp add: in_failures)
  apply (elim conjE exE bexE)
  apply (rule_tac x="<Ev a> ^^^ sa" in exI)
  apply (simp)

  (* 2 *)
  apply (simp add: in_failures)
  apply (elim conjE, simp)
  apply (elim conjE exE)
  apply (rule_tac x="<Ev a> ^^^ sb" in exI)
  apply (simp)
  (* 3 *)
  apply (simp add: in_failures)
  apply (simp add: in_traces)
done

(*********************************************************
                    Renaming expansion
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Renaming_step:
  "(? :X -> Pf) [[r]] =F[M,M] 
    ? y:(r `` X) -> (! x:{x. x:X & (x,y):r} .. (Pf x)[[r]])"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Renaming_step)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE exE)
  (* 1 *)
  apply (simp add: ren_inv_def)
  apply (force)
  (* 2 *)
  apply (simp add: ren_tr_decompo)
  apply (elim conjE exE)
  apply (rule disjI2)
  apply (rule_tac x="b" in exI)
  apply (rule_tac x="t" in exI)
  apply (simp)
  apply (fast)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE exE)
  (* 1 *)
  apply (simp add: ren_inv_def)
  apply (force)
  (* 2 *)
  apply (rule_tac x="<Ev aa> ^^^ sb" in exI)
  apply (simp)
done

(*********************************************************
            Sequential composition expansion
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Seq_compo_step: 
  "(? :X -> Pf) ;; Q =F[M,M] ? x:X -> (Pf x ;; Q)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Seq_compo_step)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim conjE exE disjE)

 apply (simp_all)
 apply (insert trace_nil_or_Tick_or_Ev)
 apply (drule_tac x="sa" in spec)
 apply (erule disjE)
 apply (simp add: in_traces)
 apply (erule disjE)
 apply (simp)

 apply (elim conjE exE)
 apply (simp)
 apply (rule_tac x="a" in exI)
 apply (rule_tac x="sb ^^^ t" in exI)
 apply (simp add: appt_assoc)
 apply (simp add: in_traces)
 apply (fast)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (erule disjE)
 (* 1 *)
  apply (rule disjI1)
  apply (simp)
  apply (fast)

 (* 2 *)
  apply (elim conjE exE disjE)

  (* 2-1 *)
   apply (simp)

  (* 2-2 *)
   apply (rule disjI2)
   apply (simp)
   apply (rule_tac x="<Ev a> ^^^ sb" in exI)
   apply (rule_tac x="t" in exI, simp)
   apply (simp add: appt_assoc)
   apply (simp add: in_traces)
done

(*********************************************************
                    Depth_rest expansion
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Depth_rest_step:
  "(? :X -> Pf) |. (Suc n) =F[M,M] ? x:X -> (Pf x |. n)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Depth_rest_step)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE exE)
 apply (simp_all)
 apply (rule_tac x="a" in exI)
 apply (rule_tac x="sb" in exI)
 apply (simp)
 apply (rule disjI2)
 apply (insert trace_nil_or_Tick_or_Ev)
 apply (drule_tac x="sa" in spec)
 apply (elim conjE exE disjE)
 apply (simp_all)
 apply (simp add: appt_assoc)
 apply (force)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE exE)
 apply (simp_all)
 apply (rule_tac x="<Ev a> ^^^ sb" in exI)
 apply (simp add: appt_assoc)
done

(*********************************************************)

lemmas cspF_step = cspF_STOP_step       cspF_Act_prefix_step 
                   cspF_Ext_choice_step cspF_Parallel_step
                   cspF_Hiding_step     cspF_Renaming_step
                   cspF_Seq_compo_step  cspF_Depth_rest_step

lemmas cspF_light_step = cspF_STOP_step  cspF_Act_prefix_step 


lemmas cspF_step_rw = cspF_STOP_step_DIV       cspF_Act_prefix_step 
                   cspF_Ext_choice_step cspF_Parallel_step
                   cspF_Hiding_step     cspF_Renaming_step
                   cspF_Seq_compo_step  cspF_Depth_rest_step

lemmas cspF_light_step_rw = cspF_STOP_step_DIV  cspF_Act_prefix_step 

end
