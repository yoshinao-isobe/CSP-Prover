           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005 (modified)    |
            |                 August 2005 (modified)    |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |               December 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_traces
imports  CSP_T_semantics
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*********************************************************
                        DomT
 *********************************************************)

(*--------------------------------*
 |             STOP               |
 *--------------------------------*)

lemma in_traces_STOP: "(t :t traces(STOP) M) = (t = <>)"
by (simp add: traces_iff)

(*--------------------------------*
 |             SKIP               |
 *--------------------------------*)

lemma in_traces_SKIP: "(t :t traces(SKIP) M) = (t = <> | t = <Tick>)"
by (simp add: traces_iff)

(*--------------------------------*
 |              DIV               |
 *--------------------------------*)

(*** DIV ***)

lemma in_traces_DIV: "(t :t traces(DIV) M) = (t = <>)"
by (simp add: traces_iff)

(*--------------------------------*
 |          Act_prefix            |
 *--------------------------------*)

(*** Act_prefix_domT ***)

lemma Act_prefix_domT: 
  "{t. t = <> | (EX s. t = <Ev a> ^^^ s & s :t T)} : domT"
apply (simp add: domT_def HC_T1_def)
apply (rule conjI)
apply (rule_tac x="<>" in exI, simp)

apply (simp add: prefix_closed_def)
apply (intro allI impI)
apply (elim conjE exE)

apply (erule disjE, simp)    (* <> *)

apply (elim conjE exE, simp)
apply (erule disjE, simp)    (* <> *)

apply (elim conjE exE, simp)
apply (rule memT_prefix_closed)
by (simp_all)

(*** Act_prefix ***)

lemma in_traces_Act_prefix: 
  "t :t traces(a -> P) M = (t = <> | (EX s. t = <Ev a> ^^^ s & s :t traces(P) M))"
apply (simp add: traces_iff)
by (simp add: CollectT_open_memT Act_prefix_domT)

(*--------------------------------*
 |        Ext_pre_choice          |
 *--------------------------------*)

(*** Ext_pre_choice_domT ***)

lemma Ext_pre_choice_domT: 
  "{t. t = <> | 
       (EX a s. t = <Ev a> ^^^ s & s :t Tf a & a : X) } : domT"
apply (simp add: domT_def HC_T1_def)
apply (rule conjI)
apply (rule_tac x="<>" in exI, simp)

apply (simp add: prefix_closed_def)
apply (intro allI impI)
apply (elim conjE exE)

apply (erule disjE, simp)    (* <> *)

apply (elim conjE exE, simp)
apply (erule disjE, simp)    (* <> *)

apply (elim conjE exE, simp)
apply (rule memT_prefix_closed)
by (simp_all)

(*** Ext_pre_choice ***)

lemma in_traces_Ext_pre_choice: 
  "(t :t traces(? :X -> Pf) M) =
   (t = <> | (EX a s. t = <Ev a> ^^^ s & s :t traces(Pf a) M & a : X))"
apply (simp add: traces_iff)
by (simp add: CollectT_open_memT Ext_pre_choice_domT)

(*--------------------------------*
 |          Ext_choice            |
 *--------------------------------*)

(*** Ext_choice_memT ***)

lemma in_traces_Ext_choice: 
  "(t :t traces(P [+] Q) M) = (t :t traces(P) M | t :t traces(Q) M)"
by (simp add: traces_iff)

(*** Semantics for Inductive external choice on T ***)

lemma in_traces_Inductive_ext_choice:
    "u :t traces ([+] l) M = (u = <> \<or> (\<exists> P\<in>(set l). u :t traces P M))"
by (induct_tac l, simp_all add: traces_iff, safe)

theorem traces_Inductive_ext_choice:
    "traces ([+] l) M = {u. u = <> \<or> (\<exists> P\<in> set l. u :t traces P M)}t"
by (simp add: in_traces_Inductive_ext_choice[THEN sym])


(*** Semantics for Replicated external choice on T ***)

lemma in_traces_Rep_ext_choice:
  "finite X \<Longrightarrow> l = (SOME l. l isListOf X)
   \<Longrightarrow> (u :t traces ([+] x:X .. PXf x) M) = (u = <> \<or> (\<exists> P\<in> (set (map PXf l)). u :t traces P M))"
by (simp add: Rep_ext_choice_def in_traces_Inductive_ext_choice)

theorem traces_Rep_ext_choice:
  "finite X \<Longrightarrow> l = (SOME l. l isListOf X)
   \<Longrightarrow> traces ([+] x:X .. PXf x) M = {u. u = <> \<or> (\<exists> P\<in>(set (map PXf l)). u :t traces P M)}t"
by (simp add: Rep_ext_choice_def traces_Inductive_ext_choice)



subsection \<open> Traces Model Comparison to Ext_pre_choice operator \<close>

text \<open> Inductive and Replicated external choice operators to Ext_prefix_choice operator

The traces of a Ext_pre_choice are not 

 "traces(? :X -> Pf) = (%M. {t. t = <> | 
                             (EX a s. t = <Ev a> ^^^ s & s :t traces(Pf a) M & a : X) }t)"
\<close>


lemma Inductive_ext_choice_domT: 
    "\<And>a . a \<in> X \<Longrightarrow> {t. t = <> \<or> (EX s. t = <Ev a> ^^^ s \<and> s : Rep_domT (Tf a)) } \<in> domT"
  apply (simp add: domT_def HC_T1_def)
  apply (rule conjI)
  apply (rule_tac x="<>" in exI, simp)
  
  apply (simp add: prefix_closed_def)
  apply (intro allI impI)
  apply (elim conjE exE)
  
  apply (erule disjE, simp)    (* <> *)
  
  apply (elim conjE exE, simp)
  apply (erule disjE, simp)    (* <> *)
  
  apply (elim conjE exE, simp)
  apply (rule Rep_domT_is_prefix_closed_unfold)
by (simp_all)


lemma Inductive_ext_choice_Rep_domT:
    "P \<in> X \<Longrightarrow> Rep_domT {t. t = <> \<or> (\<exists>s. t = <Ev P> ^^^ s \<and> s \<in> Rep_domT (traces (PXf P) M))}t
               = {t. t = <> \<or> (\<exists>s. t = <Ev P> ^^^ s \<and> s \<in> Rep_domT (traces (PXf P) M))}"
by (rule Abs_domT_inverse, rule Inductive_ext_choice_domT, simp)


theorem traces_Inductive_ext_choice_to_Ext_pre_choice :
    "l isListOf X \<Longrightarrow> traces([+] map (\<lambda> e . e -> PXf e) l) M = traces(? :X -> PXf) M"
  apply (simp add: traces_Inductive_ext_choice isListOf_set_eq)
  apply (simp add: traces.simps)
  apply (simp add: memT_def Inductive_ext_choice_Rep_domT)
  apply (rule set_CollectT_eq, rule Collect_cong)
by (fast)


theorem cspT_Inductive_ext_choice_to_Ext_pre_choice :
    "l isListOf X \<Longrightarrow> [+] map (\<lambda> e . e -> PXf e) l =T[M,M] ? :X -> PXf"
by (simp add: cspT_eqT_semantics traces_Inductive_ext_choice_to_Ext_pre_choice)


theorem cspT_Ext_pre_choice_to_Rep_ext_choice :
    "finite X \<Longrightarrow> [+]X .. (\<lambda>x . x -> PXf x) =T[M,M] ? :X -> (\<lambda>x . PXf x)"
  apply (simp add: Rep_ext_choice_def)
  apply (rule cspT_Inductive_ext_choice_to_Ext_pre_choice)
by (rule someI2_ex, rule isListOf_EX, simp, simp)




(*--------------------------------*
 |          Int_choice            |
 *--------------------------------*)

(*** Int_choice_memT ***)

lemma in_traces_Int_choice: 
  "(t :t traces(P |~| Q) M) = (t :t traces(P) M| t :t traces(Q) M)"
by (simp add: traces_iff)

(*--------------------------------*
 |        Rep_int_choice          |
 *--------------------------------*)

(*** Rep_int_choice_domT ***)

lemma Rep_int_choice_domT: 
  "{t. t = <> | (EX a:X. t :t Tf a) } : domT"
apply (simp add: domT_def HC_T1_def)
apply (rule conjI)
apply (rule_tac x="<>" in exI, simp)

apply (simp add: prefix_closed_def)
apply (intro allI impI)
apply (elim conjE exE)

apply (erule disjE, simp)    (* <> *)

apply (elim conjE bexE)
apply (rule disjI2)
apply (rule_tac x="a" in bexI)
apply (rule memT_prefix_closed)
by (simp_all)

(*** Union_proc ***)

lemma in_traces_Union_proc: 
   "(t :t {t. t = <> | (EX a:X. t :t Tf a)}t) 
  = (t = <> | (EX a:X. t :t Tf a))"
apply (insert Rep_int_choice_domT[of X Tf])
apply (simp add: CollectT_open_memT)
done

lemma in_traces_UNIV_Union_proc: 
   "(t :t {t. EX a. t :t Tf a}t) 
  = (EX a. t :t Tf a)"
apply (insert in_traces_Union_proc[of t UNIV Tf])
apply (simp)
apply (subgoal_tac "{t. t = <> | (EX a. t :t Tf a)}
                  = {t. EX a. t :t Tf a}")
by (auto)

(*** Rep_int_choice ***)

lemma in_traces_Rep_int_choice_sum: 
   "(t :t traces(!! :C .. Pf) M) =
    (t = <> | (EX c: sumset C. t :t traces(Pf c) M))"
apply (simp add: traces_iff)
apply (simp add: in_traces_Union_proc)
done

lemma in_traces_Rep_int_choice_nat: 
   "(t :t traces(!nat :N .. Pf) M) = (t = <> | (EX n:N. t :t traces(Pf n) M))"
by (simp add: Rep_int_choice_ss_def in_traces_Rep_int_choice_sum)

lemma in_traces_Rep_int_choice_set: 
   "(t :t traces(!set :Xs .. Pf) M) = (t = <> | (EX X:Xs. t :t traces(Pf X) M))"
by (simp add: Rep_int_choice_ss_def in_traces_Rep_int_choice_sum)

lemma in_traces_Rep_int_choice_com: 
   "(t :t traces(! :X .. Pf) M) = (t = <> | (EX a:X. t :t traces(Pf a) M))"
apply (simp add: traces_iff)
apply (simp add: in_traces_Union_proc)
done

lemma in_traces_Rep_int_choice_f: 
   "inj f ==> (t :t traces(!<f> :X .. Pf) M) = (t = <> | (EX a:X. t :t traces(Pf a) M))"
apply (simp add: traces_iff)
apply (simp add: in_traces_Union_proc)
done

lemmas in_traces_Rep_int_choice = in_traces_Rep_int_choice_sum
                                  in_traces_Rep_int_choice_set
                                  in_traces_Rep_int_choice_nat
                                  in_traces_Rep_int_choice_com
                                  in_traces_Rep_int_choice_f

(*--------------------------------*
 |               IF               |
 *--------------------------------*)

(*** IF ***)

lemma in_traces_IF: 
  "(t :t traces(IF b THEN P ELSE Q) M)
 = (if b then t :t traces(P) M else t :t traces(Q) M)"
by (simp add: traces_iff)

(*--------------------------------*
 |           Parallel             |
 *--------------------------------*)

(*** Parallel_domT ***)

lemma Parallel_domT : 
  "{u. EX s t. u : s |[X]|tr t & s :t T & t :t S} : domT"
apply (simp add: domT_def HC_T1_def)
apply (rule conjI)
apply (rule_tac x="<>" in exI, simp)

(* prefix closed *)
apply (simp add: prefix_closed_def)
apply (intro allI impI)
apply (elim conjE exE)
apply (erule par_tr_prefixE, simp)
apply (rule_tac x="s'" in exI)
apply (rule_tac x="t'" in exI)
apply (simp)

apply (rule conjI)
by (rule memT_prefix_closed, simp_all)+

(*** Parallel ***)

lemma in_traces_Parallel:
  "(u :t traces(P |[X]| Q) M) = 
   (EX s t. u : s |[X]|tr t & s :t traces(P) M & t :t traces(Q) M)"
apply (simp add: traces_iff)
by (simp add: CollectT_open_memT Parallel_domT)



(*** Semantics for Inductive interleave on T ***)

abbreviation
    "in_t_Induct_interleave u l M
     == ((l = [] \<and> (u = <> \<or> u = <Tick>))
         \<or> (l \<noteq> [] \<and> (\<exists>s t. u \<in> s |[{}]|tr t
                           \<and> s :t traces (hd l) M
                           \<and> t :t traces ( ||| tl l) M)))"

lemma set_CollectT_commute_left :
    "{u. Q u \<or> u \<in>t S \<or> P u}t
     = {u. u \<in>t S \<or> Q u \<or> P u}t"
by (rule set_CollectT_eq, force)

lemma in_traces_Inductive_interleave :
    "u :t traces ( ||| l) M = in_t_Induct_interleave u l M"
  apply (induct_tac l, simp add: traces_iff)
by (simp add: in_traces_Parallel)


theorem traces_Inductive_interleave :
    "traces ( ||| l) M = {u. in_t_Induct_interleave u l M }t"
by (simp add: in_traces_Inductive_interleave[THEN sym])

(*** Semantics for Replicated interleaving on T ***)

lemma in_traces_Rep_interleaving :
    "finite X \<Longrightarrow> map PXf (SOME x. x isListOf X) = Ps
     \<Longrightarrow> u :t traces ( ||| X .. PXf) M = in_t_Induct_interleave u Ps M"
  apply (simp (no_asm_use) only: Rep_interleaving_def)
by (rule trans, rule in_traces_Inductive_interleave, simp)

theorem traces_Rep_interleaving :
    "finite X \<Longrightarrow> map PXf (SOME x. x isListOf X) = Ps
     \<Longrightarrow> traces ( ||| X .. PXf) M = {u. in_t_Induct_interleave u Ps M }t"
by (simp add: in_traces_Rep_interleaving[THEN sym])





(*--------------------------------*
 |            Hiding              |
 *--------------------------------*)

(*** Hiding_domT ***)

lemma Hiding_domT : 
  "{t. EX s. t = s --tr X & s :t T } : domT"
apply (simp add: domT_def HC_T1_def)
apply (rule conjI)
apply (rule_tac x="<>" in exI, simp)

(* prefix closed *)
apply (simp add: prefix_closed_def)
apply (intro allI impI)
apply (elim conjE exE)
apply (simp add: hide_tr_prefix)
apply (elim conjE exE)
apply (rule_tac x="ta" in exI)
apply (simp)
apply (rule memT_prefix_closed)
by (simp_all)

(*** Hiding ***)

lemma in_traces_Hiding:
  "(t :t traces(P -- X) M) = 
   (EX s. t = s --tr X & s :t traces(P) M)"
apply (simp add: traces_iff)
by (simp add: CollectT_open_memT Hiding_domT)

(*--------------------------------*
 |           Renaming             |
 *--------------------------------*)

(*** Renaming_domT ***)

lemma Renaming_domT : "{t. EX s. s [[r]]* t & s :t T } : domT"
apply (simp add: domT_def HC_T1_def)
apply (rule conjI)
apply (rule_tac x="<>" in exI, simp)

(* prefix closed *)
apply (simp add: prefix_closed_def)
apply (intro allI impI)
apply (elim conjE exE)
apply (erule ren_tr_prefixE, simp)
apply (rule_tac x="ta" in exI)
apply (simp)
apply (rule memT_prefix_closed)
by (simp_all)

(*** Renaming ***)

lemma in_traces_Renaming:
  "(t :t traces(P [[r]]) M) = (EX s. s [[r]]* t & s :t traces(P) M)"
apply (simp add: traces_iff)
by (simp add: CollectT_open_memT Renaming_domT)

(*--------------------------------*
 |           Seq_compo            |
 *--------------------------------*)

(*** Seq_compo_domT ***)

lemma Seq_compo_domT : 
  "{u. (EX s. u = rmTick s & s :t S ) |
       (EX s t. u = s ^^^ t & s ^^^ <Tick> :t S & t :t T & noTick s ) } : domT"
apply (simp add: domT_def HC_T1_def)
apply (rule conjI)
apply (rule_tac x="<>" in exI)
apply (rule disjI1)
apply (rule_tac x="<>" in exI, simp)

(* prefix closed *)
apply (simp add: prefix_closed_def)

 apply (intro allI impI)
 apply (elim conjE exE)
 apply (erule disjE)

  (* case 1 *)
  apply (elim conjE exE)
  apply (rule disjI1)
  apply (simp add: rmTick_prefix)
  apply (elim conjE exE)
  apply (rule_tac x="u" in exI, simp)
  apply (rule memT_prefix_closed, simp_all)
  
  (* case 2 *)
  apply (elim conjE exE)
  apply (simp add: prefix_def)
  apply (elim exE conjE)
  apply (simp add: appt_decompo)

   apply (erule disjE)
   (* long case *)
   apply (elim conjE exE)
   apply (rule disjI2)
   apply (rule_tac x="sa" in exI, simp)
   apply (rule_tac x="ua" in exI, simp)
   apply (subgoal_tac "prefix ua (ua ^^^ u)")
    apply (rule memT_prefix_closed, simp_all)
   apply (simp)

   (* short case *)
   apply (elim conjE exE)
   apply (rule disjI1)
   apply (rule_tac x="s" in exI)
   apply (case_tac "~ noTick s", simp)
   apply (simp)
   apply (subgoal_tac "prefix s (s ^^^ ua ^^^ <Tick>)")
    apply (rule memT_prefix_closed, simp_all)
   apply (simp)
done

(*** Seq_compo ***)

lemma in_traces_Seq_compo:
  "(u :t traces(P ;; Q) M) =
   ((EX s. u = rmTick s & s :t traces(P) M) |
    (EX s t. u = s ^^^ t & s ^^^ <Tick> :t traces(P) M & t :t traces(Q) M & noTick s))"
apply (simp add: traces_iff)
by (simp add: CollectT_open_memT Seq_compo_domT)

(*--------------------------------*
 |          Depth_rest            |
 *--------------------------------*)

(*** Depth_rest ***)

lemma in_traces_Depth_rest:
  "(t :t traces(P |. n) M) = (t :t traces(P) M & (lengtht t) <= n)"
apply (simp add: traces_iff)
apply (simp add: in_rest_domT)
done

(*--------------------------------*
 |          Proc_name             |
 *--------------------------------*)

(*** Proc_name ***)

lemma in_traces_Proc_name:
  "(t :t traces($p) M) = (t :t M p)"
apply (simp add: traces_iff)
done

(*--------------------------------*
 |             alias              |
 *--------------------------------*)

lemmas traces_domT = Act_prefix_domT     Ext_pre_choice_domT
                     Rep_int_choice_domT Parallel_domT
                     Hiding_domT         Renaming_domT
                     Seq_compo_domT

lemmas in_traces = in_traces_STOP  in_traces_SKIP  in_traces_DIV
                   in_traces_Act_prefix     in_traces_Ext_pre_choice
                   in_traces_Ext_choice     in_traces_Int_choice
                   in_traces_Rep_int_choice in_traces_IF
                   in_traces_Parallel       in_traces_Hiding
                   in_traces_Renaming       in_traces_Seq_compo
                   in_traces_Union_proc     in_traces_UNIV_Union_proc
                   in_traces_Depth_rest     in_traces_Proc_name

(*--------------------------------*
 |            Timeout             |
 *--------------------------------*)

(*** Timemout ***)

lemma in_traces_Timeout1:
  "(t :t traces(P [> Q) M) = (t :t traces(P) M | t :t traces(Q) M)"
apply (simp add: traces_iff)
done

lemma in_traces_Timeout2:
  "(t :t traces(P [>def Q) M) = (t :t traces(P) M | t :t traces(Q) M)"
apply (simp add: Timeout_def traces_iff)
done

lemmas in_traces_Timeout = in_traces_Timeout1 in_traces_Timeout2

(****************** to add them again ******************)

declare disj_not1   [simp]

end
