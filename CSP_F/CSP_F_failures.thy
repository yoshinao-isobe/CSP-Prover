           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005 (modified)    |
            |                 August 2005 (modified)    |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_failures
imports CSP_F_semantics
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*********************************************************
                        setF
 *********************************************************)

(*--------------------------------*
 |             STOP               |
 *--------------------------------*)

(*** STOP_setF ***)

lemma STOP_setF: "{f. EX X. f = (<>, X)} : setF"
by (simp add: setF_def HC_F2_def)

(*** STOP ***)

lemma in_failures_STOP : "(f :f failures(STOP) M) = (EX X. f = (<>, X))"
apply (simp add: failures_iff)
by (simp add: CollectF_open_memF STOP_setF)

(*--------------------------------*
 |             SKIP               |
 *--------------------------------*)

(*** SKIP_setF ***)

lemma SKIP_setF: "{f. (EX X. f = (<>, X) & X <= Evset) |
                      (EX X. f = (<Tick>, X)) } : setF"
by (auto simp add: setF_def HC_F2_def)

(*** SKIP ***)

lemma in_failures_SKIP :
  "(f :f failures(SKIP) M) = ((EX X. f = (<>, X) & X <= Evset) |
                              (EX X. f = (<Tick>, X)))"
apply (simp add: failures_iff)
by (simp add: CollectF_open_memF SKIP_setF)

(*--------------------------------*
 |              DIV               |
 *--------------------------------*)

(*** DIV ***)

lemma in_failures_DIV : "(f ~:f failures(DIV) M)"
by (simp add: failures_iff)

(*--------------------------------*
 |          Act_prefix            |
 *--------------------------------*)

(*** Act_prefix_setF ***)

lemma Act_prefix_setF: 
  "{f. (EX X.   f = (<>,X) & Ev a ~: X) |
       (EX s X. f = (<Ev a> ^^^ s, X) & (s,X) :f F) } : setF"
apply (simp add: setF_def HC_F2_def)
apply (intro allI impI)
apply (elim conjE disjE, force)

apply (elim conjE exE, simp)
apply (rule memF_F2, simp_all)
done

(*** Act_prefix ***)

lemma in_failures_Act_prefix: 
  "(f :f failures(a -> P) M) 
    = ((EX X.   f = (<>,X) & Ev a ~: X) |
       (EX s X. f = (<Ev a> ^^^ s, X) & (s,X) :f failures(P) M))"
apply (simp add: failures_iff)
by (simp add: CollectF_open_memF Act_prefix_setF)

(*--------------------------------*
 |        Ext_pre_choice          |
 *--------------------------------*)

(*** Ext_pre_choice_setF ***)

lemma Ext_pre_choice_setF: 
  "{f. (EX Y. f = (<>,Y) & Ev`X Int Y = {}) |
       (EX a s Y. f = (<Ev a> ^^^ s, Y) & (s,Y) :f Ff a & a : X) } : setF"
apply (simp add: setF_def HC_F2_def)
apply (intro allI impI)
apply (elim conjE disjE, force)

apply (elim conjE exE, simp)
apply (rule memF_F2, simp_all)
done

(*** Ext_pre_choice ***)

lemma in_failures_Ext_pre_choice: 
  "(f :f failures(? :X -> Pf) M) = 
   ((EX Y.     f = (<>,Y) & Ev`X Int Y = {}) |
    (EX a s Y. f = (<Ev a> ^^^ s, Y) & (s,Y) :f failures(Pf a) M & a : X))"
apply (simp add: failures_iff)
by (simp add: CollectF_open_memF Ext_pre_choice_setF)

(*--------------------------------*
 |          Ext_choice            |
 *--------------------------------*)

(*** Ext_choice_setF ***)

lemma Ext_choice_setF: 
  "{f. (EX X. f = (<>, X)) & f :f F & f :f E |
              (EX s. (EX X. f = (s, X)) & (f :f F | f :f E) & s ~= <>) |
              (EX X. f = (<>, X) &
                     (<Tick> :t T | <Tick> :t S) & X <= Evset)} : setF"
apply (simp add: setF_def HC_F2_def)
apply (intro allI impI)
apply (elim conjE disjE)
apply (simp_all)

(* part1 *)
apply (rule disjI1)
apply (rule conjI)
apply (rule memF_F2, simp_all)
apply (rule memF_F2, simp_all)

(* part2 *)
apply (rule disjI1)
apply (rule memF_F2, simp_all)
apply (rule disjI2)
apply (rule memF_F2, simp_all)

(* part3 *)
apply (auto)
done

(*** Ext_choice ***)

lemma in_failures_Ext_choice: 
  "(f :f failures(P [+] Q) M) =
    ((EX X. f = (<>, X)) & f :f failures P M & f :f failures Q M |
     (EX s. (EX X. f = (s, X)) &
            (f :f failures P M | f :f failures Q M) & s ~= <>) |
     (EX X. f = (<>, X) &
            (<Tick> :t traces P (fstF o M) | <Tick> :t traces Q (fstF o M)) & X <= Evset))"
apply (simp add: failures_iff)
by (simp only: CollectF_open_memF Ext_choice_setF)

(*--------------------------------*
 |          Int_choice            |
 *--------------------------------*)

(*** Int_choice ***)

lemma in_failures_Int_choice: 
  "(f :f failures(P |~| Q) M) = (f :f failures(P) M | f :f failures(Q) M)"
by (simp add: failures_iff)

(*--------------------------------*
 |        Rep_int_choice          |
 *--------------------------------*)

(*** Rep_int_choice_setF ***)

lemma Rep_int_choice_setF: 
  "{f. EX a:X. f :f Ff a} : setF"
apply (simp add: setF_def HC_F2_def)
apply (intro allI impI)
apply (elim conjE bexE)
apply (rule_tac x="a" in bexI)
apply (rule memF_F2, simp_all)
done

(*** Union_proc ***)

lemma in_failures_Union_proc:
   "f :f {f. EX a:X. f :f Ff a}f = (EX a:X. f :f Ff a)"
by (simp add: CollectF_open_memF Rep_int_choice_setF)

lemma in_failures_UNIV_Union_proc:
   "f :f {f. EX a. f :f Ff a}f = (EX a. f :f Ff a)"
apply (insert in_failures_Union_proc[of f UNIV Ff])
by (simp)

(*** Rep_int_choice ***)

lemma in_failures_Rep_int_choice_sum: 
  "(f :f failures(!! :C .. Pf) M) = (EX c: sumset C. f :f failures(Pf c) M)"
apply (simp add: failures_iff)
by (simp add: in_failures_Union_proc)

lemma in_failures_Rep_int_choice_nat: 
  "(f :f failures(!nat :N .. Pf) M) = (EX n:N. f :f failures(Pf n) M)"
by (simp add: Rep_int_choice_ss_def in_failures_Rep_int_choice_sum)

lemma in_failures_Rep_int_choice_set: 
  "(f :f failures(!set :Xs .. Pf) M) = (EX X:Xs. f :f failures(Pf X) M)"
by (simp add: Rep_int_choice_ss_def in_failures_Rep_int_choice_sum)

lemma in_failures_Rep_int_choice_com: 
  "(f :f failures(! :X .. Pf) M) = (EX a:X. f :f failures(Pf a) M)"
apply (simp add: failures_iff)
by (simp add: in_failures_Union_proc)

lemma in_failures_Rep_int_choice_f: 
  "inj g ==>
   (f :f failures(!<g> :X .. Pf) M) = (EX a:X. f :f failures(Pf a) M)"
apply (simp add: failures_iff)
by (simp add: in_failures_Union_proc)

lemmas in_failures_Rep_int_choice =
       in_failures_Rep_int_choice_sum
       in_failures_Rep_int_choice_nat
       in_failures_Rep_int_choice_set
       in_failures_Rep_int_choice_com
       in_failures_Rep_int_choice_f

(*--------------------------------*
 |               IF               |
 *--------------------------------*)

(*** IF ***)

lemma in_failures_IF: 
  "(f :f failures(IF b THEN P ELSE Q) M)
 = (if b then f :f failures(P) M else f :f failures(Q) M)"
by (simp add: failures_iff)

(*--------------------------------*
 |           Parallel             |
 *--------------------------------*)

(*** Parallel_setF ***)

lemma Parallel_setF : 
  "{(u, Y Un Z) |u Y Z.
     Y - insert Tick (Ev ` X) = Z - insert Tick (Ev ` X) &
     (EX s t. u : s |[X]|tr t & (s, Y) :f F & (t, Z) :f E)}
    : setF"
apply (simp add: setF_def HC_F2_def)
apply (intro allI impI)
apply (elim conjE exE, simp)
apply (rename_tac u Y Z Y1 Y2 s t)
apply (rule_tac x="Z Int (Y1 - (Y2 - insert Tick (Ev ` X))) Un
                   Z Int (Y2 - insert Tick (Ev ` X))" in exI)
apply (rule_tac x="Z Int (Y2 - (Y2 - insert Tick (Ev ` X))) Un
                   Z Int (Y2 - insert Tick (Ev ` X))" in exI)

(* (s,Y), Z <= Y, Y = Y1 Un Y2, Z = Z1 Un Z2 *)

apply (rule conjI, force)
apply (rule conjI, force)

apply (rule_tac x="s" in exI)
apply (rule_tac x="t" in exI)
apply (simp)
apply (rule conjI)
apply (rule memF_F2, simp, force)+
done

lemma in_failures_Parallel:
  "(f :f failures(P |[X]| Q) M) = 
   (EX u Y Z. f = (u, Y Un Z) & Y - insert Tick (Ev ` X) = Z - insert Tick (Ev ` X) &
      (EX s t. u : s |[X]|tr t & (s,Y) :f failures(P) M & (t,Z) :f failures(Q) M))"
apply (simp add: failures_iff)
by (simp only: CollectF_open_memF Parallel_setF)

(*--------------------------------*
 |            Hiding              |
 *--------------------------------*)

(*** Hiding_setF ***)

lemma Hiding_setF : 
  "{f. EX s Y. f = (s --tr X, Y) & (s,(Ev`X) Un Y) :f F} : setF"
apply (simp add: setF_def HC_F2_def)
apply (intro allI impI)
apply (elim conjE exE, simp)
apply (rename_tac t Y Z s)
apply (rule_tac x="s" in exI)
apply (simp)
by (rule memF_F2, simp, force)

lemma in_failures_Hiding:
  "(f :f failures(P -- X) M) = 
   (EX s Y. f = (s --tr X, Y) & (s,(Ev`X) Un Y) :f failures(P) M)"
apply (simp add: failures_iff)
by (simp only: CollectF_open_memF Hiding_setF)

(*--------------------------------*
 |           Renaming             |
 *--------------------------------*)

(*** Renaming_setF ***)

lemma Renaming_setF : 
  "{f. EX s t X. f = (t,X) & (s [[r]]* t) & 
                 (s, [[r]]inv X) :f F } : setF"
apply (simp add: setF_def HC_F2_def)
apply (intro allI impI)
apply (elim conjE exE)
apply (rule_tac x="sa" in exI)
apply (simp)
apply (rule memF_F2, simp)
apply (rule ren_inv_sub, simp)
done

lemma in_failures_Renaming:
  "(f :f failures(P[[r]]) M) =
   (EX s t X. f = (t,X) & s [[r]]* t & (s, [[r]]inv X) :f failures(P) M)"
apply (simp add: failures_iff)
by (simp only: CollectF_open_memF Renaming_setF)

(*--------------------------------*
 |           Seq_compo            |
 *--------------------------------*)

(*** Seq_compo_setF ***)

lemma Seq_compo_setF : 
  "{f. (EX t X. f = (t, X) & (t, insert Tick X) :f F & noTick t) |
        (EX s t X.
            f = (s ^^^ t, X) & s ^^^ <Tick> :t T & (t, X) :f E & noTick s)}
    : setF"
apply (simp add: setF_def HC_F2_def)
 apply (intro allI impI)
 apply (elim conjE exE disjE)

  (* case 1 *)
  apply (rule disjI1, simp)
  apply (rule memF_F2, simp, force)

  (* case 2 *)
  apply (rule disjI2)
  apply (rule_tac x="sa" in exI)
  apply (rule_tac x="t" in exI)
  apply (simp)
  apply (rule memF_F2, simp, simp)
done

lemma in_failures_Seq_compo:
  "(f :f failures(P ;; Q) M) =
   ((EX t X.   f = (t,X) & (t, X Un {Tick}) :f failures(P) M & noTick t) |
    (EX s t X. f = (s ^^^ t,X) & s ^^^ <Tick> :t traces(P) (fstF o M)
               & (t, X) :f failures(Q) M & noTick s))"
apply (simp add: failures_iff)
by (simp only: CollectF_open_memF Seq_compo_setF)

(*--------------------------------*
 |          Depth_rest            |
 *--------------------------------*)

(*** Depth_rest ***)

lemma in_failures_Depth_rest:
  "(f :f failures(P |. n) M) =
   (EX t X. f = (t,X) & (t, X) :f  failures(P) M &
                (lengtht t < n |
                 lengtht t = n & (EX s. t = s ^^^ <Tick> & noTick s)))"
apply (simp add: failures_iff)
apply (subgoal_tac "EX t X. f = (t, X)")
apply (elim exE)
apply (simp add: in_rest_setF)
apply (auto)
done

(*--------------------------------*
 |          Proc_name             |
 *--------------------------------*)

(*** Proc_name ***)

lemma in_failures_Proc_name:
  "(f :f failures($p) M) = (f :f  sndF(M p))"
apply (simp add: failures_iff)
done

(*--------------------------------*
 |             alias              |
 *--------------------------------*)

lemmas failures_setF = STOP_setF       SKIP_setF
                       Act_prefix_setF Ext_pre_choice_setF
                       Ext_choice_setF Rep_int_choice_setF
                       Parallel_setF   Hiding_setF
                       Renaming_setF   Seq_compo_setF

lemmas in_failures = in_failures_STOP  in_failures_SKIP  in_failures_DIV
                     in_failures_Act_prefix     in_failures_Ext_pre_choice
                     in_failures_Ext_choice     in_failures_Int_choice
                     in_failures_Rep_int_choice in_failures_IF
                     in_failures_Parallel       in_failures_Hiding
                     in_failures_Renaming       in_failures_Seq_compo
                     in_failures_Union_proc     in_failures_UNIV_Union_proc
                     in_failures_Depth_rest     in_failures_Proc_name

(****************** to add them again ******************)

declare disj_not1   [simp]

end
