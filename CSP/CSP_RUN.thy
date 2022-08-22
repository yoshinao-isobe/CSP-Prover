theory CSP_RUN
imports Trace_op
        CSP_syntax
begin


(*subsection \<open> Guardedness \<close>

lemma guarded_Runfun [simp]: "\<forall>p. guarded (Runfun p)"
  by (rule, case_tac p, simp)

lemma guardedfun_Runfun [simp]: "guardedfun Runfun"
  by (simp add: guardedfun_def)

declare Set_Runfun_def [simp]*)



(* ----------------------------------------------- *
       definitions and lemmas for RUN A

   RUN can be defined by basic CSP processes,
   but it is defined in more general style here.
 * ---------------------------------------------- *)

inductive_set
  set_run :: "'a set => 'a trace set" for A :: "'a set"

where
set_run_nil:
  "<> : set_run A" |

set_run_step:
  "[| s : set_run A ; a : A |]
   ==> <Ev a> ^^^ s : set_run A"


(* for renaming *)

definition
   ren_set :: "'a set => ('a * 'a) set => 'a set" 
where "ren_set == (%X r. {b. EX a. (a,b) : r & a : X})"

(* ----------------------------------------------- *
                  input-completeness
 * ---------------------------------------------- *)
(*
definition
   complete_on :: "'a set => ('p,'a) proc => bool"
where "complete_on == (%X P. traces_run X <= traces P MT)"
*)


(* ------------------------------ *
        lemmas on set_run
 * ------------------------------ *)

lemma set_run_one:
  "a : A ==> <Ev a> : set_run A"
apply (subgoal_tac " <Ev a> ^^^ <>: set_run A")
apply (simp)
apply (rule set_run.intros)
apply (rule set_run.intros)
apply (simp)
done

lemma set_run_sett:
  "s : set_run A ==> sett s <= (Ev ` A)"
apply (erule set_run.induct)
apply (simp)
apply (simp)
done

lemma noTick_set_run[rule_format]:
  "s : set_run A --> noTick s"
apply (induct_tac s rule: induct_trace)
apply (simp)
apply (intro impI)
apply (erule set_run.cases)
apply (simp)
apply (simp)
apply (intro impI)
apply (simp)
apply (erule set_run.cases)
apply (simp)
apply (simp)
done

lemma set_run_prefix:
  "ALL s t A. noTick s & s ^^^ t : set_run A --> s : set_run A"
apply (intro allI)
apply (induct_tac s rule: induct_trace)
apply (intro impI)
apply (rule set_run.intros)
apply (simp)
apply (intro impI)
apply (elim conjE)
apply (simp add: appt_assoc)
apply (erule set_run.cases)
apply (simp)
apply (rule set_run.intros)
apply (simp)
apply (simp)
done

lemma set_run_prefixE:
  "[| prefix s t; t : set_run A ; noTick t;
      s : set_run A ==> R |]
   ==> R"
apply (unfold prefix_def)
apply (elim conjE exE)

apply (insert set_run_prefix)
apply (drule_tac x="s" in spec)
apply (drule_tac x="u" in spec)
apply (drule_tac x="A" in spec)
apply (simp)
done

lemma set_run_postfix:
  "ALL s t A. noTick s & s ^^^ t : set_run A --> t : set_run A"
apply (intro allI)
apply (induct_tac s rule: induct_trace)
apply (intro impI)
apply (simp)
apply (simp)
apply (intro allI impI)
apply (elim conjE)
apply (simp add: appt_assoc)
apply (erule set_run.cases)
apply (simp)
apply (simp)
done

lemma set_run_last:
  "[| noTick s ; s ^^^ <e> : set_run A |] ==> e : Ev ` A"
apply (insert set_run_postfix)
apply (drule_tac x="s" in spec)
apply (drule_tac x="<e>" in spec)
apply (drule_tac x="A" in spec)
apply (simp)
apply (rotate_tac -1)
apply (erule set_run.cases)
apply (simp)
apply (auto simp add: image_iff)
done

lemma set_run_subset[rule_format]:
  "(A <= B & t : set_run A) --> t : set_run B"
apply (induct_tac t rule: induct_trace)
apply (simp add: set_run.intros)
apply (intro allI impI)
apply (elim conjE exE)
apply (insert noTick_set_run[of "<Tick>" A])
apply (simp)
apply (intro allI impI)
apply (elim conjE exE)
apply (erule set_run.cases)
apply (auto intro: set_run.intros)
done

(* -- ren -- *)


lemma set_run_ren[rule_format]:
  "ALL s. (s [[r]]* t & s : set_run A) --> t : set_run (ren_set A r)"
apply (induct_tac t rule: induct_trace)
apply (simp add: set_run.intros)
apply (intro allI impI)
apply (simp add: ren_tr_def)
apply (elim conjE exE)
apply (subgoal_tac "noTick s")
apply (erule renx.cases)
apply (simp_all)
apply (simp add: noTick_set_run)

(* Ev *)
apply (intro allI impI)
apply (elim conjE exE)
apply (erule set_run.cases)
apply (simp)
apply (simp)

apply (drule mp)
 apply (elim conjE exE)
 apply (rule_tac x="sb" in exI)
 apply (simp)

apply (rule set_run.intros)
apply (simp)
apply (simp add: ren_set_def)
apply (rule_tac x="aa" in exI)
apply (simp)
done

(* -- hide -- *)

lemma set_run_hide:
  "t : set_run A --> t --tr X : set_run (A - X)"
apply (induct_tac t rule: induct_trace)
apply (simp add: set_run.intros)
apply (intro allI impI)
apply (erule set_run.cases)
apply (simp)
apply (simp)

apply (intro allI impI)
apply (erule set_run.cases)
apply (simp)
apply (simp)
apply (case_tac "a : X")
apply (simp)
apply (simp)
apply (simp add: set_run.intros)
done

lemma set_run_par[rule_format]:
  "ALL s t. (s : set_run A & t : set_run B & u : s |[X]|tr t) --> u : set_run (A Un B)"
apply (induct_tac u rule: induct_trace)

(* <> *)
apply (simp add: set_run.intros)

(* <Tick> *)
apply (simp)
apply (intro strip)
apply (elim conjE exE)
apply (subgoal_tac "noTick <Tick>")
apply (simp)
apply (rule noTick_set_run)
apply (simp)

(* Ev a *)
apply (intro strip)
apply (elim conjE exE)
apply (simp add: par_tr_head)

apply (elim disjE conjE exE)
apply (simp_all)

(* sync *)
 apply (drule mp)
 apply (rule_tac x="s'" in exI)
 apply (erule set_run.cases)
 apply (simp)
 apply (simp)
 apply (rule_tac x="t'" in exI)
 apply (erule set_run.cases)
 apply (simp)
 apply (simp)
 apply (rule set_run.intros)
 apply (simp)
 apply (simp)
 apply (erule set_run.cases)
 apply (simp)
 apply (simp)

(* left *)
 apply (drule mp)
 apply (rule_tac x="s'" in exI)
 apply (erule set_run.cases)
 apply (simp)
 apply (simp)
 apply (rule_tac x="t" in exI)
 apply (simp)
 apply (rule set_run.intros)
 apply (simp)
 apply (simp)
 apply (erule set_run.cases)
 apply (simp)
 apply (simp)

(* right *)
 apply (drule mp)
 apply (rule_tac x="sa" in exI)
 apply (simp)
 apply (rule_tac x="t'" in exI)
 apply (rotate_tac 1)
 apply (erule set_run.cases)
 apply (simp)
 apply (simp)
 apply (rotate_tac 1)
 apply (rule set_run.intros)
 apply (simp)
 apply (simp)
 apply (erule set_run.cases)
 apply (simp)
 apply (simp)
done


lemma set_run_app[rule_format]:
   "(s : set_run A & t : set_run A) --> s ^^^ t : set_run A"
apply (induct_tac s rule: induct_trace)

(* <> *)
apply (simp)

(* <Tick> *)
apply (intro strip)
apply (elim conjE exE)
apply (subgoal_tac "noTick <Tick>")
apply (simp)
apply (rule noTick_set_run)
apply (simp)

(* Ev a *)
apply (intro strip)
apply (elim conjE exE)
apply (erule set_run.cases)
apply (simp)
apply (simp)
apply (subgoal_tac "noTick sa")
apply (simp add: appt_assoc)
apply (rule set_run.intros)
apply (simp)
apply (simp)
apply (simp add: noTick_set_run)
done

(* ||| *)

lemma interleave_set_run_only_if[rule_format]:
  "u : set_run (X Un Y) 
   --> (EX s t. u : s |[{}]|tr t & s : set_run X & t : set_run Y)"
apply (induct_tac u rule: induct_trace)
apply (simp add: set_run.intros)

apply (simp)
apply (intro allI impI)
apply (erule set_run.cases)
apply (simp)
apply (simp)

(* Ev a *)
apply (intro allI impI)
apply (erule set_run.cases)
apply (simp)
apply (simp)
apply (elim disjE conjE exE)

 apply (rule_tac x="<Ev a> ^^^ sb" in exI)
 apply (rule_tac x="t" in exI)
 apply (simp)
 apply (simp add: par_tr_head)
 apply (simp add: set_run.intros)

 apply (rule_tac x="sb" in exI)
 apply (rule_tac x="<Ev a> ^^^ t" in exI)
 apply (simp)
 apply (simp add: par_tr_head)
 apply (simp add: set_run.intros)
done

lemma interleave_set_run_if[rule_format]:
  "ALL s t. (u : s |[{}]|tr t & s : set_run X & t : set_run Y)
   --> u : set_run (X Un Y)"
apply (induct_tac u rule: induct_trace)
apply (simp add: set_run.intros)

apply (simp)

apply (intro allI impI)
apply (elim conjE exE)
apply (erule set_run.cases)
apply (simp)
apply (simp)

apply (intro allI impI)
apply (elim conjE exE)
apply (simp add: par_tr_head)
apply (elim disjE conjE exE)

 apply (simp)
 apply (drule mp)
  apply (rule_tac x="s'" in exI)
  apply (rule_tac x="t" in exI)
  apply (simp)
  apply (erule set_run.cases)
  apply (simp)
  apply (simp)
 apply (rule set_run.intros)
 apply (simp)
 apply (simp)
 apply (erule set_run.cases)
 apply (simp)
 apply (simp)

 apply (simp)
 apply (drule mp)
  apply (rule_tac x="sa" in exI)
  apply (rule_tac x="t'" in exI)
  apply (simp)
  apply (rotate_tac 1)
  apply (erule set_run.cases)
  apply (simp)
  apply (simp)
 apply (rule set_run.intros)
 apply (simp)
 apply (simp)
 apply (rotate_tac 1)
 apply (erule set_run.cases)
 apply (simp)
 apply (simp)
done



lemma Tick_notin_set_run [simp]:
    "<Tick> \<notin> set_run A"
  apply (auto)
  by (erule set_run.cases, simp_all)


end