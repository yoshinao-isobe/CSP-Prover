           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                  April 2005               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_op_alpha_par
imports CSP_T_traces
begin

(*********************************************************
       Preparation (traces operated by par and hide)
 *********************************************************)

(*** par rest ***)

(*** if ***)

lemma par_tr_rest_tr_if_all:
  "sett(u) <= insert Tick (Ev ` (X Un Y))
   --> u : u rest-tr X |[X Int Y]|tr u rest-tr Y"
apply (induct_tac u rule: induct_trace)
apply (simp_all)
apply (simp add: par_tr_head)
 apply (case_tac "a : X")
 apply (case_tac "a : Y")
 apply (auto)
done

lemma par_tr_rest_tr_if:
  "sett(u) <= insert Tick (Ev ` (X Un Y))
   ==> u : u rest-tr X |[X Int Y]|tr u rest-tr Y"
by (simp add: par_tr_rest_tr_if_all)

(*** only if ***)

lemma par_tr_rest_tr_only_if_all:
  "ALL s t. (sett s <= insert Tick (Ev ` X) & sett t <= insert Tick (Ev ` Y) & 
             u : s |[X Int Y]|tr t)
            --> (s = u rest-tr X & t = u rest-tr Y &
                 sett(u) <= insert Tick (Ev ` (X Un Y)))"
apply (induct_tac u rule: induct_trace)
apply (simp_all)

apply (intro allI impI)
apply (simp add: par_tr_head)
apply (elim conjE exE)

 (* sync *)
 apply (erule disjE)
 apply (elim conjE exE)
 apply (drule_tac x="s'" in spec)
 apply (drule_tac x="t'" in spec)
 apply (simp)

 (* left *)
 apply (erule disjE)
 apply (elim conjE exE)
 apply (drule_tac x="s'" in spec)
 apply (drule_tac x="t" in spec)
 apply (simp)
 apply (case_tac "a : X")
 apply (simp)
 apply (fast)

 (* right *)
 apply (elim conjE exE)
 apply (drule_tac x="sa" in spec)
 apply (drule_tac x="t'" in spec)
 apply (simp)
 apply (case_tac "a : Y")
 apply (simp)
 apply (fast)
done

(*** par rest ***)

lemma par_tr_rest_tr:
  "[| sett s <= insert Tick (Ev ` X) ; sett t <= insert Tick (Ev ` Y) |]
   ==> u : s |[X Int Y]|tr t 
    = (s = u rest-tr X & t = u rest-tr Y &
       sett(u) <= insert Tick (Ev ` (X Un Y)))"
apply (rule iffI)
apply (insert par_tr_rest_tr_only_if_all[of X Y u])
apply (drule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
apply (simp)

apply (simp add: par_tr_rest_tr_if)
done

(*********************************************************
             Alphabetized Parallel eval
 *********************************************************)

(*** Par and SKIP ***)

lemma in_traces_Parallel_SKIP:
  "(u :t traces (P |[X]| SKIP) M) = 
   (u :t traces P M & sett(u) Int (Ev ` X) = {})"
apply (simp add: in_traces)
apply (rule iffI)

(* => *)
 apply (elim conjE exE)
 apply (erule disjE)

 (* t = <> *)
  apply (simp add: par_tr_nil)
  apply (elim conjE, simp)

 (* t = [Tick]t *)
  apply (simp add: par_tr_Tick)
  apply (elim conjE, simp)

(* <= *)
 apply (case_tac "Tick ~: sett u")

 (* t = <> *)
  apply (rule_tac x="u" in exI)
  apply (rule_tac x="<>" in exI)
  apply (simp add: par_tr_nil)
  apply (erule conjE)
  apply (simp)

 (* t = <Tick> *)
  apply (rule_tac x="u" in exI)
  apply (rule_tac x="<Tick>" in exI)
  apply (simp add: par_tr_Tick)
done

(*** complement ***)

lemma in_traces_Parallel_SKIP_comp:
  "(u :t traces (P |[- X]| SKIP) M) = 
   (u :t traces P M & sett u <= insert Tick (Ev ` X))"
apply (simp add: in_traces_Parallel_SKIP)
apply (auto)
apply (insert event_Tick_or_Ev)
apply (drule_tac x="x" in spec)
apply (auto)
done

(*** Alpha_parallel_evalT ***)

lemma in_traces_Alpha_parallel:
  "(u :t traces (P |[X1,X2]| Q) M) = 
   ((u rest-tr X1) :t traces P M & (u rest-tr X2) :t traces Q M &
    sett(u) <= insert Tick (Ev ` (X1 Un X2)))"
apply (simp add: Alpha_parallel_def)
apply (simp add: in_traces_Parallel[of _ _ "X1 Int X2"])
apply (simp add: in_traces_Parallel_SKIP_comp)
apply (rule iffI)

(* => *)
 apply (elim conjE exE)
 apply (simp add: par_tr_rest_tr)

(* <= *)
 apply (rule_tac x="u rest-tr X1" in exI)
 apply (rule_tac x="u rest-tr X2" in exI)
 apply (simp add: par_tr_rest_tr_if)
done

(*** Semantics for alphabetized parallel on T ***)

lemma traces_Alpha_parallel:
  "traces (P |[X1,X2]| Q) M =
   {u. ((u rest-tr X1) :t traces P M & (u rest-tr X2) :t traces Q M &
        sett(u) <= insert Tick (Ev ` (X1 Un X2)))}t"
apply (simp add: in_traces_Alpha_parallel[THEN sym])
done

end
