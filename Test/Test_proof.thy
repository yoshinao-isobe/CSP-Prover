           (*-------------------------------------------*
            |                   Test                    |
            |        CSP-Prover on Isabelle2005         |
            |                  April 2006               |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Test_proof
imports CSP_F_Main
begin

(*****************************************************************

   "(a -> P) |[{a}]| (a -> Q) =F a -> (P |[{a}]| Q)" is proven
   by the following three strategies:

         1. semantical proof
         2. algebraic proof
         3. tactic proof
         4. 

 *****************************************************************)

(*---------------------------------------------------------------*
    semantical proof by the difinition of traces and failures 
 *---------------------------------------------------------------*)

lemma semantical_proof: 
  "(a -> P) |[{a}]| (a -> Q) =F a -> (P |[{a}]| Q)"
apply (simp add: cspF_eqF_semantics)
apply (rule)

(* trace *)
apply (rule order_antisym)

 (* <= *)
 apply (rule)     (* subdomTI is automatically applied *)
 apply (simp add: in_traces)
 apply (auto simp add: par_tr_nil par_tr_head_Ev_Ev)

 (* => *)
 apply (auto simp add: in_traces)
 apply (simp add: par_tr_head)
 apply (rule_tac x="<Ev a> ^^^ sa" in exI)
 apply (rule_tac x="<Ev a> ^^^ ta" in exI)
 apply (auto)

(* failures *)
apply (rule order_antisym)

 (* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim conjE exE disjE)
 apply (simp_all add: par_tr_nil par_tr_head_Ev_Ev)
 apply (force)

 (* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim conjE exE disjE)
 apply (simp_all)
 apply (rule_tac x="X - {(Ev a)}" in exI)
 apply (rule_tac x="X - {(Ev a)}" in exI)
 apply (simp)
 apply (rule_tac x="Y" in exI)
 apply (rule_tac x="Z" in exI)
 apply (simp)
 apply (simp add: par_tr_head)
 apply (rule_tac x="<Ev a> ^^^ sb" in exI)
 apply (rule_tac x="<Ev a> ^^^ t" in exI)
 apply (auto)
done

(*---------------------------------------------------------------*
          manual syntactical proof by algebraic CSP laws
 *---------------------------------------------------------------*)

lemma syntactical_proof: 
  "(a -> P) |[{a}]| (a -> Q) =F a -> (P |[{a}]| Q)"
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_step)
apply (rule cspF_step)

apply (rule cspF_rw_left)
apply (rule cspF_step)

apply (rule cspF_rw_right)
apply (rule cspF_step)

apply (rule cspF_decompo)
apply (simp)
apply (simp)
done

(*---------------------------------------------------------------*
            semi-automatic syntactical proof by tactics
 *---------------------------------------------------------------*)

lemma tactical_proof: 
  "(a -> P) |[{a}]| (a -> Q) =F a -> (P |[{a}]| Q)"
apply (cspF_auto)+
apply (auto)
done

end
