           (*-------------------------------------------*
            |         Interrupt on CSP-Prover 5         |
            |                                           |
            |                  August 2009              |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            | Joabe Jesus (POLI-UPE & CIn-UFPE  BRAZIL) |
            *-------------------------------------------*)

theory CSP_T_law_interrupt
imports CSP.CSP_RUN CSP_T.CSP_T_surj
begin

subsection \<open> definitions and lemmas for Interrupt /\ based on CSPIO \<close>

(*
definition
   IR :: "('p,'a) proc => ('p,'a) proc => ('p,'a) proc" ("(1_ /IR _)" [75,76] 75)
where "P IR Q == (Proc_T (IR_domT (traces P MT) (traces Q MT)))"

notation (xsymbols) IR ("(1_ /\<triangle> _)" [75,76] 75)
*)


definition
   IR_set :: "'a domT => 'a domT => 'a trace set"
where "IR_set == (%S T. 
        {u. u :t S | (EX s t. u=s^^^t & noTick s & s :t S & t :t T)})"

definition
   IR_domT :: "'a domT => 'a domT => 'a domT"
where "IR_domT == (%S T. Abs_domT (IR_set S T))"

(* ------------------------------ *
      lemmas on IR
 * ------------------------------ *)

lemma IR_set_in_domT:
  "IR_set S T : domT"
apply (simp add: domT_def HC_T1_def)
apply (rule conjI)

(* non empty *)
 apply (simp add: IR_set_def)
 apply (rule_tac x="<>" in exI)
 apply (simp)

(* prefix closed *)
 apply (simp add: IR_set_def)
 apply (simp add: prefix_closed_def)

 apply (intro strip)
 apply (elim disjE conjE exE)

  apply (rule disjI1)
  apply (rule memT_prefix_closed)
  apply (simp)
  apply (simp)

  apply (simp)
  apply (simp add: prefix_def)
  apply (elim disjE conjE exE)

  apply (simp add: appt_decompo)
  apply (elim disjE conjE exE)

   apply (rule disjI2)
   apply (rule_tac x="sa" in exI)
   apply (rule_tac x="ua" in exI)
   apply (simp)
   apply (rule memT_prefix_closed)
   apply (simp)
   apply (simp)

   apply (force)

   apply (rule disjI2)
   apply (rule_tac x="s" in exI)
   apply (rule_tac x="<>" in exI)
   apply (simp)
   apply (rule memT_prefix_closed)
   apply (simp)
   apply (simp)

   apply (rule disjI2)
   apply (rule_tac x="s" in exI)
   apply (rule_tac x="<>" in exI)
   apply (simp)
   apply (rule memT_prefix_closed)
   apply (simp)
   apply (simp)

  apply (force)
done


lemma in_traces_Interrupt:
  "(u :t traces(P />i Q) MT) = 
   (u :t traces P MT |
     (EX s t. u=s^^^t & noTick s & s :t traces P MT & t :t traces Q MT))"
apply (simp add: traces_iff)
apply (simp add: traces_Proc_T)
apply (simp add: IR_domT_def memT_def)
apply (simp add: Abs_domT_inverse IR_set_in_domT)
apply (fold memT_def)
apply (simp add: IR_set_def)
done

lemma alphas_Interrupt:
  "[| A : alphas P ; B : alphas Q |] ==> A Un B : alphas (P />i Q)"
apply (simp add: alphas_def)
apply (rule)
apply (simp add: in_traces_IR)
apply (elim disjE conjE exE)
apply (rule traces_run_subset[of A])
apply (simp)
apply (force)

apply (simp)
apply (rule traces_run_app)
apply (rule traces_run_subset[of A])
apply (simp)
apply (force)

apply (rule traces_run_subset[of B])
apply (simp)
apply (force)
done

lemma alphas_IR_sub:
  "[| A : alphas P ; B : alphas Q ; A Un B <= C|] ==> C : alphas (P IR Q)"
apply (insert alphas_IR[of A P B Q])
apply (rule alpha_subset)
apply (simp (no_asm_simp))
apply (simp)
done

lemma noTickPr_IR:
  "[| noTickPr P ; noTickPr Q |] ==> noTickPr (P IR Q)"
apply (simp add: noTickPr_def)
apply (intro strip)
apply (simp add: in_traces_IR)
apply (auto)
done


lemma cspT_decompo_IR:
  "[| P1 <=T Q1 ; P2 <=T Q2 |] ==> P1 IR P2 <=T Q1 IR Q2"
apply (simp add: cspT_semantics)
apply (rule subdomTI)
apply (simp add: subdomT_iff)
apply (simp add: in_traces_IR)
apply (auto)
done


end