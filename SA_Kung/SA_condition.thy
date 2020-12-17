           (*-------------------------------------------*
            |    Example 1 [Roscoe_Dathi_1987 P.10]     |
            |             WITH computation              |
            |  Self-timed version of a systolic array   |
            |                   June 2005               |
            |               December 2005  (modified)   |
            |                                           |
            |   on DFP on CSP-Prover ver.3.0            |
            |              September 2006  (modified)   |
            |                                           |
            |   on DFP on CSP-Prover ver.4.0            |
            |                  April 2007  (modified)   |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory SA_condition
imports SA_definition
begin

(*********************************************************
     Small conditions for Deadlock freedom verification
 *********************************************************)

(* finite set *)
(*
lemma Example1_finite_lm1: "finite ({i. i < (n::nat)} <*> {m})"
apply (induct_tac n)
apply (simp)
apply (subgoal_tac 
  "{i. i < Suc n} <*> {m} = ({i. i < n} <*> {m}) Un {(n,m)}")
by (auto)

lemma Example1_finite_lm2: "finite ({m} <*> {i. i < (n::nat)})"
apply (induct_tac n)
apply (simp)
apply (subgoal_tac 
  "{m} <*> {i. i < Suc n} = ({m} <*> {i. i < n}) Un {(m,n)}")
by (auto)
*)

lemma Example1_finite: "finite (Array_Index N)"
apply (simp add: Array_Index_def)
(*
apply (induct_tac N)
apply (simp)
apply (subgoal_tac 
  "{i. i < Suc n} <*> {j. j < Suc n} =
   ({i. i < n} <*> {j. j < n}) Un
   ({i. i < Suc n} <*> {n}) Un
   ({n} <*> {j. j < Suc n})")
apply (simp)
apply (rule conjI)
apply (simp add: Example1_finite_lm1)
apply (simp add: Example1_finite_lm2)
apply (auto)
*)
done

(* Example1_triple_disjoint *)

lemma Example1_triple_disjoint: "triple_disjoint (Systolic_ArrayF N)"
apply (simp add: triple_disjoint_def)
apply (simp add: Systolic_ArrayF_def)
apply (simp add: Array_Index_def)
apply (simp add: Alpha_pe.simps)
by (auto)

(* Example1_BusyNetwork *)

lemma Example1_BusyNetwork_out_lm:
   "[| ALL (s::('r::ring) Event trace) Y.
             (s, Y) : peF_rec n (i, j) --> Y ~= Ev ` Alpha_pe (i, j);
          ((s::('r::ring) Event trace), Y) : Faiures_out x y (i, j) (peF_rec n (i, j)) |]
       ==> Y ~= Ev ` Alpha_pe (i, j)"
apply (simp add: Faiures_out_def)
apply (elim disjE conjE exE)
apply (simp add: Alpha_pe.simps)
apply (rule neq_Set_EX2)
apply (rule_tac x="Ev (hori (i, Suc j) y)" in bexI)
apply (simp)
apply (simp)

apply (simp add: Faiures_out_hori_def)
apply (elim disjE conjE exE)
apply (simp add: Alpha_pe.simps)
apply (rule neq_Set_EX2)
apply (rule_tac x="Ev (hori (i, Suc j) y)" in bexI)
apply (simp)
apply (simp)
apply (simp)

apply (simp add: Faiures_out_vert_def)
apply (elim disjE conjE exE)
apply (simp add: Alpha_pe.simps)
apply (rule neq_Set_EX2)
apply (rule_tac x="Ev (vert (Suc i, j) x)" in bexI)
apply (simp)
apply (simp)
apply (simp)
done

lemma Example1_BusyNetwork_lm:
  "ALL s Y. (s, Y) : peF_rec n (i, j) --> Y ~= Ev ` Alpha_pe (i, j)"
apply (induct_tac n)
apply (simp)
apply (simp)
apply (intro allI impI)

apply (simp add: Faiures_in_def)
apply (elim disjE conjE exE)
apply (simp add: Alpha_pe.simps)
apply (rule neq_Set_EX2)
apply (force)

apply (simp add: Faiures_in_hori_def)
apply (elim disjE conjE exE)
apply (simp add: Alpha_pe.simps)
apply (rule neq_Set_EX2)
apply (force)
apply (simp)
apply (rule Example1_BusyNetwork_out_lm)
apply (simp_all)

apply (simp add: Faiures_in_vert_def)
apply (elim disjE conjE exE)
apply (simp add: Alpha_pe.simps)
apply (rule neq_Set_EX2)
apply (force)
apply (rule Example1_BusyNetwork_out_lm)
apply (simp_all)
done

lemma Example1_BusyNetwork: "BusyNetwork (Systolic_ArrayF N)"
apply (simp add: BusyNetwork_def)
apply (simp add: Systolic_ArrayF_def)
apply (simp add: peF_def)
apply (simp add: isDeadlockStateOf_def)
apply (rule ballI)
apply (simp add: Example1_index_mem)
apply (elim conjE exE)
apply (rename_tac ij i j)
apply (simp)
apply (intro allI impI)
apply (simp add: isStateOf_def)
apply (elim conjE exE)
apply (simp add: ALP_def)
apply (simp add: Example1_BusyNetwork_lm)
done

end
