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
            |                                           |
            |   on DFP on CSP-Prover ver.5.0            |
            |                   July 2009  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2012         |
            |               November 2012  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory SA_main
imports SA_condition SA_expanding SA_local
begin

(*=================================================================*
 |                 main theorem (deadlock freedom)                 |
 *=================================================================*)

theorem Example1_ring:
  "ALL N. N ~= 0 --> DeadlockFreeNetwork (Systolic_Array N)"
apply (intro allI impI)
apply (rule Rule1_Roscoe_Dathi_1987_I)
apply (simp_all)
apply (rule EX1_isFailureOf[simplified Systolic_ArrayF_def])

(* nonempty *)
apply (simp add: Array_Index_def)
apply (fast)

(* finite *)
apply (simp add: Example1_finite)

(* 3triple_disjoint*)
apply (simp add: Example1_triple_disjoint[simplified Systolic_ArrayF_def])

(* BusyNetwork *)
apply (simp add: Example1_BusyNetwork[simplified Systolic_ArrayF_def])

(* variant function *)
apply (rule_tac x="(%(i,j). (%(s,X). (lengtht s) + 2 * (i + j)))" in exI)
apply (simp)
apply (intro ballI impI allI)
apply (simp add: Example1_index_mem)
apply (elim conjE exE)
apply (rename_tac N ij1 ij2 t Yf i1 i2 j1 j2)
apply (simp)
apply (subgoal_tac "(i1 = i2 & j1 = Suc j2)
                  | (i1 = i2 & j2 = Suc j1)
                  | (i1 = Suc i2 & j1 = j2)
                  | (i2 = Suc i1 & j1 = j2)")
apply (elim conjE disjE)
apply (simp add: local_hori_rev)
apply (simp add: local_hori)
apply (simp add: local_vert_rev)
apply (simp add: local_vert)
apply (simp add: possible_pairs)
done

(****************** to add it again ******************)

end
