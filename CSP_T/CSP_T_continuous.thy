           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005  (modified)   |
            |                 August 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_continuous
imports CSP_T_traces Domain_T_cpo CSP.CPO_prod
begin

(*****************************************************************

         1. continuous traces
         2. continuous [[ ]]Tfun

 *****************************************************************)

(*--------------------------------*
 |        STOP,SKIP,DIV           |
 *--------------------------------*)

(*** Constant_continuous ***)

lemma continuous_Constant: "continuous (%p. C)"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (insert complete_cpo_lm)
apply (drule_tac x="X" in spec, simp)
apply (simp add: hasLUB_def)
apply (elim exE)
apply (simp add: image_def isLUB_def isUB_def)
apply (intro allI impI)
apply (elim conjE exE)
apply (drule mp)
apply (simp add: directed_def)
apply (auto)
done

lemma continuous_traces_STOP: "continuous (traces (STOP))"
by (simp add: traces_iff continuous_Constant)

lemma continuous_traces_SKIP: "continuous (traces (SKIP))"
by (simp add: traces_iff continuous_Constant)

lemma continuous_traces_DIV: "continuous (traces (DIV))"
by (simp add: traces_iff continuous_Constant)

(*--------------------------------*
 |          Act_prefix            |
 *--------------------------------*)

lemma continuous_traces_Act_prefix:
 "continuous (traces P) ==> continuous (traces (a -> P))"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="X" in spec, simp)
apply (elim conjE exE)
apply (rule_tac x="x" in exI, simp)

apply (subgoal_tac "X ~= {}")
apply (simp add: isLUB_UnionT)
apply (rule order_antisym)

(* <= *)
apply (rule)
apply (simp add: in_traces)
apply (erule disjE, fast)
apply (elim conjE exE)
apply (simp)

(* => *)
apply (rule)
apply (simp)
apply (erule bexE)
apply (simp add: in_traces)
apply (erule disjE, simp)
apply (elim conjE exE)
apply (rule disjI2)
apply (rule_tac x="s" in exI, simp)
apply (rule_tac x="xa" in bexI)
apply (simp_all)

by (simp add: directed_def)

(*--------------------------------*
 |        Ext_pre_choice          |
 *--------------------------------*)

lemma continuous_traces_Ext_pre_choice:
 "ALL a. continuous (traces (Pf a))
  ==> continuous (traces (? a:X -> (Pf a)))"
apply (simp add: continuous_iff)
apply (intro allI impI)

apply (subgoal_tac "Xa ~= {}")
apply (erule exchange_forall_orderE)
apply (drule_tac x="Xa" in spec)
apply (simp add: isLUB_UnionT)

apply (rule_tac x="LUB Xa" in exI)
apply (rule conjI)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (erule disjE, fast)
 apply (elim conjE exE)
 apply (simp)
 apply (drule_tac x="a" in spec)
 apply (elim conjE exE)
 apply (subgoal_tac "LUB Xa = x", simp)
 apply (simp add: isLUB_LUB)

(* => *)
 apply (rule)
 apply (simp)
 apply (erule bexE)
 apply (simp add: in_traces)
 apply (erule disjE, simp)
 apply (elim conjE exE)
 apply (rule disjI2)
 apply (rule_tac x="a" in exI)
 apply (rule_tac x="s" in exI, simp)

 apply (drule_tac x="a" in spec)
 apply (elim conjE exE)
 apply (subgoal_tac "LUB Xa = xa", simp)
 apply (rule_tac x="x" in bexI)
 apply (simp)
 apply (simp)
 apply (simp add: isLUB_LUB)

 apply (drule_tac x="a" in spec)
 apply (elim conjE exE)
 apply (simp add: isLUB_LUB)

by (simp add: directed_def)

(*--------------------------------*
 |          Ext_choice            |
 *--------------------------------*)

lemma continuous_traces_Ext_choice:
 "[| continuous (traces P) ; continuous (traces Q) |]
  ==> continuous (traces (P [+] Q))"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="X" in spec, simp)
apply (drule_tac x="X" in spec, simp)
apply (elim conjE exE)

apply (subgoal_tac "xa = x")
apply (rule_tac x="x" in exI, simp)

apply (subgoal_tac "X ~= {}")
apply (simp add: isLUB_UnionT)
apply (rule order_antisym)
 apply (rule, simp add: in_traces, fast)
 apply (rule, simp add: in_traces, fast)
apply (simp add: directed_def)
by (rule LUB_unique, simp_all)

(*--------------------------------*
 |          Int_choice            |
 *--------------------------------*)

lemma continuous_traces_Int_choice:
 "[| continuous (traces P) ; continuous (traces Q) |]
  ==> continuous (traces (P |~| Q))"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="X" in spec, simp)
apply (drule_tac x="X" in spec, simp)
apply (elim conjE exE)

apply (subgoal_tac "xa = x")
apply (rule_tac x="x" in exI, simp)

apply (subgoal_tac "X ~= {}")
apply (simp add: isLUB_UnionT)
apply (rule order_antisym)
 apply (rule, simp add: in_traces, fast)
 apply (rule, simp add: in_traces, fast)
apply (simp add: directed_def)
by (rule LUB_unique, simp_all)

(*--------------------------------*
 |        Rep_int_choice          |
 *--------------------------------*)

lemma continuous_traces_Rep_int_choice:
 "ALL c. continuous (traces(Pf c))
  ==> continuous (traces (!! :C .. Pf))"
apply (simp add: continuous_iff)
apply (intro allI impI)

apply (subgoal_tac "X ~= {}")
apply (erule exchange_forall_orderE)
apply (drule_tac x="X" in spec)
apply (simp add: isLUB_UnionT)

apply (rule_tac x="LUB X" in exI)
apply (rule conjI)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (erule disjE, fast)
 apply (elim conjE bexE)
 apply (drule_tac x="c" in spec)
 apply (elim conjE exE)
 apply (subgoal_tac "LUB X = x", simp)
 apply (elim bexE)
 apply (rule_tac x="xa" in bexI)
 apply (fast)
 apply (simp)
 apply (simp add: isLUB_LUB)

(* => *)
 apply (rule)
 apply (simp)
 apply (erule bexE)
 apply (simp add: in_traces)
 apply (erule disjE, simp)
 apply (elim conjE bexE)
 apply (rule disjI2)
 apply (rule_tac x="c" in bexI)

 apply (drule_tac x="c" in spec)
 apply (elim conjE exE)
 apply (subgoal_tac "LUB X = xa", simp)
 apply (rule_tac x="x" in bexI)
 apply (simp)
 apply (simp)
 apply (simp add: isLUB_LUB)
 apply (simp)

 apply (drule_tac x="c" in spec)
 apply (elim conjE exE)
 apply (simp add: isLUB_LUB)

by (simp add: directed_def)

(*--------------------------------*
 |                IF              |
 *--------------------------------*)

lemma continuous_traces_IF:
 "[| continuous (traces P) ; continuous (traces Q) |]
  ==> continuous (traces (IF b THEN P ELSE Q))"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="X" in spec, simp)
apply (drule_tac x="X" in spec, simp)
apply (elim conjE exE)
apply (case_tac "b")
 apply (rule_tac x="x" in exI, simp)
 apply (simp add: traces_iff)
 apply (rule_tac x="xa" in exI, simp)
 apply (simp add: traces_iff)
done

(*--------------------------------*
 |           Parallel             |
 *--------------------------------*)

lemma continuous_traces_Parallel:
 "[| continuous (traces P) ; continuous (traces Q) |]
  ==> continuous (traces (P |[X]| Q))"
apply (subgoal_tac "mono (traces P) & mono (traces Q)")

apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="Xa" in spec, simp)
apply (drule_tac x="Xa" in spec, simp)
apply (elim conjE exE)

apply (subgoal_tac "xa = x")
apply (rule_tac x="x" in exI, simp)

apply (subgoal_tac "Xa ~= {}")
apply (simp add: isLUB_UnionT)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim exE bexE conjE)

 apply (simp add: directed_def)
 apply (drule_tac x="xb" in spec)
 apply (drule_tac x="xc" in spec)
 apply (simp, elim conjE exE)
 apply (rule_tac x="z" in bexI)
 apply (rule_tac x="s" in exI)
 apply (rule_tac x="ta" in exI)
 apply (simp)
 apply (rule conjI)
 apply (rule memT_subdomT, simp)
 apply (simp add: mono_def)
 apply (rotate_tac -4)
 apply (rule memT_subdomT, simp)
 apply (simp add: mono_def)
 apply (simp)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (fast)

apply (simp add: directed_def)
apply (simp add: LUB_unique)

by (simp add: continuous_mono)

(*--------------------------------*
 |            Hiding              |
 *--------------------------------*)

lemma continuous_traces_Hiding:
 "continuous (traces P)
  ==> continuous (traces (P -- X))"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="Xa" in spec, simp)
apply (elim conjE exE)

apply (rule_tac x="x" in exI, simp)
apply (subgoal_tac "Xa ~= {}")
apply (simp add: isLUB_UnionT)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (fast)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (fast)

by (simp add: directed_def)

(*--------------------------------*
 |           Renaming             |
 *--------------------------------*)

lemma continuous_traces_Renaming:
 "continuous (traces P)
  ==> continuous (traces (P [[r]]))"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="X" in spec, simp)
apply (elim conjE exE)

apply (rule_tac x="x" in exI, simp)
apply (subgoal_tac "X ~= {}")
apply (simp add: isLUB_UnionT)
apply (rule order_antisym)
 apply (rule, simp add: in_traces, fast)
 apply (rule, simp add: in_traces, fast)
by (simp add: directed_def)

(*--------------------------------*
 |           Seq_compo            |
 *--------------------------------*)

lemma continuous_traces_Seq_compo:
 "[| continuous (traces P) ; continuous (traces Q) |]
  ==> continuous (traces (P ;; Q))"
apply (subgoal_tac "mono (traces P) & mono (traces Q)")
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="X" in spec, simp)
apply (drule_tac x="X" in spec, simp)
apply (elim conjE exE)

apply (subgoal_tac "xa = x")
apply (rule_tac x="x" in exI, simp)

apply (subgoal_tac "X ~= {}")
apply (simp add: isLUB_UnionT)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim bexE exE conjE disjE)
 apply (rule_tac x="xb" in bexI)
 apply (fast)
 apply (simp)

 apply (simp add: directed_def)
 apply (drule_tac x="xb" in spec)
 apply (drule_tac x="xc" in spec)
 apply (simp, elim conjE exE)
 apply (rule_tac x="z" in bexI)
 apply (rule disjI2)
 apply (rule_tac x="s" in exI)
 apply (rule_tac x="ta" in exI)
 apply (simp)
 apply (rule conjI)
 apply (rule memT_subdomT, simp)
 apply (simp add: mono_def)
 apply (rotate_tac -4)
 apply (rule memT_subdomT, simp)
 apply (simp add: mono_def)
 apply (simp)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (fast)

apply (simp add: directed_def)
apply (simp add: LUB_unique)

by (simp add: continuous_mono)

(*--------------------------------*
 |          Depth_rest            |
 *--------------------------------*)

lemma continuous_traces_Depth_rest:
 "continuous (traces P)
  ==> continuous (traces (P |. n))"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="X" in spec, simp)
apply (elim conjE exE)

apply (rule_tac x="x" in exI, simp)
apply (subgoal_tac "X ~= {}")
apply (simp add: isLUB_UnionT)
apply (rule order_antisym)
 apply (rule, simp add: in_traces)
 apply (rule, simp add: in_traces)
by (simp add: directed_def)

(*--------------------------------*
 |            variable            |
 *--------------------------------*)

lemma continuous_traces_variable: 
   "continuous (traces ($p))"
apply (simp add: traces_iff)
apply (simp add: continuous_prod_variable)
done

(*--------------------------------*
 |            Procfun             |
 *--------------------------------*)

lemma continuous_traces: 
  "continuous (traces P)"
apply (induct_tac P)
apply (simp add: continuous_traces_STOP)
apply (simp add: continuous_traces_SKIP)
apply (simp add: continuous_traces_DIV)
apply (simp add: continuous_traces_Act_prefix)
apply (simp add: continuous_traces_Ext_pre_choice)
apply (simp add: continuous_traces_Ext_choice)
apply (simp add: continuous_traces_Int_choice)
apply (simp add: continuous_traces_Rep_int_choice)
apply (simp add: continuous_traces_IF)
apply (simp add: continuous_traces_Parallel)
apply (simp add: continuous_traces_Hiding)
apply (simp add: continuous_traces_Renaming)
apply (simp add: continuous_traces_Seq_compo)
apply (simp add: continuous_traces_Depth_rest)
apply (simp add: continuous_traces_variable)
done

(*=============================================================*
 |                          [[P]]Tf                            |
 *=============================================================*)

lemma continuous_semTf: 
  "continuous [[P]]Tf"
apply (simp add: semTf_def)
apply (simp add: continuous_traces)
done

(*=============================================================*
 |                         [[P]]Tfun                           |
 *=============================================================*)

lemma continuous_semTfun: "continuous [[Pf]]Tfun"
apply (simp add: prod_continuous)
apply (simp add: semTfun_def)
apply (simp add: proj_fun_def)
apply (simp add: comp_def)
apply (simp add: continuous_semTf)
done

end
