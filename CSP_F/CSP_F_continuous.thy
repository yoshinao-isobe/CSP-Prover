           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005 (modified)    |
            |              September 2005 (modified)    |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_continuous
imports CSP_F_domain Domain_F_cpo CSP_T.CSP_T_mono
begin

(*****************************************************************

         1. continuous failuresfun
         2. continuous failuresFun
         3. continuous [[ ]]Ffun
         4. continuous [[ ]]FFun

 *****************************************************************)

(*=============================================================*
 |                     traces fstF                             |
 *=============================================================*)

lemma continuous_traces_fstF:
   "continuous ((%M. traces P (fstF o M)))"
apply (subgoal_tac "(%M. traces P (fstF o M)) = (traces P) o ((o) fstF)")
apply (simp add: continuous_traces continuous_op_fstF compo_continuous)
apply (simp add: fun_eq_iff)
done

(*--------------------------------*
 |        STOP,SKIP,DIV           |
 *--------------------------------*)

lemma continuous_failures_STOP: "continuous (failures (STOP))"
by (simp add: failures_iff continuous_Constant)

lemma continuous_failures_SKIP: "continuous (failures (SKIP))"
by (simp add: failures_iff continuous_Constant)

lemma continuous_failures_DIV: "continuous (failures (DIV))"
by (simp add: failures_iff continuous_Constant)

(*--------------------------------*
 |          Act_prefix            |
 *--------------------------------*)

lemma continuous_failures_Act_prefix:
 "continuous (failures P) ==> continuous (failures (a -> P))"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="X" in spec, simp)
apply (elim conjE exE)
apply (rule_tac x="x" in exI, simp)

apply (subgoal_tac "X ~= {}")
apply (simp add: isLUB_UnionF)
apply (rule order_antisym)

(* <= *)
apply (rule)
apply (simp add: in_failures)
apply (erule disjE, fast)
apply (elim conjE exE)
apply (simp)

(* => *)
apply (rule)
apply (simp)
apply (erule bexE)
apply (simp add: in_failures)
apply (erule disjE, simp)
apply (elim conjE exE)
apply (rule disjI2)
apply (rule_tac x="sa" in exI, simp)
apply (rule_tac x="xa" in bexI)
apply (simp_all)

by (simp add: directed_def)

(*--------------------------------*
 |        Ext_pre_choice          |
 *--------------------------------*)

lemma continuous_failures_Ext_pre_choice:
 "ALL a. continuous (failures (Pf a))
     ==> continuous (failures (? a:X -> (Pf a)))"
apply (simp add: continuous_iff)
apply (intro allI impI)

apply (subgoal_tac "Xa ~= {}")
apply (erule exchange_forall_orderE)
apply (drule_tac x="Xa" in spec)
apply (simp add: isLUB_UnionF)

apply (rule_tac x="LUB Xa" in exI)
apply (rule conjI)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
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
 apply (simp add: in_failures)
 apply (erule disjE, simp)
 apply (elim conjE exE)
 apply (rule disjI2)
 apply (rule_tac x="a" in exI)
 apply (rule_tac x="sa" in exI, simp)

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

lemma continuous_failures_Ext_choice:
 "[| continuous (failures P) ; continuous (failures Q) |]
  ==> continuous (failures (P [+] Q))"
apply (subgoal_tac "mono (failures P) & mono (failures Q)")
apply (subgoal_tac "continuous (%M. traces P (fstF o M)) &
                    continuous (%M. traces Q (fstF o M))")
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (elim conjE)
apply (drule_tac x="X" in spec, simp)
apply (drule_tac x="X" in spec, simp)
apply (drule_tac x="X" in spec, simp)
apply (drule_tac x="X" in spec, simp)
apply (elim conjE exE)

apply (subgoal_tac "xa = x")
apply (subgoal_tac "xb = x")
apply (subgoal_tac "xc = x")
apply (rule_tac x="x" in exI, simp)

apply (subgoal_tac "X ~= {}")
apply (simp add: isLUB_UnionF)
apply (simp add: isLUB_UnionT)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim conjE bexE disjE)

 (* 1 *)
  apply (simp add: directed_def)
  apply (drule_tac x="xd" in spec)
  apply (drule_tac x="xe" in spec)
  apply (simp, elim conjE exE)
  apply (rule_tac x="z" in bexI)
  apply (rule disjI1)
  apply (rule conjI)
  apply (rule memF_subsetF, simp)
  apply (simp add: mono_def)
  apply (rotate_tac -4)
  apply (rule memF_subsetF, simp)
  apply (simp add: mono_def)

 (* 2-5 *)
  apply (fast)+

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (fast)

apply (simp add: directed_def)
apply (rule LUB_unique, simp_all)+

apply (simp add: continuous_traces_fstF)
apply (simp add: continuous_mono)
done

(*--------------------------------*
 |          Int_choice            |
 *--------------------------------*)

lemma continuous_failures_Int_choice:
 "[| continuous (failures P) ; continuous (failures Q) |]
  ==> continuous (failures (P |~| Q))"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="X" in spec, simp)
apply (drule_tac x="X" in spec, simp)
apply (elim conjE exE)

apply (subgoal_tac "xa = x")
apply (rule_tac x="x" in exI, simp)

apply (subgoal_tac "X ~= {}")
apply (simp add: isLUB_UnionF)
apply (rule order_antisym)
 apply (rule, simp add: in_failures, fast)
 apply (rule, simp add: in_failures, fast)
apply (simp add: directed_def)
by (rule LUB_unique, simp_all)

(*--------------------------------*
 |        Rep_int_choice          |
 *--------------------------------*)

lemma continuous_failures_Rep_int_choice:
 "ALL c. continuous (failures (Pf c))
  ==> continuous (failures (!! :C .. Pf))"
apply (simp add: continuous_iff)
apply (intro allI impI)

apply (subgoal_tac "X ~= {}")
apply (erule exchange_forall_orderE)
apply (drule_tac x="X" in spec)
apply (simp add: isLUB_UnionF)

apply (rule_tac x="LUB X" in exI)
apply (rule conjI)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
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
 apply (simp add: in_failures)
 apply (elim conjE bexE)
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
 |              IF                |
 *--------------------------------*)

lemma continuous_failures_IF:
 "[| continuous (failures P) ; continuous (failures Q) |]
  ==> continuous (failures (IF b THEN P ELSE Q))"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="X" in spec, simp)
apply (drule_tac x="X" in spec, simp)
apply (elim conjE exE)
apply (case_tac "b")
 apply (rule_tac x="x" in exI, simp)
 apply (simp add: failures_iff)

 apply (rule_tac x="xa" in exI, simp)
 apply (simp add: failures_iff)
done

(*--------------------------------*
 |           Parallel             |
 *--------------------------------*)

lemma continuous_failures_Parallel:
 "[| continuous (failures P) ; continuous (failures Q) |]
  ==> continuous (failures (P |[X]| Q))"
apply (subgoal_tac "mono (failures P) & mono (failures Q)")

apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="Xa" in spec, simp)
apply (drule_tac x="Xa" in spec, simp)
apply (elim conjE exE)

apply (subgoal_tac "xa = x")
apply (rule_tac x="x" in exI, simp)

apply (subgoal_tac "Xa ~= {}")
apply (simp add: isLUB_UnionF)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim exE bexE conjE)

 apply (simp add: directed_def)
 apply (drule_tac x="xb" in spec)
 apply (drule_tac x="xc" in spec)
 apply (simp, elim conjE exE)
 apply (rule_tac x="z" in bexI)
 apply (rule_tac x="Y" in exI)
 apply (rule_tac x="Z" in exI)
 apply (simp)
 apply (rule_tac x="sa" in exI)
 apply (rule_tac x="t" in exI)
 apply (simp)

 apply (rule conjI)
 apply (rule memF_subsetF, simp)
 apply (simp add: mono_def)
 apply (rotate_tac -4)
 apply (rule memF_subsetF, simp)
 apply (simp add: mono_def)
 apply (simp)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (fast)

apply (simp add: directed_def)
apply (simp add: LUB_unique)

by (simp add: continuous_mono)

(*--------------------------------*
 |            Hiding              |
 *--------------------------------*)

lemma continuous_failures_Hiding:
 "continuous (failures P)
  ==> continuous (failures (P -- X))"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="Xa" in spec, simp)
apply (elim conjE exE)

apply (rule_tac x="x" in exI, simp)
apply (subgoal_tac "Xa ~= {}")
apply (simp add: isLUB_UnionF)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (fast)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (fast)

by (simp add: directed_def)

(*--------------------------------*
 |           Renaming             |
 *--------------------------------*)

lemma continuous_failures_Renaming:
 "continuous (failures P)
  ==> continuous (failures (P [[r]]))"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="X" in spec, simp)
apply (elim conjE exE)

apply (rule_tac x="x" in exI, simp)
apply (subgoal_tac "X ~= {}")
apply (simp add: isLUB_UnionF)
apply (rule order_antisym)
 apply (rule, simp add: in_failures, fast)
 apply (rule, simp add: in_failures, fast)
by (simp add: directed_def)

(*--------------------------------*
 |           Seq_compo            |
 *--------------------------------*)

lemma continuous_failures_Seq_compo:
 "[| continuous (failures P) ; continuous (failures Q) |]
  ==> continuous (failures (P ;; Q))"
apply (subgoal_tac "mono (traces P) & mono (failures Q)")
apply (subgoal_tac "continuous (%M. traces P (fstF o M))")
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="X" in spec, simp)
apply (drule_tac x="X" in spec, simp)
apply (drule_tac x="X" in spec, simp)
apply (elim conjE exE)

apply (subgoal_tac "xa = x")
apply (subgoal_tac "xb = x")
apply (rule_tac x="x" in exI, simp)

apply (subgoal_tac "X ~= {}")
apply (simp add: isLUB_UnionF)
apply (simp add: isLUB_UnionT)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim bexE exE conjE disjE)

 (* 1 *)
  apply (fast)

 (* 2 *)
  apply (simp add: directed_def)
  apply (drule_tac x="xc" in spec)
  apply (drule_tac x="xd" in spec)
  apply (simp, elim conjE exE)
  apply (rule_tac x="z" in bexI)
  apply (rule disjI2)
  apply (rule_tac x="sa" in exI)
  apply (rule_tac x="t" in exI)
  apply (simp)

  apply (rule conjI)
  apply (rule memT_subdomT, simp)
  apply (simp add: mono_def)
  apply (subgoal_tac "fstF o xc <= fstF o z")
  apply (simp add: comp_def)

  apply (simp add: comp_def)
  apply (simp add: order_prod_def)
  apply (simp add: mono_fstF[simplified mono_def])

  apply (rotate_tac -4)
  apply (rule memF_subsetF, simp)
  apply (simp add: mono_def)
  apply (simp)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (fast)

apply (simp add: directed_def)
apply (simp add: LUB_unique)+
apply (simp add: continuous_traces_fstF)
apply (simp add: continuous_mono)
apply (simp add: mono_traces)
done

(*--------------------------------*
 |          Depth_rest            |
 *--------------------------------*)

lemma continuous_failures_Depth_rest:
 "continuous (failures P)
  ==> continuous (failures (P |. n))"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="X" in spec, simp)
apply (elim conjE exE)

apply (rule_tac x="x" in exI, simp)
apply (subgoal_tac "X ~= {}")
apply (simp add: isLUB_UnionF)
apply (rule order_antisym)
 apply (rule, simp add: in_failures)
 apply (rule, simp add: in_failures)
by (simp add: directed_def)

(*--------------------------------*
 |            variable            |
 *--------------------------------*)

lemma continuous_failures_variable_lm: "continuous (sndF o (%M. M p))"
apply (rule compo_continuous)
apply (simp add: continuous_prod_variable)
apply (simp add: sndF_def)
apply (rule compo_continuous)
apply (simp add: cont_Rep_domF)
apply (simp add: snd_continuous)
done

lemma continuous_failures_variable: 
   "continuous (failures ($p))"
apply (simp add: failures_iff)
apply (simp add: continuous_failures_variable_lm[simplified comp_def])
done

(** [[ ]]Ff **)

lemma continuous_semFf_variable: "continuous ([[$p]]Ff)"
apply (simp add: semFf_Proc_name)
apply (simp add: continuous_prod_variable)
done

(*--------------------------------*
 |             Proc               |
 *--------------------------------*)

lemma continuous_failures: "continuous (failures P)"
apply (induct_tac P)
apply (simp add: continuous_failures_STOP)
apply (simp add: continuous_failures_SKIP)
apply (simp add: continuous_failures_DIV)
apply (simp add: continuous_failures_Act_prefix)
apply (simp add: continuous_failures_Ext_pre_choice)
apply (simp add: continuous_failures_Ext_choice)
apply (simp add: continuous_failures_Int_choice)
apply (simp add: continuous_failures_Rep_int_choice)
apply (simp add: continuous_failures_IF)
apply (simp add: continuous_failures_Parallel)
apply (simp add: continuous_failures_Hiding)
apply (simp add: continuous_failures_Renaming)
apply (simp add: continuous_failures_Seq_compo)
apply (simp add: continuous_failures_Depth_rest)
apply (simp add: continuous_failures_variable)
done

(*=============================================================*
 |                          [[P]]Ff                            |
 *=============================================================*)

lemma continuous_semFf: 
  "continuous ([[Pf]]Ff)"
apply (simp add: semFf_def)
apply (simp add: continuous_domF_decompo)
apply (simp add: continuous_traces_fstF)
apply (simp add: continuous_failures)
done

(*=============================================================*
 |                         [[P]]Ffun                           |
 *=============================================================*)

lemma continuous_semFfun: 
  "continuous ([[PF]]Ffun)"
apply (simp add: semFfun_def)
apply (simp add: prod_continuous)
apply (simp add: proj_fun_def comp_def)
apply (simp add: continuous_semFf)
done

end
