           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005 (modified)    |
            |                 August 2005 (modified)    |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_mono
imports CSP_F_domain CSP_T.CSP_T_mono
begin

(*****************************************************************

         1. mono check of failuresfun
         2. 
         3. 
         4. 

 *****************************************************************)

(*--------------------------------*
 |        STOP,SKIP,DIV           |
 *--------------------------------*)

lemma mono_failures_STOP: "mono (failures (STOP))"
by (simp add: mono_def failures_iff)

lemma mono_failures_SKIP: "mono (failures (SKIP))"
by (simp add: mono_def failures_iff)

lemma mono_failures_DIV: "mono (failures (DIV))"
by (simp add: mono_def failures_iff)

(*--------------------------------*
 |          Act_prefix            |
 *--------------------------------*)

lemma mono_failures_Act_prefix:
 "mono (failures P) ==> mono (failures (a -> P))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (simp)
apply (rule)
apply (simp add: in_failures)
apply (auto)
done

(*--------------------------------*
 |        Ext_pre_choice          |
 *--------------------------------*)

lemma mono_failures_Ext_pre_choice:
 "ALL a. mono (failures (Pf a))
  ==> mono (failures (? a:X -> (Pf a)))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_failures)
apply (erule disjE, simp)
apply (rule disjI2)
apply (elim conjE exE)
apply (drule_tac x="a" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (auto)
done

(*--------------------------------*
 |          Ext_choice            |
 *--------------------------------*)

lemma mono_failures_Ext_choice:
 "[| mono (traces P) ; mono (traces Q) ;
     mono (failures P) ; mono (failures Q) |]
  ==> mono (failures (P [+] Q))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_failures)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="(fstF o x)" in spec)
apply (drule_tac x="(fstF o x)" in spec)
apply (drule_tac x="(fstF o y)" in spec)
apply (drule_tac x="(fstF o y)" in spec)
apply (simp add: order_prod_def mono_fstF[simplified mono_def])
apply (elim conjE disjE)
apply (force)+
done

(*--------------------------------*
 |          Int_choice            |
 *--------------------------------*)

lemma mono_failures_Int_choice:
 "[| mono (failures P) ; mono (failures Q) |]
  ==> mono (failures (P |~| Q))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_failures)
apply (elim disjE)
apply (force)
apply (force)
done

(*--------------------------------*
 |        Rep_int_choice          |
 *--------------------------------*)

lemma mono_failures_Rep_int_choice:
 "ALL c. mono (failures (Pf c))
  ==> mono (failures (!! c:C .. (Pf c)))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_failures)
apply (elim conjE bexE)
apply (drule_tac x="c" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (auto)
done

(*--------------------------------*
 |              IF                |
 *--------------------------------*)

lemma mono_failures_IF:
 "[| mono (failures P) ; mono (failures Q) |]
  ==> mono (failures (IF b THEN P ELSE Q))"
apply (simp add: mono_def)
apply (auto simp add: in_failures subsetF_iff)
done

(*--------------------------------*
 |           Interrupt            |
 *--------------------------------*)

lemma mono_failures_Interrupt:
 "[| mono (traces P) ; mono (traces Q) ;
     mono (failures P) ; mono (failures Q) |]
  ==> mono (failures (P /> Q))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_failures)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="(fstF o x)" in spec)
apply (drule_tac x="(fstF o x)" in spec)
apply (drule_tac x="(fstF o y)" in spec)
apply (drule_tac x="(fstF o y)" in spec)
apply (simp add: order_prod_def mono_fstF[simplified mono_def])
apply (elim conjE disjE)
apply (force)+
done

(*--------------------------------*
 |           Parallel             |
 *--------------------------------*)

lemma mono_failures_Parallel:
 "[| mono (failures P) ; mono (failures Q) |]
  ==> mono (failures (P |[X]| Q))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_failures)
apply (elim conjE exE)
apply (rule_tac x="Y" in exI)
apply (rule_tac x="Z" in exI)
apply (simp)
apply (rule_tac x="sa" in exI)
apply (rule_tac x="t" in exI)
apply (auto simp add: subsetF_iff)
done

(*--------------------------------*
 |            Hiding              |
 *--------------------------------*)

lemma mono_failures_Hiding:
 "mono (failures P)
  ==> mono (failures (P -- X))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_failures)
apply (elim conjE exE)
apply (rule_tac x="sa" in exI)
apply (auto simp add: subsetF_iff)
done

(*--------------------------------*
 |           Renaming             |
 *--------------------------------*)

lemma mono_failures_Renaming:
 "mono (failures P)
  ==> mono (failures (P [[r]]))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_failures)
apply (elim conjE exE)
apply (rule_tac x="sa" in exI)
apply (auto simp add: subsetF_iff)
done

(*--------------------------------*
 |           Seq_compo            |
 *--------------------------------*)

lemma mono_failures_Seq_compo:
 "[| mono (failures P) ; mono (failures Q) |]
  ==> mono (failures (P ;; Q))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_failures)

apply (erule disjE)
apply (simp add: subsetF_iff)
apply (elim conjE exE)
apply (rule disjI2)
apply (rule_tac x="sa" in exI)
apply (rule_tac x="t" in exI)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (drule_tac x="y" in spec)
apply (simp)

apply (subgoal_tac "traces P (fstF o x) <= traces P (fstF o y)")
apply (force)
apply (subgoal_tac "fstF o x <= fstF o y")
apply (simp add: mono_traces[simplified mono_def])
apply (simp add: order_prod_def)
apply (rule allI)
apply (drule_tac x="xa" in spec)
apply (simp add: mono_fstF[simplified mono_def])
done

(*--------------------------------*
 |          Depth_rest            |
 *--------------------------------*)

lemma mono_failures_Depth_rest:
 "mono (failures P)
  ==> mono (failures (P |. n))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_failures)
apply (elim conjE exE disjE)
apply (force)
apply (force)
done

(*--------------------------------*
 |            variable            |
 *--------------------------------*)

lemma mono_failures_variable: 
   "mono (failures ($p))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_failures)
apply (simp add: order_prod_def)
apply (drule_tac x="p" in spec)
apply (insert mono_sndF)
apply (simp add: mono_def)
apply (drule_tac x="x p" in spec)
apply (drule_tac x="y p" in spec)
apply (simp add: subsetF_iff order_prod_def)
done

(*--------------------------------*
 |            Procfun             |
 *--------------------------------*)

lemma mono_failures: "mono (failures P)"
apply (induct_tac P)
apply (simp add: mono_failures_STOP)
apply (simp add: mono_failures_SKIP)
apply (simp add: mono_failures_DIV)
apply (simp add: mono_failures_Act_prefix)
apply (simp add: mono_failures_Ext_pre_choice)
apply (simp add: mono_failures_Ext_choice mono_traces)
apply (simp add: mono_failures_Int_choice)
apply (simp add: mono_failures_Rep_int_choice)
apply (simp add: mono_failures_IF)
apply (simp add: mono_failures_Interrupt mono_traces)
apply (simp add: mono_failures_Parallel)
apply (simp add: mono_failures_Hiding)
apply (simp add: mono_failures_Renaming)
apply (simp add: mono_failures_Seq_compo mono_traces)
apply (simp add: mono_failures_Depth_rest)
apply (simp add: mono_failures_variable)
done

(*=============================================================*
 |                         [[P]]Ff                             |
 *=============================================================*)

lemma mono_semFf: "mono [[Pf]]Ff"
apply (simp add: mono_def)
apply (simp add: subdomF_decompo)
apply (intro allI impI)

apply (simp add: mono_failures[simplified mono_def])

apply (subgoal_tac "mono (traces Pf)")
apply (simp add: mono_def)
apply (drule_tac x="fstF o x" in spec)
apply (drule_tac x="fstF o y" in spec)
apply (drule mp)

 apply (simp add: order_prod_def)
 apply (simp add: mono_fstF[simplified mono_def])
 apply (simp)

apply (simp add: mono_traces)
done

(*=============================================================*
 |                         [[P]]Ffun                           |
 *=============================================================*)

lemma mono_semFfun: "mono [[PF]]Ffun"
apply (simp add: prod_mono)
apply (simp add: semFfun_def)
apply (simp add: comp_def)
apply (simp add: proj_fun_def)
apply (simp add: mono_semFf)
done

end
