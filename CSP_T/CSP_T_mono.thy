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

theory CSP_T_mono
imports CSP_T_traces
begin

(*****************************************************************

         1. mono check of tracesfun
         2. 
         3. 
         4. 

 *****************************************************************)

(*--------------------------------*
 |        STOP,SKIP,DIV           |
 *--------------------------------*)

lemma mono_traces_STOP: "mono (traces (STOP))"
by (simp add: mono_def traces_iff)

lemma mono_traces_SKIP: "mono (traces (SKIP))"
by (simp add: mono_def traces_iff)

lemma mono_traces_DIV: "mono (traces (DIV))"
by (simp add: mono_def traces_iff)

(*--------------------------------*
 |          Act_prefix            |
 *--------------------------------*)

lemma mono_traces_Act_prefix:
 "mono (traces P) ==> mono (traces (a -> P))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (simp)
apply (rule)
apply (simp add: in_traces)
apply (auto)
done

(*--------------------------------*
 |        Ext_pre_choice          |
 *--------------------------------*)

lemma mono_traces_Ext_pre_choice:
 "ALL a. mono (traces (Pf a))
  ==> mono (traces (? a:X -> (Pf a)))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_traces)
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

lemma mono_traces_Ext_choice:
 "[| mono (traces P) ; mono (traces Q) |]
  ==> mono (traces (P [+] Q))"
apply (simp add: mono_def)
apply (auto simp add: in_traces subdomT_iff)
done

(*--------------------------------*
 |          Int_choice            |
 *--------------------------------*)

lemma mono_traces_Int_choice:
 "[| mono (traces P) ; mono (traces Q) |]
  ==> mono (traces (P |~| Q))"
apply (simp add: mono_def)
apply (auto simp add: in_traces subdomT_iff)
done

(*--------------------------------*
 |        Rep_int_choice          |
 *--------------------------------*)

lemma mono_traces_Rep_int_choice:
 "ALL c: sumset C. mono (traces (Pf c))
  ==> mono (traces (!! :C .. Pf))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_traces)
apply (erule disjE, simp)
apply (rule disjI2)
apply (elim conjE bexE)
apply (drule_tac x="c" in bspec, simp)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (auto)
done

(*--------------------------------*
 |              IF                |
 *--------------------------------*)

lemma mono_traces_IF:
 "[| mono (traces P) ; mono (traces Q) |]
  ==> mono (traces (IF b THEN P ELSE Q))"
apply (simp add: mono_def)
apply (auto simp add: in_traces subdomT_iff)
done

(*--------------------------------*
 |           Interrupt            |
 *--------------------------------*)

lemma mono_traces_Interrupt:
 "[| mono (traces P) ; mono (traces Q) |]
  ==> mono (traces (P /> Q))"
apply (simp add: mono_def)
apply (simp add: subdomT_iff)
apply (simp add: in_traces)
apply (intro allI impI)
apply (elim conjE exE)
apply (rule disjI2)
apply (rule_tac x="s" in exI)
apply (rule_tac x="u" in exI)
apply (auto simp add: subdomT_iff)
done

(*--------------------------------*
 |           Parallel             |
 *--------------------------------*)

lemma mono_traces_Parallel:
 "[| mono (traces P) ; mono (traces Q) |]
  ==> mono (traces (P |[X]| Q))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_traces)
apply (elim conjE exE)
apply (rule_tac x="s" in exI)
apply (rule_tac x="ta" in exI)
apply (auto simp add: subdomT_iff)
done

(*--------------------------------*
 |            Hiding              |
 *--------------------------------*)

lemma mono_traces_Hiding:
 "mono (traces P)
  ==> mono (traces (P -- X))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_traces)
apply (elim conjE exE)
apply (rule_tac x="s" in exI)
apply (auto simp add: subdomT_iff)
done

(*--------------------------------*
 |           Renaming             |
 *--------------------------------*)

lemma mono_traces_Renaming:
 "mono (traces P)
  ==> mono (traces (P [[r]]))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_traces)
apply (elim conjE exE)
apply (rule_tac x="s" in exI)
apply (auto simp add: subdomT_iff)
done

(*--------------------------------*
 |           Seq_compo            |
 *--------------------------------*)

lemma mono_traces_Seq_compo:
 "[| mono (traces P) ; mono (traces Q) |]
  ==> mono (traces (P ;; Q))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_traces)
apply (erule disjE)
apply (simp add: subdomT_iff)
apply (fast)

apply (elim conjE exE)
apply (rule disjI2)
apply (rule_tac x="s" in exI)
apply (rule_tac x="ta" in exI)
apply (auto simp add: subdomT_iff)
done

(*--------------------------------*
 |          Depth_rest            |
 *--------------------------------*)

lemma mono_traces_Depth_rest:
 "mono (traces P)
  ==> mono (traces (P |. n))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_traces)
apply (elim conjE exE)
apply (auto simp add: subdomT_iff)
done

(*--------------------------------*
 |            variable            |
 *--------------------------------*)

lemma mono_traces_variable: 
   "mono (traces ($p))"
apply (simp add: mono_def)
apply (intro allI impI)
apply (rule)
apply (simp add: in_traces)
apply (simp add: order_prod_def)
apply (auto simp add: subdomT_iff)
done

(*--------------------------------*
 |            Procfun             |
 *--------------------------------*)

lemma mono_traces: "mono (traces P)"
apply (induct_tac P)
apply (simp add: mono_traces_STOP)
apply (simp add: mono_traces_SKIP)
apply (simp add: mono_traces_DIV)
apply (simp add: mono_traces_Act_prefix)
apply (simp add: mono_traces_Ext_pre_choice)
apply (simp add: mono_traces_Ext_choice)
apply (simp add: mono_traces_Int_choice)
apply (simp add: mono_traces_Rep_int_choice)
apply (simp add: mono_traces_IF)
apply (simp add: mono_traces_Interrupt)
apply (simp add: mono_traces_Parallel)
apply (simp add: mono_traces_Hiding)
apply (simp add: mono_traces_Renaming)
apply (simp add: mono_traces_Seq_compo)
apply (simp add: mono_traces_Depth_rest)
apply (simp add: mono_traces_variable)
done

(*=============================================================*
 |                          [[P]]Tf                            |
 *=============================================================*)

lemma mono_semTf: "mono [[Pf]]Tf"
apply (simp add: semTf_def)
apply (simp add: mono_traces)
done

(*=============================================================*
 |                         [[P]]Tfun                           |
 *=============================================================*)

lemma mono_semTfun: "mono [[Pf]]Tfun"
apply (simp add: prod_mono)
apply (simp add: semTfun_def)
apply (simp add: proj_fun_def)
apply (simp add: comp_def)
apply (simp add: mono_semTf)
done

end
