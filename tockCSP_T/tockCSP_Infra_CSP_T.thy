theory tockCSP_Infra_CSP_T
imports tockCSP.tockCSP_Infra
        CSP_T
begin


subsection \<open> CSP_T \<close>


lemma SKIP_domT: "{t. (t = <> | t = <Tick>) } : domT"
  apply (simp add: domT_def HC_T1_def)
  apply (rule conjI)
  apply (rule_tac x="<>" in exI, simp)
  
  apply (simp add: prefix_closed_def)
  apply (intro allI impI)
  apply (elim conjE exE)
  
  apply (erule disjE, simp)    (* <> *)
  
  by (simp_all)


lemma FIX_traces :
    "(Pf::('pn,'e) pnfun) = PNfun \<Longrightarrow>
     FPmode = CMSmode \<longrightarrow> guardedfun Pf \<Longrightarrow>
     traces ($(p::'pn)) MT = traces ((FIX Pf) p) MT"
  apply (insert cspT_FIX[of Pf p])
  apply (simp add: cspT_semantics)
  by (case_tac FPmode, simp_all)




end