           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 2022 / 2023               |
            |                                           |
            |          Lemmas and Theorems from         |
            |    Jesus and Sampaio's SBMF 2022 paper    |
            |                     and                   |
            |    Jesus and Sampaio's SCP 2023 paper     |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory tockCSP_Infra_CSP_T
imports tockCSP.tockCSP_Infra
        CSP_T.CSP_T_semantics
begin


subsection \<open> tockCSP_Infra_CSP_T - TODO: move to CSP_T \<close>

lemma SKIP_domT: "{t. (t = <> | t = <Tick>) } : domT"
  apply (simp add: domT_def HC_T1_def)
  apply (rule conjI)
  apply (rule_tac x="<>" in exI, simp)
  
  apply (simp add: prefix_closed_def)
  apply (intro allI impI)
  apply (elim conjE exE)
  
  apply (erule disjE, simp)    (* <> *)
  
  by (simp_all)




end