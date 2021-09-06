           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021               |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory Infra_neset
imports Infra_set
begin            



typedef ('e) neset = "{ X::'e set . X \<noteq> {} }" morphisms to_set to_neset
by (auto)

setup_lifting type_definition_neset

declare [[coercion to_neset]]


lemma to_neset_inverse_Un [simp]: "S \<union> R \<noteq> {} \<Longrightarrow> (to_set (to_neset (S \<union> R))) = (S \<union> R)"
by (simp add: to_neset_inverse)



end