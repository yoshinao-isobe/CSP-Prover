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

theory tockCSP_Infra_HOL
imports Complex_Main
begin



lemma impPE :
  assumes "P \<longrightarrow> Q" "P = P2" P2 "Q \<Longrightarrow> R"
  shows R
proof -
  from assms have "P2" by (simp)
  with assms have "P" by (simp)
  with assms have "Q" by (simp)
  with assms show ?thesis by (simp) 
qed





lemma subset_doubleton_iff:
   "A \<subseteq> {x,y} \<longleftrightarrow> A = {} \<or> A = {x} \<or> A = {y} \<or> A = {x,y}"
  by fast


lemma insert_eq_doubleton : "insert (b) (A) = {a, b} \<Longrightarrow> a \<noteq> b \<Longrightarrow> b \<notin> A \<Longrightarrow> A = {a}"
  by (auto)


lemma Union_constant :
    "I \<noteq> {} \<Longrightarrow> \<Union> {X. X = A \<and> (\<exists>i. i \<in> I)} = A"
  by (auto)


end