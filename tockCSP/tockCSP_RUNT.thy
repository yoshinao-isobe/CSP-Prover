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

theory tockCSP_RUNT
imports tockCSP_tock
        CSP.CSP_RUN
begin

definition
  RUNT :: "'a set => ('a RunName, 'a::tockCSP) proc" ("RUN\<^sub>T")
where
  "RUN\<^sub>T S == RUN(S \<union> {tock})"

end