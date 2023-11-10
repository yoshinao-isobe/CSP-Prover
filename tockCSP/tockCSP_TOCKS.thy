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

theory tockCSP_TOCKS
imports tockCSP_tock
begin


subsection \<open> TOCKS from Roscoe's book The Theory and Practice of Concurrency \<close>


datatype TOCKSPN = TOCKS

primrec
  TOCKSfun ::  "(TOCKSPN, 'event::tockCSP) pnfun"
where
  "TOCKSfun (TOCKS) = tock \<rightarrow> $(TOCKS)"

overloading Set_TOCKSfun == 
  "PNfun :: (TOCKSPN, 'event::tockCSP) pnfun"
begin
  definition "PNfun :: (TOCKSPN, 'event::tockCSP) pnfun == TOCKSfun"
end

declare Set_TOCKSfun_def [simp]


lemma guardedfun_TOCKSfun [simp]: "guardedfun TOCKSfun"
  apply (simp add: guardedfun_def)
  by (rule allI, induct_tac p, simp)




end