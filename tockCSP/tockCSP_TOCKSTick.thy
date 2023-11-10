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

theory tockCSP_TOCKSTick
imports tockCSP_tock
begin


subsection \<open> TOCKS from Roscoe's book The Theory and Practice of Concurrency \<close>


subsection \<open> TOCKSTick = TOCKS\<surd> from Roscoe's book The Theory and Practice of Concurrency \<close>


datatype TOCKSTickPN = TOCKSTick

primrec
  TOCKSTickfun ::  "(TOCKSTickPN, 'event::tockCSP) pnfun"
where
  "TOCKSTickfun (TOCKSTick) = (tock \<rightarrow> $(TOCKSTick)) |~| SKIP"

overloading Set_TOCKSTickfun == 
  "PNfun :: (TOCKSTickPN, 'event::tockCSP) pnfun"
begin
  definition "PNfun :: (TOCKSTickPN, 'event::tockCSP) pnfun == TOCKSTickfun"
end

declare Set_TOCKSTickfun_def [simp]


lemma guardedfun_TOCKSTickfun [simp]: "guardedfun TOCKSTickfun"
  apply (simp add: guardedfun_def)
  apply (rule allI, induct_tac p, simp)
  done



end