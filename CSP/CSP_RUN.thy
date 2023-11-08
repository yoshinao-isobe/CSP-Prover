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

theory CSP_RUN
imports CSP_runs
        CSP_syntax
begin


subsection \<open> RUN process, Run process name and equation (PNfun) \<close>

datatype 'a RunName = Run "'a set"

primrec
  Runfun :: "('a RunName, 'a) pnfun"
where
  "Runfun (Run A) = ? a : A -> $Run(A)"


overloading Set_Runfun == 
  "PNfun :: ('a RunName, 'a) pnfun"
begin
  definition "(PNfun::('a RunName, 'a) pnfun) == Runfun"
end

declare Set_Runfun_def [simp]




subsection \<open> Guardedness \<close>

lemma guarded_Runfun [simp]: "\<forall>p. guarded (Runfun p)"
  by (rule, case_tac p, simp)

lemma guardedfun_Runfun [simp]: "guardedfun Runfun"
  by (simp add: guardedfun_def)



(* RUN process *)

definition RUN :: "'a set => ('a RunName, 'a) proc"
where
  "RUN(A) = $(Run A)"





end