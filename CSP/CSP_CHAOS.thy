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

theory CSP_CHAOS
imports CSP_syntax
begin


section \<open> CHAOS \<close>


datatype 'a ChaosName = Chaos "'a set"
                      | ChaosTick "'a set"
                      | ChaosR "'a set"
                      | ChaosRTick "'a set"

primrec
  Chaosfun :: "'a ChaosName => ('a ChaosName, 'a) proc"
where
  "Chaosfun(Chaos A)      = (! x:A -> $(Chaos A)) |~| STOP"
| "Chaosfun(ChaosTick A)  = (! x:A -> $(ChaosTick A)) |~| STOP |~| SKIP"
| "Chaosfun(ChaosR A)     = (? x:A -> $(ChaosR A)) |~| STOP"
| "Chaosfun(ChaosRTick A) = (? x:A -> $(ChaosRTick A)) |~| STOP |~| SKIP"

overloading Set_Chaosfun == 
  "PNfun :: ('a ChaosName, 'a) pnfun"
begin
  definition "(PNfun::('a ChaosName, 'a) pnfun) == Chaosfun"
end


definition
  CHAOS :: "'a set => ('a ChaosName, 'a) proc"
  where
  CHAOS_def : "CHAOS == (%A. $(Chaos A))"


definition
  CHAOSTick :: "'a set => ('a ChaosName, 'a) proc"
  where
  CHAOSTick_def : "CHAOSTick == (%A. $(ChaosTick A))"


definition
  CHAOSr :: "'a set => ('a ChaosName, 'a) proc"
  where
  CHAOSr_def : "CHAOSr == (%A. $(ChaosR A))"


definition
  CHAOSrTick :: "'a set => ('a ChaosName, 'a) proc"
  where
  CHAOSrTick_def : "CHAOSrTick == (%A. $(ChaosRTick A))"


subsection \<open> Guardedness \<close>

lemma guarded_Chaosfun [simp]: "\<forall>p. guarded (Chaosfun p)"
  by (rule, case_tac p, simp_all)

lemma guardedfun_Chaosfun [simp]: "guardedfun Chaosfun"
  by (simp add: guardedfun_def)

declare Set_Chaosfun_def [simp]


end