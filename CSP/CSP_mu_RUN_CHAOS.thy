           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 2022 / 2023               |
            |                                           |
            |          Lemmas and Theorems from         |
            |    Jesus and Sampaio's SBMF 2022 paper,   |
            |    Jesus and Sampaio's SCP 2023 paper     |
            |                     and                   |
            |              Jesus PhD Thesis             |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory CSP_mu_RUN_CHAOS
imports CSP_mu
        CSP_RUN
        CSP_CHAOS
begin


section \<open> mu, RUN and Chaos \<close>

datatype 'a PN = muP "('a PN, 'a) proc"
               | muL "('a PN, 'a) proc" "('a PN, 'a) proc"
               | muR "('a PN, 'a) proc" "('a PN, 'a) proc"
               | Run "'a set"
               | Chaos "'a set"

primrec
  PNfun :: "'a PN => ('a PN, 'a) proc"
where
  "PNfun (muP P) = P ;; $muP P"
| "PNfun (muL P Q) = ( (P ;; $muL P Q) [+] Q )"
| "PNfun (muR P Q) = ( P [+] ( Q ;; $muR P Q ) )"
| "PNfun (Run A) = ? a : A -> $Run(A)"
| "PNfun (Chaos A) = (! x:A -> $(Chaos A)) |~| STOP"

(*TODO?: Does Chaos have |~| SKIP ? *)


overloading Set_PNfun == 
  "CSP_syntax.PNfun :: ('a PN, 'a) pnfun"
begin
  definition "CSP_syntax.PNfun (pn::'a PN) == PNfun pn"
end


definition
  mu :: "('a PN, 'a) proc => ('a PN, 'a) proc"
  where
  mu_def : "mu == (% P. $(muP P))"

notation (xsymbols) mu ("\<mu> _" [85] 84)


definition
  mu_l :: "('a PN, 'a) proc => ('a PN, 'a) proc => ('a PN, 'a) proc"
  where
  mu_l_def : "mu_l == (% P Q. $(muL P Q))"


definition
  mu_r :: "('a PN, 'a) proc => ('a PN, 'a) proc => ('a PN, 'a) proc"
  where
  mu_r_def : "mu_r == (% P Q. $(muR P Q))"

notation (xsymbols) mu_r ("\<mu>R _" [85] 84)


definition
  RUN :: "'a set => ('a PN, 'a) proc"
  where
  RUN_def : "RUN == (% A. $(Run A))"


definition
  CHAOS :: "'a set => ('a PN, 'a) proc"
  where
  CHAOS_def : "CHAOS == (%A. $(Chaos A))"

end