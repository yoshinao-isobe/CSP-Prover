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

theory CSP_mu
imports CSP_syntax
begin


section \<open> 'nameless'/anonymous (mu-like) recursive processes \<close>

text \<open>
\<mu> is discussed in pages 15 and 34 of Roscoe book TPC.

The syntax proposed is \<mu> p. P and unwind is performed by replacing the
variable p with a new call to \<mu>, i.e., \<mu> p. P = P[(\<mu> p.P)/p] (where Q[R/p]
means the substitution of the process R for all free (i.e., not bound by
some lower-level recursion) occurrences of the process identifier p).

However, Isabelle does not allow to use (\<mu> p. P) in the place of the p
as long as there is a type problem: P is used as a process but its free variable
p must be bound, otherwise P is a lambda term. Indeed, if we try to use the unwind
rule proposed for \<mu>, Isabelle outputs an error and a syntactical translation
reveals duplicate vars in lhs.

syntax
  "muSugar" :: "idt \<Rightarrow> ('pn, 'a) proc \<Rightarrow> ('pn, 'a) proc"
       ("(1\<mu> _ . _)" [900,68] 80)
translations
  "\<mu> p . P" == "let p = (\<mu> p . P) in P"

\<close>

(*
datatype ('a) muPN = p
                   | muP "'a muPN" "('a muPN,'a) proc"

primrec
  muPNfun :: "('a) muPN => (('a) muPN, 'a) proc"
where
  "muPNfun (muP _ P) = (let p = (muP p P) in P)"
*)







datatype ('a) muPN = muP "('a muPN,'a) proc"

primrec
  muPNfun :: "('a) muPN => (('a) muPN, 'a) proc"
where
  "muPNfun (muP P) = P ;; $muP P"


overloading Set_mufun == 
  "PNfun :: (('a) muPN, 'a) pnfun"
begin
  definition "PNfun (pn::('a) muPN) == muPNfun pn"
end


definition
  mu :: "(('a) muPN, 'a) proc => (('a) muPN, 'a) proc"
  where
  mu_def : "mu == (% P. $(muP P))"


(*definition
  mu :: "'pn => ('qn, 'a) proc => ('pn, 'a) proc"
where
    "mu P F == F << (\<lambda>p. $P)"*)

notation (xsymbols) mu ("\<mu> _" [85] 84)




end