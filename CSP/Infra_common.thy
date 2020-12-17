           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   June 2005  (modified)   |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Infra_common
imports Complex_Main
begin

(*****************************************************
           Convenient technique for proofs
 *****************************************************)

(*--------------------------*
 |    remove assumeption    |
 *--------------------------*)

lemma rem_asmE: "[| A ; R |] ==> R"
by simp

(*--------------------------*
 |      !!x. ==> ALL x.     |
 *--------------------------*)

lemma rev_all1E:
   "[| !!x. P x ; ALL x. P x ==> S |] ==> S"
by (auto)

lemma rev_all2E:
   "[| !!x y. P x y ; ALL x y. P x y ==> S |] ==> S"
by (auto)

lemma rev_all3E:
   "[| !!x y z. P x y z ; ALL x y z. P x y z ==> S |] ==> S"
by (auto)

lemmas rev_allE = rev_all1E rev_all2E rev_all3E

lemma rev_allI: "ALL x. P x ==> (!!x. P x)"
by (auto)

end
