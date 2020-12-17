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

theory Infra_nat
imports Infra_common
begin

(*****************************************************
                      nat
 *****************************************************)

lemma nat_zero_or_Suc: "ALL n::nat. n=0 | (EX m::nat. n=Suc m)"
apply (intro allI)
apply (induct_tac n)
apply (simp)
apply (rule disjI2)
apply (erule disjE)
apply (rule_tac x=0 in exI)
apply (simp)
apply (erule exE)
apply (rule_tac x="Suc m" in exI)
apply (simp)
done

(*** min ***)

lemma min_is1: "(m::'a::order) <= n ==> min m n = m"
by (simp add: min_def)

lemma min_is2: "(n::'a::order) <= m ==> min m n = n"
apply (simp add: min_def)
done

lemmas min_is = min_is1 min_is2

(*** max ***)

lemma max_is1: "(m::'a::order) <= n ==> max m n = n"
by (simp add: max_def)

lemma max_is2: "(n::'a::order) <= m ==> max m n = m"
apply (simp add: max_def)
done

lemmas max_is = max_is1 max_is2

end
