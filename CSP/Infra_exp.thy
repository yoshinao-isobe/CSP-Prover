           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   June 2005  (modified)   |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Infra_exp
imports Infra_order
begin

(*****************************
         powr --> pow  
 *****************************)

lemma nat_powr_pow:
  "(0::real) < r ==> r powr (real n) = r ^ n"
apply (induct_tac n)
apply (simp)
(* for Isabelle 2013
apply (simp add: real_of_nat_Suc) *)
(* apply (simp add: of_nat_Suc) *)
apply (simp add: powr_add)
done

(*****************************************************
              Exponentail convergence
 *****************************************************)

lemma powr_less_mono_inv:
  "[| (1::real) < a ; (x::real) < y |]
     ==> (inverse a) powr y < (inverse a) powr x"
apply (simp add: powr_def)
apply (auto simp add: ln_inverse)
done

lemma powr_less_mono_conv:
  "[| (0::real) < a ; a < (1::real) ; (x::real) < y |]
    ==> a powr y < a powr x"
apply (insert powr_less_mono_inv[of "inverse a" x y])
apply (simp)
apply (subgoal_tac "1 < inverse a")
apply (simp)
apply (rule inverse_less_imp_less)
apply (simp_all)
done

lemma powr_convergence:
  "[| (0::real) < alpha ; alpha < (1::real) ; (0::real) < x |]
      ==> (EX n::nat. alpha powr (real n) < x)"
apply (insert powr_log_cancel[of "alpha" x])
apply (insert reals_Archimedean2[of "log alpha x"])
apply (erule exE) 
apply (subgoal_tac "alpha powr real n < alpha powr log alpha x")
apply (rule_tac x="n" in exI)
apply (simp)
apply (insert powr_less_mono_conv[of "alpha" "log alpha x"])
by (simp)

lemma pow_convergence:
  "[| (0::real) <= alpha ; alpha < (1::real) ; (0::real) < x |]
   ==> (EX n::nat. alpha^n < x)"

apply (case_tac "alpha=0")
 apply (rule_tac x="1" in exI)
 apply (simp)

apply (case_tac "0 < alpha")
 apply (insert powr_convergence[of "alpha" x])
 apply (simp)
 apply (erule exE)
 apply (rule_tac x="n" in exI)
 apply (simp add: nat_powr_pow)

apply (simp add: less_le)
done

(*** if 0 <=alpha < 1 then alpha^n ----> 0 ***)

lemma zero_isGLB_pow:
  "[| (0::real) <= alpha ; alpha < 1 |] 
   ==> (0 isGLB {r. EX n. r = alpha ^ n})"
apply (simp add: isGLB_def isLB_def)
apply (rule conjI)

(* lb *)

apply (intro allI impI)
apply (erule exE)
apply (simp)
(* 
apply (simp add: zero_le_power) was necessary in Isabelle 2005 
*)

(* glb *)

apply (intro allI impI)
apply (case_tac "y <=0")
apply (simp)

 (* 0 < y *)
 apply (subgoal_tac "EX n. alpha ^ n < y")
 apply (simp)
 apply (erule exE)
 apply (drule_tac x="alpha ^ n" in spec)
 apply (simp)
 apply (drule_tac x="n" in spec)
 apply (simp)

 apply (simp add: pow_convergence)
done

(*** GLB ***)

lemma zero_GLB_pow:
  "[| (0::real) <= alpha ; alpha < 1 |] 
   ==> GLB {r. EX n. r = alpha ^ n} = 0"
apply (subgoal_tac "{r. EX n. r = alpha ^ n} hasGLB")
apply (simp add: GLB_iff zero_isGLB_pow)
apply (insert zero_isGLB_pow[of alpha])
apply (simp add: hasGLB_def)
apply (rule_tac x="0" in exI)
by (simp)

end
