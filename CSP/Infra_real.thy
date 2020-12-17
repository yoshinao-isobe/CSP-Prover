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
            |                  April 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2020         |
            |                  April 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Infra_real
imports Infra_common
begin

(*****************************************************
                    Real number
 *****************************************************)

(* this lemma real_mult_less_mono
   was given in Isabelle 2005, but is removed in Isabelle 2007 *)

lemma real_mult_less_mono:
     "[| u<v;  x<y;  (0::real) < v;  0 < x |] ==> u*x < v* y"
by (simp add: Rings.mult_strict_mono order_less_imp_le)
(* by (simp add: Ring_and_Field.mult_strict_mono order_less_imp_le)     isabelle2009-1 *)

(* mult_commute for Isabelle 2016 *)
lemma mult_commute: "(x::real) * y = y * x"
apply (simp)
done

lemma real_mult_add_distrib: "(x::real) * (y + z) = x * y + x * z"
apply (subgoal_tac "x * (y + z) = (y + z) * x")
 (* apply (simp add: real_add_mult_distrib)   isabelle 2011 *)
(* apply (simp add: distrib)  Isabelle 2013 *)
apply (simp add: distrib_left)
apply (simp add: mult_commute)
done

lemma real_mult_order_eq : "[| 0 <= x; 0 <= y |] ==> (0::real) <= x * y"
apply (case_tac "x = 0", simp)
apply (case_tac "y = 0", simp)
apply (subgoal_tac "0 < x * y")
apply (simp)
(* apply (simp add: real_mult_order)  isabelle 2011 *)
apply (simp add: zero_less_mult_iff)
done

lemma real_div_le_eq:
   "0 < (z::real) ==> (x <= y / z) = (x * z <= y)"
apply (rule iffI)
apply (insert mult_right_mono[of x "y/z" z], simp)
apply (insert real_mult_le_cancel_iff1[of z x "y/z"], simp)
done

lemma real_div_less_eq:
   "0 < (z::real) ==> (x < y / z) = (x * z < y)"
apply (rule iffI)
apply (insert real_mult_less_iff1[of z x "y/z"], simp)
apply (insert mult_less_cancel_right[of x "y/z" z], simp)
done

lemma real_less_div_eq:
   "0 < (z::real) ==> (x / z < y) = (x < y * z)"
apply (rule iffI)
apply (insert real_mult_less_iff1[of z "x/z" y], simp)
apply (insert mult_less_cancel_right[of "x/z" y z], simp)
done

lemma real_mult_div_commute: 
     "[| (0::real) <= x ; 0 < y ; 0 < z ; 0 < r |]
        ==> (x < y * z / r) = (r * x / z < y)"
apply (simp add: real_div_less_eq)
apply (simp add: real_less_div_eq)
apply (simp add: mult_commute)
done

lemma real_mult_div_commuteI: 
     "[| (0::real) <= x ; 0 < y ; 0 < z ; 0 < r ; x < y * z / r |]
        ==> (r * x / z < y)"
apply (simp add: real_mult_div_commute)
done

lemma real_mult_less_iff2: "(0::real) < z ==> (z*x < z*y) = (x < y)"
by (simp add: mult_commute)

lemma real_mult_less_if2: "[| (0::real) < z ; (x::real) < y |] ==> z*x < z*y"
by (simp add: real_mult_less_iff2)

lemma real_mult_less_if1: "[| (0::real) < z ; (x::real) < y |] ==> x*z < y*z"
by (simp)

(*** rev_power_decreasing ***)

lemma rev_power_decreasing:
  "[| (0::real) < r ; r < 1 ; r ^ n <= r ^ m |] ==> m <= n"

apply (case_tac "m <= n")
 apply (simp)

(* else n < m --> contradiction *)
apply (insert power_decreasing[of "Suc n" m r])
  apply (simp)
(*
not necessary for isabelle 2020:
apply (subgoal_tac "r * r ^ n <  1 * r ^ n")
apply (simp)
apply (rule real_mult_less_if1)
by (simp_all)
*)
  done

(*** rev_power_decreasing_strict ***)

lemma rev_power_decreasing_strict :
  "[| (0::real) < r ; r < 1 ; r ^ n < r ^ m |] ==> m < n"
apply (case_tac "m < n")
 apply (simp)

(* else n <= m --> contradiction *)
apply (insert power_decreasing[of n m r])
by (simp)

end
