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
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Infra_prog
imports Infra_real
begin

(*****************************************************
                    Progression
 *****************************************************)

primrec
  prog_sum0 :: "nat => (nat => real) => real"
where
  "prog_sum0 (Suc n) f = (prog_sum0 n f) + f (Suc n)"
 |"prog_sum0 0 f = 0"

(* Isabelle 2013 
consts
  prog_sum  :: "nat => nat => (nat => real) => real"
  geo_prop  :: "real => real => nat => real"

defs
  prog_sum_def : 
    "prog_sum m n f == (prog_sum0 n f) - (prog_sum0 m f)"

  geo_prop_def :
    "geo_prop K alpha == (%n. (alpha^(n - (Suc 0))) * K)"
*)

definition
  prog_sum  :: "nat => nat => (nat => real) => real"
  where
  "prog_sum m n f == (prog_sum0 n f) - (prog_sum0 m f)"

definition
  geo_prop  :: "real => real => nat => real"
  where
    "geo_prop K alpha == (%n. (alpha^(n - (Suc 0))) * K)"

lemma geo_prog_sum0: 
  "prog_sum0 n (geo_prop K alpha) * ((1::real) - alpha)
       = K*((1::real)-(alpha^n))"
apply (induct_tac n)
apply (simp)
apply (simp add: geo_prop_def)
apply (simp add: distrib_right)
apply (simp add: right_diff_distrib)
done

lemma geo_prog_sum: 
  "prog_sum m n (geo_prop K alpha) * ((1::real) - alpha)
       = K*((alpha^m)-(alpha^n))"
apply (unfold prog_sum_def)
apply (simp add: left_diff_distrib)
apply (simp add: geo_prog_sum0)
apply (simp add: right_diff_distrib)
done

lemmas geo_prog_sum_sym = geo_prog_sum[THEN sym]

lemma geo_prog_sum_div: 
  "alpha < (1::real)
    ==> prog_sum m n (geo_prop K alpha)
      = K*((alpha^m)-(alpha^n)) / ((1::real)-alpha)"
by (simp add: geo_prog_sum_sym)

lemma geo_prog_sum_infinite: 
  "[| (0::real) <= K ; (0::real) <= alpha |]
   ==>  prog_sum m n (geo_prop K alpha) * ((1::real)-alpha)
       <= K*(alpha^m)"
apply (simp add: geo_prog_sum)
apply (simp add: right_diff_distrib)
(*
apply (simp add: real_mult_order_eq)
for Isabelle 2013
apply (simp add: zero_le_power real_mult_order_eq)
for Isabelle 2007
*)
done

lemma geo_prog_sum_infinite_div: 
  "[| (0::real) <= K ; (0::real) <= alpha ; alpha < (1::real) |] 
   ==> prog_sum m n (geo_prop K alpha) <= K*(alpha^m)/((1::real)-alpha)"
apply (simp add: real_div_le_eq)
apply (simp_all add: geo_prog_sum_infinite)
done

end
