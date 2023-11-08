           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009-2       |
            |                October 2010  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                  April 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CMS
imports Infra
begin

(*****************************************************************

         1. Metric space (MS)
         2. Complete metric space (CMS)
         3. Contracting map
         4. Banach Theorem

 *****************************************************************)


(*
axclass ms0 < type
consts 
  distance    :: "'a::ms0 * 'a::ms0 => real"  (* Distance function *)
*)

class ms0 =
  fixes distance    :: "'a * 'a => real"  ("distance") (* Distance function *)

(********************************************************** 
                    metric space (MS)
 **********************************************************)

(*  isabelle 2009-1
axclass
  ms < ms0
  positive_ms           : 
    "ALL (x::'a::ms0) (y::'a::ms0). 0 <= distance(x,y)"
  diagonal_ms           : 
    "ALL (x::'a::ms0) (y::'a::ms0). (distance(x,y) = 0) = (x = y)"
  symmetry_ms           : 
    "ALL (x::'a::ms0) (y::'a::ms0). distance(x,y) = distance(y,x)"
  triangle_inequality_ms: 
    "ALL (x::'a::ms0) (y::'a::ms0) (z::'a::ms0). 
       distance(x,z) <= distance(x,y)+distance(y,z)"
*)


class ms = ms0 +
  assumes positive_ms           : 
    "ALL (x::'a::ms0) (y::'a::ms0). 0 <= distance(x,y)"
  assumes diagonal_ms           : 
    "ALL (x::'a::ms0) (y::'a::ms0). (distance(x,y) = 0) = (x = y)"
  assumes symmetry_ms           : 
    "ALL (x::'a::ms0) (y::'a::ms0). distance(x,y) = distance(y,x)"
  assumes triangle_inequality_ms: 
    "ALL (x::'a::ms0) (y::'a::ms0) (z::'a::ms0). 
       distance(x,z) <= distance(x,y)+distance(y,z)"

(*
class ms = ms0 +
  assumes positive_ms           : 
    "0 <= distance(x,y)"
  assumes diagonal_ms           : 
    "(distance(x,y) = 0) = (x = y)"
  assumes symmetry_ms           : 
    "distance(x,y) = distance(y,x)"
  assumes triangle_inequality_ms: 
    "distance(x,z) <= distance(x,y)+distance(y,z)"
*)

declare positive_ms [simp]

(*
lemma all_positive_ms:
      "ALL (x::'a::ms) (y::'a::ms). 0 <= distance(x,y)"
by (simp add: positive_ms)

lemma all_diagonal_ms:
      "ALL (x::'a::ms) (y::'a::ms). (distance(x,y) = 0) = (x = y)"
by (simp add: diagonal_ms)

lemma all_symmetry_ms:
  "ALL (x::'a::ms) (y::'a::ms). distance(x,y) = distance(y,x)"
by (simp add: symmetry_ms)

lemma all_triangle_inequality_ms:
  "ALL (x::'a::ms) (y::'a::ms) (z::'a::ms).
   distance(x,z) <= distance(x,y)+distance(y,z)"
by (simp add: triangle_inequality_ms)
*)

(*------------------*
 | cauchy and limit |
 *------------------*)

definition
  cauchy     :: "'a::ms infinite_seq => bool"
  where
  cauchy_def :"cauchy xs == ALL delta::real. 
               0 < delta --> (EX n. ALL i j. 
                    ((n <= i & n <= j) --> (distance(xs i, xs j) < delta)))"
  
definition
  convergeTo :: "'a::ms infinite_seq => 'a::ms => bool"  
                ("_ convergeTo _" [55,55] 55)
  where
  convergeTo_def :"xs convergeTo x == ALL eps::real. 0 < eps --> (EX n. ALL m.
                    n <= m --> distance(x, xs m) < eps)"
  
(*definition
  hasLimit   :: "'a::ms infinite_seq => bool"
  ...
*)

definition
  Limit      :: "'a::ms infinite_seq => 'a::ms"
  where
  Limit_def      :"Limit xs    == THE x. xs convergeTo x"

(*---------*
 | mapping |
 *---------*)
(* Isabelle 2013
consts
  non_expanding     :: "('a::ms => 'b::ms) => bool"
  contraction       :: "('a::ms => 'b::ms) => bool"
  contraction_alpha :: "('a::ms => 'b::ms) => real => bool"
  map_alpha         :: "('a::ms => 'b::ms) => real => bool"

defs
  non_expanding_def    : 
     "non_expanding f == map_alpha f 1"
  contraction_def      : 
     "contraction f == EX (alpha::real). contraction_alpha f alpha"
  contraction_alpha_def: 
     "contraction_alpha f alpha == (alpha < 1 & map_alpha f alpha)"
  map_alpha_def: 
     "map_alpha f alpha == (0 <= alpha &
              (ALL x y. distance(f x,f y) <= (alpha * distance(x,y))))"
*)

definition  
  map_alpha         :: "('a::ms => 'b::ms) => real => bool"
  where
  map_alpha_def: 
     "map_alpha f alpha == (0 <= alpha &
              (ALL x y. distance(f x,f y) <= (alpha * distance(x,y))))"

definition
  non_expanding     :: "('a::ms => 'b::ms) => bool"
  where
  non_expanding_def    : 
     "non_expanding f == map_alpha f 1"
  
definition  
  contraction_alpha :: "('a::ms => 'b::ms) => real => bool"
  where
  contraction_alpha_def: 
     "contraction_alpha f alpha == (alpha < 1 & map_alpha f alpha)"

definition  
  contraction       :: "('a::ms => 'b::ms) => bool"
  where
  contraction_def      : 
     "contraction f == EX (alpha::real). contraction_alpha f alpha"
  
  

(********************************************************** 
                     small lemmas 
 **********************************************************)

lemma same_pnt_zero[simp]: "distance((x::'a::ms),x)=0"
by (simp add: diagonal_ms)

lemma diff_pnt_pos_only_if:
  "0 < distance(x::'a::ms,y) ==> x ~= y"
apply (case_tac "x = y")
by (simp_all)

lemma diff_pnt_pos_if:
  "(x::'a::ms) ~= y ==> 0 < distance(x,y)"
apply (case_tac "distance (x, y) = 0")
apply (simp add: diagonal_ms)
by (simp add: less_le)

lemma diff_pnt_pos:
  "(0 < distance(x::'a::ms,y)) = (x ~= y)"
apply (rule iffI)
apply (simp add: diff_pnt_pos_only_if)
apply (simp add: diff_pnt_pos_if)
done

(********************************************************** 
                         map
 **********************************************************)

(*** contraction_alpha ***)

lemma contraction_alpha_range: 
  "contraction_alpha f alpha ==> 0 <= alpha & alpha < 1"
by (simp add: contraction_alpha_def map_alpha_def)

(*** contraction --> non expanding ***)

lemma contraction_non_expanding: 
  "contraction f ==> non_expanding f"

apply (simp add: contraction_def contraction_alpha_def map_alpha_def
                 non_expanding_def)
apply (elim conjE exE)
apply (intro allI)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)

apply (subgoal_tac "alpha * distance (x, y) <= 1 * distance (x, y)")
apply (simp)

by (rule mult_right_mono, simp_all)

(*** composition ***)
(* map_alpha *)

lemma compo_map_alpha:
   "[| map_alpha f alpha1 ; map_alpha g alpha2 |]
     ==> map_alpha (f o g) (alpha1 * alpha2)"
apply (simp add: map_alpha_def)
apply (elim conjE)
apply (insert mult_right_mono[of 0 alpha1 alpha2], simp)

apply (intro allI)
apply (drule_tac x="g x" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="g y" in spec)
apply (drule_tac x="y" in spec)

apply (subgoal_tac 
  "alpha1 * distance (g x, g y) <= alpha1 * alpha2 * distance (x, y)") (* ...1 *)
apply (simp)
      (* 1 *)
(* by (simp add: real_mult_assoc mult_left_mono)  isabelle 2011 *)
by (simp add: mult.assoc mult_left_mono)

lemma compo_contra_alpha:
   "[| contraction_alpha f alpha1 ; contraction_alpha g alpha2 |]
     ==> contraction_alpha (f o g) (alpha1 * alpha2)"
apply (simp add: contraction_alpha_def)
apply (simp add: compo_map_alpha)
apply (simp add: map_alpha_def)
apply (case_tac "alpha2 = 0", simp)
apply (insert real_mult_less_mono[of alpha1 "1::real" alpha2 "1::real"])
by (force)

lemma compo_non_expand_map_alpha:
   "[| non_expanding f ; map_alpha g alpha |]
     ==> map_alpha (f o g) alpha"
apply (simp add: non_expanding_def)
apply (insert compo_map_alpha[of f 1 g alpha])
by (simp)

lemma compo_map_alpha_non_expand:
   "[| map_alpha f alpha ; non_expanding g |]
     ==> map_alpha (f o g) alpha"
apply (simp add: non_expanding_def)
apply (insert compo_map_alpha[of f alpha g 1])
by (simp)

lemma compo_non_expand_contra_alpha:
   "[| non_expanding f ; contraction_alpha g alpha |]
     ==> contraction_alpha (f o g) alpha"
apply (simp add: contraction_alpha_def)
by (simp add: compo_non_expand_map_alpha)

lemma compo_contra_alpha_non_expand:
   "[| contraction_alpha f alpha ; non_expanding g |]
     ==> contraction_alpha (f o g) alpha"
apply (simp add: contraction_alpha_def)
by (simp add: compo_map_alpha_non_expand)

lemma compo_non_expand:
   "[| non_expanding f ; non_expanding g |]
     ==> non_expanding (f o g)"
apply (simp add: non_expanding_def)
apply (insert compo_map_alpha[of f 1 g 1])
by (simp)

(********************************************************** 
                     convergeTo
 **********************************************************)

(*** The limit is unique ***)

lemma unique_convergence: 
  "[| xs convergeTo x ; xs convergeTo y |] ==> x = y"

apply (case_tac "x = y")
apply (simp)

apply (simp add: convergeTo_def)

apply (drule_tac x="distance (x, y) /2" in spec)
apply (drule_tac x="distance (x, y) /2" in spec)
apply (simp add: diff_pnt_pos)
apply (elim exE)

apply (rename_tac n m)
apply (drule_tac x="max n m" in spec)
apply (drule_tac x="max n m" in spec)
apply (simp)
 (* apply (simp add: le_maxI1 le_maxI2)  Isabelle 2005 *)

apply (insert triangle_inequality_ms)
apply (drule_tac x="x" in spec)
apply (drule_tac x="xs (max n m)" in spec)
apply (drule_tac x="y" in spec)

apply (simp add: symmetry_ms)
done

(*** Convergence implies cauchy seq***)

lemma convergece_cauchy: "xs convergeTo x ==> cauchy xs"

apply (simp add: cauchy_def)
apply (intro allI impI)

apply (simp add: convergeTo_def)
apply (drule_tac x="delta/2" in spec)
apply (simp)
apply (erule exE)

apply (rule_tac x="n" in exI)
apply (intro allI impI)

apply (frule_tac x="i" in spec)
apply (drule_tac x="j" in spec)
apply (simp)

apply (insert triangle_inequality_ms)
apply (drule_tac x="xs i" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="xs j" in spec)
apply (simp add: symmetry_ms)
done

(********************************************************** 
                Complete metric space (CMS)
 **********************************************************)

(*
isabelle2009-1

axclass
  cms < ms

  complete_ms: "ALL xs. cauchy xs --> (EX x. xs convergeTo x)"

*)

class cms = ms +
assumes complete_ms: "ALL (xs::(nat=>'a::ms)). cauchy xs --> (EX x. xs convergeTo x)"

(********************************************************** 
                     CMS lemmas
 **********************************************************)

lemma convergeTo_to_Limit : 
    "cauchy (xs::'a::cms infinite_seq)
       ==> (xs convergeTo x) = (x = Limit xs)"
apply (simp add: Limit_def)
apply (rule iffI)
apply (rule sym)
apply (rule the_equality)
apply (simp)
apply (simp add: unique_convergence)

apply (simp)
apply (insert complete_ms)
apply (drule_tac x="xs" in spec, simp)
apply (erule exE)
apply (rule theI[of "(%x. xs convergeTo x)"])
apply (simp)
apply (simp add: unique_convergence)
done

lemma Limit_to_convergeTo:
    "cauchy (xs::'a::cms infinite_seq)
       ==> (x = Limit xs) = (xs convergeTo x)"
by (simp add: convergeTo_to_Limit)

lemma Limit_to_convergeTo_sym:
    "cauchy (xs::'a::cms infinite_seq)
       ==> (Limit xs = x) = (xs convergeTo x)"
apply (simp add: convergeTo_to_Limit)
by (fast)

lemmas Limit_iff = Limit_to_convergeTo Limit_to_convergeTo_sym

lemma Limit_is:
  "cauchy (xs::'a::cms infinite_seq) ==> xs convergeTo Limit xs"
by (simp add: convergeTo_to_Limit)

(********************************************************** 
                     Banach Theory
 **********************************************************)

(*** step 1 (cauchy) ***)

lemma Banach_lm_contraction:
  "[| contraction_alpha f alpha ; ALL i. xs (Suc i) = f(xs i) |]
    ==> distance(xs n, f(xs n)) <= alpha^n * distance(xs 0, f(xs 0))"
apply (induct_tac n)
apply (simp)
apply (simp)
apply (simp add: contraction_alpha_def map_alpha_def)
apply (elim conjE)
apply (drule_tac x="0" in spec)    (* for convenienec *)

apply (drule_tac x="xs n" in spec)
apply (drule_tac x="f (xs n)" in spec)

apply (subgoal_tac "alpha * distance (xs n, f (xs n))
                 <= alpha * (alpha ^ n * distance (xs 0, f (xs 0)))")
apply (simp)
apply (rule mult_left_mono)
by (simp_all)

lemma Banach_lm_triangle:
  "distance((xs::'a::cms infinite_seq) r, xs (r+n)) <= 
   prog_sum0 n (%m. distance(xs (r+m-(1::nat)), xs (r+m)))"
apply (induct_tac n)
apply (simp)

apply (simp)
apply (insert triangle_inequality_ms)
apply (drule_tac x="xs r" in spec)
apply (drule_tac x="xs (r + n)" in spec)
apply (drule_tac x="xs (Suc (r + n))" in spec)
apply (simp)
done

lemma Banach_lm_geo_prog_sum:
  "[| contraction_alpha f alpha ; (ALL i. xs (Suc i) = f(xs i)) |]
   ==>  prog_sum0 n (%m::nat. distance(xs (r+m-(1::nat)), xs (r+m)))
        <= prog_sum r (r+n) (geo_prop (distance(xs 0, xs 1)) alpha)"
apply (induct_tac n)
apply (simp add: prog_sum_def)

apply (simp add: prog_sum_def)
apply (subgoal_tac 
        "distance (xs (r + n), f (xs (r + n)))
      <= geo_prop (distance (xs 0, f (xs 0))) alpha (Suc (r + n))")
apply (simp)

apply (insert Banach_lm_contraction[of f alpha xs])
apply (simp add: geo_prop_def)
done

lemma Banach_lm_ineq:
  "[| contraction_alpha f alpha ; 
      (ALL i. (xs::'a::cms infinite_seq) (Suc i) = f(xs i)) |]
     ==> distance(xs r, xs (r+n)) <= 
         distance (xs 0, f(xs 0)) * alpha^r / (1-alpha)"
apply (insert Banach_lm_triangle[of xs r n])
apply (insert Banach_lm_geo_prog_sum[of f "alpha" xs n r])
apply (insert geo_prog_sum_infinite_div
       [of "distance (xs 0, xs 1)" "alpha" r "r+n"])
by (simp add: contraction_alpha_def map_alpha_def)

lemma Banach_lm_cauchy_lm_pos_distance:
  "[| contraction_alpha f alpha ;
      ALL i. (xs::'a::cms infinite_seq) (Suc i) = f(xs i) ; 
      0 < delta ; 0 < distance (xs 0, f(xs 0)) |]
    ==> (EX n. ALL m. distance (xs n, xs (n+m)) < delta)"
apply (insert pow_convergence[of 
       "alpha" "delta*(1-alpha)/distance (xs 0, f(xs 0))"])
apply (simp add: contraction_alpha_range)

(* for Isabelle 2013
apply (subgoal_tac "0 < delta * (1 - alpha) / distance (xs 0, f (xs 0))")
apply (simp)
*)

apply (elim conjE exE)
apply (rule_tac x="n" in exI)
apply (rule allI)

      (* give a subgoal to use transitivity *)
apply (subgoal_tac 
 "distance (xs n, xs (n + m))
  <= distance (xs 0, f (xs 0)) * alpha ^ n / (1 - alpha) &
     distance (xs 0, f (xs 0)) * alpha ^ n / (1 - alpha)
     < delta")
apply (erule conjE, simp)
apply (simp add: Banach_lm_ineq)
apply (simp_all add: real_mult_div_commute
                     contraction_alpha_def map_alpha_def)
      (* contraction_alpha_range did not work well here *)
(*
for Isabelle2007
apply (simp_all add: zero_le_power real_mult_div_commute
                     contraction_alpha_def map_alpha_def)
*)
done

lemma Banach_lm_cauchy_lm_zero_distance:
  "[| contraction_alpha f alpha ;
      ALL i. (xs::'a::cms infinite_seq) (Suc i) = f(xs i) ; 
      0 < delta ; distance (xs 0, f(xs 0)) = 0 |]
      ==> (EX n. ALL m. distance (xs n, xs (n+m)) < delta)"
apply (simp add: diagonal_ms)
apply (rule_tac x="0" in exI)
apply (rule allI)
apply (subgoal_tac "distance (xs 0, xs m) <= 0", simp)
by (insert Banach_lm_ineq[of f "alpha" "xs" 0], simp)

lemma Banach_lm_cauchy_lm:
  "[| contraction_alpha f alpha ;
      ALL i. (xs::'a::cms infinite_seq) (Suc i) = f(xs i) ; 0 < delta |]
    ==> (EX n. ALL m. distance (xs n, xs (n+m)) < delta)"
apply (case_tac "0 < distance (xs 0, f(xs 0))")
apply (simp add: Banach_lm_cauchy_lm_pos_distance)
apply (case_tac "distance (xs 0, f(xs 0)) = 0")
apply (simp add: Banach_lm_cauchy_lm_zero_distance)

apply (insert positive_ms)
apply (drule_tac x="xs 0" in spec)
apply (drule_tac x="f(xs 0)" in spec)
by (simp)

lemma Banach_lm_cauchy:
  "[| contraction_alpha f alpha ;
      ALL i. (xs::'a::cms infinite_seq) (Suc i) = f(xs i) |]
    ==> cauchy xs"
apply (simp add: cauchy_def)
apply (intro allI impI)

apply (subgoal_tac "EX n. ALL m. distance (xs n, xs (n + m)) < delta/2")
apply (erule exE)
apply (rule_tac x="n" in exI)
apply (intro allI impI)

apply (drule_tac x="0" in spec)     (* dummy *)
apply (frule_tac x="i-n" in spec)
apply (drule_tac x="j-n" in spec)
apply (simp)

apply (insert triangle_inequality_ms)
apply (drule_tac x="xs i" in spec)
apply (drule_tac x="xs n" in spec)
apply (drule_tac x="xs j" in spec)
apply (simp add: symmetry_ms)

apply (rule Banach_lm_cauchy_lm)
by (auto)

(*** step 2 (converge to a fixpoint) ***)

lemma Banach_lm_converge:
  "[| contraction_alpha f alpha ;
      ALL i. (xs::'a::cms infinite_seq) (Suc i) = f(xs i) |]
    ==> EX x. xs convergeTo x"
by (simp add: Banach_lm_cauchy complete_ms)

lemma Banach_lm_fixpoint_lm:
  "[| contraction_alpha f alpha ;
      ALL i. (xs::'a::cms infinite_seq) (Suc i) = f(xs i) ;
      xs convergeTo y ; 0 < eps |]
    ==> distance(y, f y) < eps"
apply (simp add: convergeTo_def)

apply (rotate_tac 2)
apply (drule_tac x="eps/2" in spec)
apply (simp)
apply (erule exE)
apply (rotate_tac -1)
apply (frule_tac x="n" in spec)
apply (drule_tac x="Suc n" in spec)
apply (simp)

apply (insert triangle_inequality_ms)
apply (drule_tac x="y" in spec)
apply (drule_tac x="xs (Suc n)" in spec)
apply (drule_tac x="f y" in spec)

apply (simp add: contraction_alpha_def map_alpha_def)
apply (elim conjE)

apply (rotate_tac -1)
apply (drule_tac x="xs n" in spec)
apply (drule_tac x="y" in spec)

apply (insert symmetry_ms)
apply (drule_tac x="xs n" in spec)
apply (drule_tac x="y" in spec)
apply (simp)

apply (subgoal_tac "alpha * distance (y, xs n) <= 1 * distance (y, xs n)")
apply (simp)

apply (rule mult_right_mono)
by (simp_all)

lemma Banach_lm_fixpoint:
  "[| contraction_alpha f alpha ;
      ALL i. (xs::'a::cms infinite_seq) (Suc i) = f(xs i) ;
      xs convergeTo y |]
    ==> y = f y"

apply (case_tac "0 < distance(y, f y)")
apply (insert Banach_lm_fixpoint_lm[of f alpha xs y "distance (y, f y)"])
apply (simp)

apply (case_tac "0 = distance(y, f y)")
apply (simp add: diagonal_ms)

(* distance(y, f y) < 0 *)
 apply (insert positive_ms)
 apply (drule_tac x="y" in spec)
 apply (drule_tac x="f y" in spec)
 apply (simp)
done

(*** step 3 (unique fixpoint) ***)

lemma Banach_lm_unique_lm:
  "[| contraction_alpha f alpha ;
      ALL i. (xs::'a::cms infinite_seq) (Suc i) = f(xs i) ;
      y = f y ; z = f z |] 
        ==> distance(y, z) <= alpha * distance(y, z)"
apply (simp add: contraction_alpha_def map_alpha_def)
apply (elim conjE)
apply (drule_tac x="y" in spec)
apply (drule_tac x="z" in spec)
apply (simp)
done

lemma Banach_lm_unique:
  "[| contraction_alpha f alpha ;
      ALL i. (xs::'a::cms infinite_seq) (Suc i) = f(xs i) ;
      y = f y ; z = f z |] 
        ==> y = z"
apply (case_tac "0 < distance(y, z)")
apply (insert Banach_lm_unique_lm[of f alpha xs y z])
apply (simp add: contraction_alpha_def)
apply (insert mult_less_cancel_right[of alpha "distance (y, z)" 1])
apply (simp)

apply (case_tac "0 = distance(y, z)")
apply (simp add: diagonal_ms)

(* distance(y, Z) < 0 *)
apply (simp add: less_le)
done

(*** final step (Banach Theory) ***)

(*------------------*
 |     Banach lm    |
 *------------------*)

theorem Banach_thm_xs:
  "[| contraction f ;
      ALL i. (xs::'a::cms infinite_seq) (Suc i) = f(xs i) |]
        ==> (EX y. (xs convergeTo y & y isUFP f))"
apply (simp add: contraction_def)
apply (erule exE)
apply (subgoal_tac "EX y. xs convergeTo y")
apply (erule exE)
apply (rule_tac x="y" in exI)
apply (simp)

apply (subgoal_tac "y = f y")
apply (simp add: isUFP_def)
apply (intro allI impI)
apply (rule Banach_lm_unique[of f _ xs])
apply (simp_all)

apply (simp add: Banach_lm_fixpoint)
apply (simp add: Banach_lm_converge)
done

(*-------------------*
 |      Banach       |
 *-------------------*)

theorem Banach_thm:
  "contraction (f::('a::cms => 'a))
     ==> f hasUFP & (%n. (f^^n) x0) convergeTo UFP f"
apply (subgoal_tac "f hasUFP", simp)
apply (insert Banach_thm_xs[of f "(%n. ((f^^n) x0))"])
apply (simp)
apply (elim conjE exE)

apply (insert UFP_is[of f], simp)
apply (subgoal_tac "y = UFP f", simp)
apply (simp add: UFP_unique)

apply (simp add: hasUFP_def)
apply (erule exE)
apply (rule_tac x="y" in exI, simp)
done

(*------------------*
 | Banach existency |
 *------------------*)

theorem Banach_thm_EX: "contraction (f::('a::cms => 'a)) ==> f hasUFP"
by (simp add: Banach_thm)

end
