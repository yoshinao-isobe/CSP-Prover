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
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2020         |
            |                  April 2020  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory RS
imports Norm_seq
begin

(*****************************************************************

         1. Definition of Restriction Spaces (RS)
         2. RS ==> MS
         3. Metric Fixed point induction
         4. 

 *****************************************************************)


(*
  It was defined by ("_ .|. _" [55,56] 55) until Isabelle 2007, 
  but it was changed because it caused many syntactic ambiguity 
  in Isabelle 2008.
*)


(******** X-symbols ********)
(*
notation (xsymbols) restriction ("_ \<down> _" [84,900] 84)

Isabelle 2005
syntax (output)
  "_restriction" :: "'a::ms0 => nat => 'a::ms0"  ("_ .|. _" [55,56] 55)

syntax (xsymbols)
  "_restriction" :: "'a::ms0 => nat => 'a::ms0"  ("_ \<down> _" [55,56] 55)

translations
  "x \<down> n"  == "x .|. n"
*)

(********************************************************** 
                  restriction space (rs)
 **********************************************************)

(* isabelle2009-1
consts 
  restriction :: "'a::ms0 => nat => 'a::ms0"  ("_ .|. _" [84,900] 84)

axclass rs < ms0
  zero_eq_rs: "ALL (x::'a::ms0) (y::'a::ms0). x .|. 0 = y .|. 0"
  min_rs    : "ALL (x::'a::ms0) (m::nat) (n::nat). 
                     (x .|. m) .|. n = x .|. (min m n)"
  diff_rs   : "ALL (x::'a::ms0) (y::'a::ms0).
                     (x ~= y) --> (EX n. x .|. n ~= y .|. n)"
*)

class rs0 = 
fixes restriction :: "'a => nat => 'a"  ("_ .|. _" [84,900] 84)


(* class rs = rs0 + ms0 + *)

class rs = rs0 + 
assumes
  zero_eq_rs: "ALL x y. x .|. 0 = y .|. 0"
assumes
  min_rs    : "ALL x m n.
                     (x .|. m) .|. n = x .|. (min m n)"
assumes
  diff_rs   : "ALL x y.
                     (x ~= y) --> (EX n. x .|. n ~= y .|. n)"


declare zero_eq_rs [simp]

lemma diff_rs_Suc:
  "ALL n (x::'a::rs) y. x .|. n ~= y .|. n --> (EX m. n = Suc m) "
apply (rule allI)
apply (induct_tac n)
by (auto)

(********************************************************** 
            restriction space --> metric space
 **********************************************************)

definition
  distance_nat_set :: "('a::rs * 'a::rs) => nat set"
  where
  distance_nat_set_def :
     "distance_nat_set xy == 
      {n. ((fst xy) .|. n) = ((snd xy) .|. n)}"
  
definition  
  distance_nat     :: "('a::rs * 'a::rs) => nat"
  where
  distance_nat_def :
     "distance_nat xy == Max (distance_nat_set xy)"
  
definition
  distance_rs_set  :: "('a::rs * 'a::rs) => real set"
  where
  distance_rs_set_def :
     "distance_rs_set xy == {(1/2)^n |n. n:distance_nat_set xy}"

(*
defs (overloaded)
  distance_rs_def : "distance xy == GLB (distance_rs_set xy)"
*)

definition
  distance_rs :: "('a::rs * 'a::rs) => real"
  where
  distance_rs_def: "distance_rs xy == GLB (distance_rs_set xy)"


(********************************************************** 
             complete restriction space (crs)
 **********************************************************)

class ms0_rs =  ms0 + rs +
assumes 
  to_distance_rs: "distance (xy::('a::{ms0,rs}) * 'a) = distance_rs xy"

class ms_rs =  ms + ms0_rs
class cms_rs = cms + ms_rs

(********************************************************** 
                        RS lemmas 
 **********************************************************)

(*** contraposition of diff_rs ***)

lemma contra_diff_rs: 
    "[| ALL n. (x::'a::rs) .|. n = y .|. n |] ==> (x = y)"
apply (erule contrapos_pp)
by (simp add: diff_rs)

(*** diff_rs inv ***)

lemma contra_diff_rs_inv: 
    "[| (x::'a::rs) .|. n ~= y .|. n |] ==> (x ~= y)"
apply (auto)
done

(*** zero distance ***)

lemma distance_rs_zero[simp]: 
  "distance_rs ((x::'a::rs), x) = 0"
apply (simp add: distance_rs_def distance_rs_set_def)
apply (simp add: distance_nat_set_def)
by (simp add: zero_GLB_pow)

(*---------------------------*
 |       equal-preserv       |
 *---------------------------*)

lemma rest_equal_preserve:
  "[| (x::'a::rs) .|. n = y .|. n ; m <= n |] ==> x .|. m = y .|. m"
apply (insert min_rs)
apply (drule_tac x="x" in spec)
apply (drule_tac x="n" in spec)
apply (drule_tac x="m" in spec)
apply (insert min_rs)
apply (drule_tac x="y" in spec)
apply (drule_tac x="n" in spec)
apply (drule_tac x="m" in spec)
by (simp add: min_is)

lemma rest_equal_preserve_Suc:
  "(x::'a::rs) .|. Suc n = y .|. Suc n ==> x .|. n = y .|. n"
apply (rule rest_equal_preserve)
by (auto)

lemma rest_nonequal_preserve:
  "[| (x::'a::rs) .|. m ~= y .|. m ; m <= n |] ==> x .|. n ~= y .|. n"
apply (erule contrapos_pp)
apply (simp)
apply (rule rest_equal_preserve)
by (simp_all)

(*---------------------------*
 |  distance_nat_set hasMAX  |
 *---------------------------*)

lemma distance_nat_set_hasMAX :
  "(x::'a::rs) ~= y ==> (distance_nat_set (x,y)) hasMAX"
apply (insert EX_MIN_nat[of "{m. x .|. m ~= y .|. m}"])
apply (simp add: diff_rs)
apply (erule exE)
apply (simp add: isMIN_def)

apply (insert diff_rs_Suc)
apply (drule_tac x="n" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (simp)
apply (erule exE)

 (* m must be the max *)

apply (simp add: hasMAX_def)
apply (rule_tac x="m" in exI)
apply (simp add: distance_nat_set_def isMAX_def)

apply (case_tac "x .|. m = y .|. m")
 apply (simp add: isUB_def)
 apply (intro allI impI)

 apply (simp add: isLB_def)
 apply (erule conjE)
 apply (case_tac "Suc m <= ya")
 apply (rotate_tac 3)
 apply (erule contrapos_pp)

 apply (rule rest_nonequal_preserve)
 apply (simp_all)
 apply (force)

      (* x .|. m ~= y .|. m *)  (* --> contradict for MIN *)
 apply (simp add: isLB_def)
 apply (erule conjE)
 apply (drule_tac x="m" in spec)
 apply (simp)
done

(*---------------------------*
 |     isMAX <--> isGLB      |
 *---------------------------*)

lemma to_distance_rsMAX_isGLB:
 "n isMAX distance_nat_set ((x::'a::rs), y)
  ==> (1/2)^n isGLB distance_rs_set (x, y)"
apply (simp add: distance_rs_set_def)
apply (simp add: isGLB_def isLB_def)
apply (rule conjI)

 (* LB *)
 apply (intro allI impI)
 apply (simp add: isMAX_def isUB_def)
 apply (elim conjE exE)
 apply (drule_tac x="na" in spec)
 apply (simp add: power_decreasing)

 (* GLB *)
 apply (intro allI impI)
 apply (drule_tac x="(1 / 2) ^ n" in spec)
 apply (drule mp)
 apply (rule_tac x="n" in exI, simp_all)
 apply (simp add: isMAX_def)
done

(*---------------------------*
 |    distance_set hasGLB    |
 *---------------------------*)

lemma distance_rs_set_hasGLB :
  "(distance_rs_set ((x::'a::rs),y)) hasGLB"
apply (simp add: hasGLB_def)

apply (case_tac "x = y")
apply (simp add: distance_rs_set_def)
apply (simp add: distance_nat_set_def)
apply (rule_tac x="0" in exI)
apply (simp add: zero_isGLB_pow)

apply (insert distance_nat_set_hasMAX[of x y])
apply (simp add: hasMAX_def)
apply (erule exE)
apply (rule_tac x="(1/2)^xa" in exI)
by (simp add: to_distance_rsMAX_isGLB)

(*---------------------------*
 |       MAX <--> GLB        |
 *---------------------------*)

lemma distance_rs_nat_lm:
  "[| (x::'a::rs) ~= y ; distance_nat (x,y) = n ; distance_rs (x,y) = r |]
   ==> r = (1 / 2) ^ n"
apply (simp add: distance_nat_def MAX_iff distance_nat_set_hasMAX)
apply (simp add: distance_rs_def  GLB_iff distance_rs_set_hasGLB)
apply (insert to_distance_rsMAX_isGLB[of n x y])
by (simp add: GLB_unique)

lemma distance_iff1:
  "(x::'a::rs) ~= y
   ==> distance_rs (x,y) = (1 / 2) ^ (distance_nat (x,y))"
by (simp add: distance_rs_nat_lm)

lemma distance_iff2:
  "(y::'a::rs) ~= x
   ==> distance_rs (x,y) = (1 / 2) ^ (distance_nat (x,y))"
apply (rule distance_iff1)
by (force)

lemmas distance_iff = distance_iff1 distance_iff2

(*---------------------------*
 |       less than 1B        |
 *---------------------------*)

lemma distance_rs_less_one: 
  "distance_rs ((x::'a::rs), y) <= 1"
apply (case_tac "x=y", simp)
apply (simp add: distance_iff)
apply (rule order_trans)
apply (subgoal_tac "(1 / 2) ^ distance_nat (x, y) <= (1 / 2) ^ 0")
apply (assumption)
apply (rule power_decreasing)
apply (simp_all)
done

(*---------------------------*
 |      distance_nat iff     |
 *---------------------------*)

lemma isMAX_distance_nat1 : 
  "(x::'a::rs) ~= y ==> (n isMAX distance_nat_set (x,y)) = (distance_nat (x,y) = n)"
apply (simp add: distance_nat_def)
by (simp add: distance_nat_set_hasMAX MAX_iff)

lemmas distance_nat_isMAX1 = isMAX_distance_nat1[THEN sym]

lemma distance_nat_isMAX_sym1:
  "(x::'a::rs) ~= y ==> (n = distance_nat (x,y)) = (n isMAX distance_nat_set (x,y))"
by (auto simp add: isMAX_distance_nat1)

lemma isMAX_distance_nat2 :
  "(y::'a::rs) ~= x ==> (n isMAX distance_nat_set (x,y)) = (distance_nat (x,y) = n)"
apply (rule isMAX_distance_nat1)
by (auto)

lemmas distance_nat_isMAX2 = isMAX_distance_nat2[THEN sym]

lemma distance_nat_isMAX_sym2:
  "(y::'a::rs) ~= x ==> (n = distance_nat (x,y)) = (n isMAX distance_nat_set (x,y))"
by (auto simp add: isMAX_distance_nat2)

lemmas distance_nat_iff = distance_nat_isMAX1 distance_nat_isMAX_sym1
                          distance_nat_isMAX2 distance_nat_isMAX_sym2

(*** for insert ***)

lemma distance_nat_is:
  "(x::'a::rs) ~= y ==> distance_nat (x,y) isMAX distance_nat_set (x,y)"
apply (insert distance_nat_isMAX1[of x y "distance_nat (x,y)"])
by (simp)

(*============================================================*
 |                                                            |
 |         (restriction space ==> metric space)               |
 |                                                            |
 |    instance x :: (type) rs ==> instance x :: (type) ms     |
 |                                                            |
 |               by  positive_rs                              |
 |                   diagonal_rs                              |
 |                   symmetry_rs                              |
 |                   triangle_inequality_rs                   |
 |                                                            |
 *============================================================*)

(*** positive_rs ***)

lemma positive_rs[simp]: "0 <= distance_rs (x::'a::rs,y)"
apply (case_tac "x = y")
by (simp_all add: distance_iff)
(*
in Isabelle2007
by (simp_all add: distance_iff zero_le_power)
*)

(*** diagonal_rs ***)

lemma diagonal_rs_only_if: "(distance_rs((x::'a::rs),y) = 0) ==> (x = y)"
apply (case_tac "x = y", simp)
by (simp add: distance_iff)

lemma diagonal_rs: "(distance_rs((x::'a::rs),y) = 0) = (x = y)"
apply (rule iffI)
apply (simp add: diagonal_rs_only_if)
by (simp)

lemma diagonal_rs_neq: "((x::'a::rs) ~= y) ==> 0 < distance_rs((x::'a::rs), y)"
apply (case_tac "distance_rs(x, y) = 0")
apply (simp add: diagonal_rs)
apply (insert positive_rs[of x y])
apply (simp (no_asm_simp))
done

(*** symmetry_rs ***)

lemma symmetry_nat_lm: 
  "[| (x::'a::rs) ~= y; 
      distance_nat (x,y) = n; distance_nat (y,x) = m |] ==> n = m"
apply (simp add: distance_nat_iff)
apply (rule MAX_unique)
apply (simp)
by (simp add: isMAX_def isUB_def distance_nat_set_def)

lemma symmetry_nat: 
  "(x::'a::rs) ~= y ==> distance_nat (x,y) = distance_nat (y,x)"
by (simp add: symmetry_nat_lm)

lemma symmetry_rs: "distance_rs((x::'a::rs),y) = distance_rs(y,x)"
apply (case_tac "x = y", simp)
apply (simp add: distance_iff)
by (insert symmetry_nat[of x y], simp)

(*** triangle_inequality_rs ***)

lemma triangle_inequality_nat_lm:
  "[| (x::'a::rs) ~= y ; y ~= z ; x ~= z ;
      distance_nat (x,z) = n1 ;
      distance_nat (x,y) = n2 ;
      distance_nat (y,z) = n3 |]
   ==> min n2 n3 <= n1"
apply (simp add: distance_nat_iff)
apply (simp add: distance_nat_set_def)
apply (simp add: isMAX_def)

apply (subgoal_tac "min n3 n2 = min n2 n3")
apply (subgoal_tac "x .|. min n2 n3 = z .|. min n3 n2")
apply (simp add: isUB_def)

(* FOR x .|. min n2 n3 = z .|. min n3 n2 *)

apply (insert min_rs)
apply (frule_tac x="x" in spec)
apply (frule_tac x="y" in spec)
apply (frule_tac x="y" in spec)
apply (drule_tac x="z" in spec)

apply (drule_tac x="n2" in spec)
apply (drule_tac x="n2" in spec)
apply (drule_tac x="n3" in spec)
apply (drule_tac x="n3" in spec)

apply (drule_tac x="n3" in spec)
apply (drule_tac x="n3" in spec)
apply (drule_tac x="n2" in spec)
apply (drule_tac x="n2" in spec)
apply (simp)

by (simp add: min_def)

lemma triangle_inequality_nat:
  "[| (x::'a::rs) ~= y ; y ~= z ; x ~= z |]
   ==> min (distance_nat (x,y)) (distance_nat (y,z)) <= distance_nat (x,z)"
by (simp add: triangle_inequality_nat_lm)

lemma triangle_inequality_neq:
  "[| (x::'a::rs) ~= y ; y ~= z ; x ~= z |]
   ==> distance_rs (x,z) <= max (distance_rs (x,y)) (distance_rs (y,z))"
apply (simp add: distance_iff)
apply (insert triangle_inequality_nat[of x y z], simp)

apply (case_tac "distance_nat (x, y) <= distance_nat (y, z)")
 apply (simp add: min_is)
 apply (subgoal_tac "((1::real) / 2) ^ distance_nat (y, z) 
                  <= (1 / 2) ^ distance_nat (x, y)") 
 apply (simp add: max_is)
 apply (simp) (* modified for Isabelle2020 *)

 (* ~ distance_nat (x, y) <= distance_nat (y, z) *)
 apply (simp add: min_is)
 apply (subgoal_tac "((1::real) / 2) ^ distance_nat (x, y) 
                  <= (1 / 2) ^ distance_nat (y, z)") 
 apply (simp add: max_is)
 apply (simp) (* modified for Isabelle2020 *)
done

lemma triangle_inequality_max:
  "distance_rs ((x::'a::rs),z) <= max (distance_rs (x,y)) (distance_rs (y,z))"
apply (case_tac "x = y", simp add: max_is)
apply (case_tac "y = z", simp add: max_is)
apply (case_tac "x = z", simp add: max_def)
by (simp add: triangle_inequality_neq)

(*** triangle_inequality ***)

lemma triangle_inequality_rs:
  "distance_rs ((x::'a::rs),z) <= distance_rs (x,y) + distance_rs (y,z)"

apply (insert triangle_inequality_max[of x z y])
apply (subgoal_tac "max (distance_rs (x, y)) (distance_rs (y, z)) 
                      <= distance_rs (x, y) + distance_rs (y, z)")
apply (blast intro: order_trans)
by (simp)

(********************************************************** 
                 .|. <--> distance_nat
 **********************************************************)

(*---------------------------*
 |  distance_nat satisfies   |
 *---------------------------*)

lemma distance_nat_rest:
  "[| (x::'a::rs) ~= y ; distance_nat (x, y) = n |]
    ==> x .|. n = y .|. n"
apply (simp add: distance_nat_iff)
apply (simp add: isMAX_def)
by (simp add: distance_nat_set_def)

(*---------------------------*
 |    distance_nat is max    |
 *---------------------------*)

lemma distance_nat_rest_Suc:
  "[| (x::'a::rs) ~= y ; distance_nat (x, y) = n |]
    ==> x .|. (Suc n) ~= y .|. (Suc n)"
apply (simp add: distance_nat_iff)
apply (simp add: isMAX_def isUB_def)
apply (simp add: distance_nat_set_def)
apply (case_tac "x .|. Suc n ~= 
                 y .|. Suc n", simp)
apply (erule conjE)
apply (drule_tac x="Suc n" in spec)
by (simp)

(*---------------------------*
 |     distance_nat_le       |
 *---------------------------*)

(* 1 only if *)

lemma distance_nat_le_1_only_if:
  "[| (x::'a::rs) ~= y ; x .|. n = y .|. n |] ==> n <= distance_nat (x,y)"
apply (insert distance_nat_is[of x y])
apply (simp add: isMAX_def isUB_def)
apply (erule conjE)
apply (drule_tac x="n" in spec)
apply (drule mp)

apply (simp add: distance_nat_set_def)
by (simp)

(* 1 if *)

lemma distance_nat_le_1_if:
  "[| (x::'a::rs) ~= y ; n <= distance_nat (x,y) |] ==> x .|. n = y .|. n"
apply (insert distance_nat_is[of x y])
apply (simp add: isMAX_def isUB_def)
apply (erule conjE)
apply (simp add: distance_nat_set_def)
apply (rule rest_equal_preserve)
by (simp_all)

(* 1 iff *)

lemma distance_nat_le_1:
  "(x::'a::rs) ~= y ==> (x .|. n = y .|. n) = (n <= distance_nat (x,y))"
apply (rule iffI)
apply (simp add: distance_nat_le_1_only_if)
apply (simp add: distance_nat_le_1_if)
done

(* 2 iff *)

lemma distance_nat_le_2:
  "(x::'a::rs) ~= y 
   ==> (x .|. n ~= y .|. n) = (distance_nat (x,y) < n)"
by (auto simp add: distance_nat_le_1)

(*---------------------------*
 |    distance_nat_less      |
 *---------------------------*)

(* 1 only if *)

lemma distance_nat_less_1_only_if:
  "(x::'a::rs) ~= y 
   ==> (x::'a::rs) .|. (Suc n) = y .|. (Suc n) ==> n < distance_nat (x,y)"
by (simp add: distance_nat_le_1)

(* 1 if *)

lemma distance_nat_less_1_if:
  "(x::'a::rs) ~= y 
   ==> n < distance_nat (x,y) ==> x .|. (Suc n) = y .|. (Suc n)"
apply (insert distance_nat_is[of x y], simp)
apply (simp add: isMAX_def distance_nat_set_def)
apply (rule rest_equal_preserve[of x "distance_nat (x, y)" y "Suc n"])
by (simp_all)

(* 1 iff *)

lemma distance_nat_less_1:
  "(x::'a::rs) ~= y 
   ==> (x .|. (Suc n) = y .|. (Suc n)) = (n < distance_nat (x,y)) "
apply (intro allI iffI)
apply (simp add: distance_nat_less_1_only_if)
apply (simp add: distance_nat_less_1_if)
done

(* 2 iff *)

lemma distance_nat_less_2:
  "(x::'a::rs) ~= y 
   ==> (x .|. (Suc n) ~= y .|. (Suc n)) = (distance_nat (x,y) <= n)"
by (auto simp add: distance_nat_less_1)

(********************************************************** 
                   .|. <--> distance
 **********************************************************)

(*---------------------------*
 |      distance_rs_le       |
 *---------------------------*)

(* 1 only if *)

lemma distance_rs_le_1_only_if:
  "(x::'a::rs) .|. n = y .|. n ==> distance_rs(x,y) <= (1/2)^n"
(*
Isabelle 2007
apply (case_tac "x = y", simp add: zero_le_power)
*)
apply (case_tac "x = y", simp)
apply (simp add: distance_iff)
apply (simp add: distance_nat_le_1)
done 

(* 1 if *)

lemma distance_rs_le_1_if:
  "distance_rs((x::'a::rs),y) <= (1/2)^n ==> x .|. n = y .|. n"
apply (case_tac "x = y", simp)
apply (simp add: distance_iff)
apply (simp add: distance_nat_le_1)
done

(* 1 iff *)

lemma distance_rs_le_1:
  "((x::'a::rs) .|. n = y .|. n) = (distance_rs(x,y) <= (1/2)^n)"
apply (rule iffI)
apply (simp add: distance_rs_le_1_only_if)
apply (simp add: distance_rs_le_1_if)
done

(* 2 iff *)

lemma distance_rs_le_2:
  "((x::'a::rs) .|. n ~= y .|. n) = ((1/2)^n < distance_rs(x,y))"
by (auto simp add: distance_rs_le_1)

(*****************************
       distance_rs_less
 *****************************)

(* 1 only if *)

lemma distance_rs_less_1_only_if:
  "(x::'a::rs) .|. (Suc n) = y .|. (Suc n) ==> distance_rs(x,y) < (1/2)^n"
apply (case_tac "x = y", simp)
apply (simp add: distance_rs_le_1)
apply (subgoal_tac "distance_rs (x, y) < distance_rs (x, y) * 2")
apply (simp)
apply (simp)
by (simp add: diagonal_rs_neq)

(* 1 if *)

lemma distance_rs_less_1_if:
  "distance_rs((x::'a::rs),y) < (1/2)^n ==> x .|. (Suc n) = y .|. (Suc n)"
apply (case_tac "x = y", simp)
apply (simp add: distance_iff)
apply (simp add: distance_nat_less_1)  (* modified for Isabelle2020 *)
done

(* 1 iff *)

lemma distance_rs_less_1:
  "((x::'a::rs) .|. (Suc n) = y .|. (Suc n)) = (distance_rs(x,y) < (1/2)^n)"
apply (intro allI iffI)
apply (simp add: distance_rs_less_1_only_if)
apply (simp add: distance_rs_less_1_if)
done

(* 2 iff *)

lemma distance_rs_less_2:
  "((x::'a::rs) .|. (Suc n) ~= y .|. (Suc n)) = ((1/2)^n <= distance_rs(x,y))"
by (auto simp add: distance_rs_less_1)

(*********************************************************************
                   for constructiveness of prefix
 *********************************************************************)

lemma contra_diff_rs_Suc:
      "[| ALL n. (x::'a::rs) .|. (Suc n) = y .|. (Suc n) |] ==> (x = y)"
apply (erule contrapos_pp)
apply (simp)
apply (insert diff_rs)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (simp)
apply (erule exE)
apply (rule_tac x="n" in exI)

apply (rule rest_nonequal_preserve)
by (auto)

(*---------------------------*
 |    for contractiveness    |
 *---------------------------*)

lemma rest_Suc_dist_half:
  "[| ALL n. ((x1::'a::rs) .|. n = x2 .|. n) =
             ((y1::'a::rs) .|. (Suc n) = y2 .|. (Suc n)) |]
   ==> (1/2) * distance_rs(x1,x2) = distance_rs(y1,y2)"

apply (case_tac "x1 = x2")
 apply (simp)
 apply (subgoal_tac "y1 = y2")  (* ...1 *)
 apply (simp)

 (* 1 *)
 apply (rule contra_diff_rs_Suc, simp)

 (* x1 ~= x2 *)
  apply (case_tac "y1 = y2", simp)
  apply (rotate_tac 1)
  apply (erule contrapos_np)
  apply (rule contra_diff_rs, simp)

 (* x1 ~= x2 & y1 ~= y2 *)
 apply (simp add: distance_iff)

 apply (subgoal_tac 
        "distance_nat (y1, y2) = Suc (distance_nat (x1, x2))") (* ... 2 *)
 apply (simp)
 apply (rule order_antisym)

  (* <= *)
  apply (insert nat_zero_or_Suc)
  apply (rotate_tac -1)
  apply (drule_tac x="distance_nat (y1, y2)" in spec)
  apply (erule disjE, simp)
  apply (erule exE, simp)

  apply (simp add: distance_nat_le_1)

  (* => *)
  apply (simp add: distance_nat_le_1)
  apply (drule_tac x="distance_nat (x1, x2)" in spec)
  apply (simp)
done

(*********************************************************************
                  rest_to_dist_pair (fun and pair)
 *********************************************************************)

lemma rest_to_dist_pair:
  "[| xps ~= {} ;
      (ALL n. (ALL x:(xps::(('a::rs) * ('a::rs)) set). 
      (fst x) .|. n = (snd x) .|. n) --> ((y1::'b::rs) .|. n = y2 .|. n)) |]
   ==> (EX x. x:xps & distance_rs(y1,y2) <= distance_rs((fst x), (snd x)))"
apply (case_tac "y1 = y2", force)
      (* y1 ~= y2 *)
apply (insert distance_nat_is[of y1 y2], simp)

apply (simp add: distance_iff)
apply (drule_tac x="Suc (distance_nat (y1, y2))" in spec)
apply (simp add: distance_nat_rest_Suc)
apply (erule bexE)
apply (rule_tac x="fst x" in exI)
apply (rule_tac x="snd x" in exI)
apply (simp add: distance_rs_less_2)
done

(*** two sets (e.g. for domT and domF) ***)

lemma rest_to_dist_pair_two:
  "[| xps ~= {} ; yps ~= {} ;
      (ALL n. 
       (ALL x:(xps::(('a::rs) * ('a::rs)) set). (fst x) .|. n = (snd x) .|. n) &
       (ALL y:(yps::(('b::rs) * ('b::rs)) set). (fst y) .|. n = (snd y) .|. n)
       --> ((z1::'c::rs) .|. n = z2 .|. n)) |]
   ==> (EX x. x:xps & distance_rs(z1,z2) <= distance_rs((fst x), (snd x))) |
       (EX y. y:yps & distance_rs(z1,z2) <= distance_rs((fst y), (snd y)))"
apply (case_tac "z1 = z2", force)
      (* z1 ~= z2 *)
apply (insert distance_nat_is[of z1 z2], simp)

apply (simp add: distance_iff)
apply (drule_tac x="Suc (distance_nat (z1, z2))" in spec)
apply (simp add: distance_nat_rest_Suc)
apply (elim bexE disjE)

 apply (rule disjI1)
 apply (rule_tac x="fst x" in exI)
 apply (rule_tac x="snd x" in exI)
 apply (simp add: distance_rs_less_2)

 apply (rule disjI2)
 apply (rule_tac x="fst y" in exI)
 apply (rule_tac x="snd y" in exI)
 apply (simp add: distance_rs_less_2)
done

(************************************************************
           .|. <--> distance lemma (different types)
 ************************************************************)

(*** subset ***)

lemma rest_distance_subset:
  "[| ALL n. ((x::'a::rs) .|. n = y .|. n) --> ((X::'b::rs) .|. n = Y .|. n) |]
   ==> distance_rs(X, Y) <= distance_rs(x, y)"
apply (case_tac "X = Y", simp)
apply (case_tac "x = y", simp)
apply (insert contra_diff_rs[of X Y], simp)  (* contradiction *)

      (* x ~= y & X ~= Y *)
apply (simp add: distance_rs_le_1)
apply (simp add: distance_iff)
done

(*** eq ***)

lemma rest_distance_eq:
  "[| ALL n. ((x::'a::rs) .|. n = y .|. n) = ((X::'b::rs) .|. n = Y .|. n) |]
   ==> distance_rs(x, y) = distance_rs(X, Y)"
apply (rule order_antisym)
by (simp_all add: rest_distance_subset)


(*----------------------------------------------------------*
 |                                                          |
 |                  distance = distance_rs                   |
 |                                                          |
 *----------------------------------------------------------*)


(*********************************************************************
                             Limit (ms_rs)
 *********************************************************************)

(*---------------------------*
 |  mini_number_cauchy_rest  |
 *---------------------------*)

lemma mini_number_cauchy_rest:
  "[| ALL (xy::('a::ms_rs * 'a::ms_rs)). distance xy = distance_rs xy ;
      normal (xs::'a::ms_rs infinite_seq) |]
   ==> (ALL n m. k <= n & k <= m --> (xs n) .|. k = (xs m) .|. k)"
apply (intro allI impI)
apply (simp add: normal_def)
apply (drule_tac x="n" in spec)
apply (drule_tac x="m" in spec)

apply (simp add: distance_rs_le_1)
apply (subgoal_tac "((1::real) / 2) ^ min n m <= (1 / 2) ^ k")
apply (simp (no_asm_simp))  (* modified for Isabelle2020 *)
apply (simp)
done

(*---------------------------*
 |        rest_Limit         |
 *---------------------------*)

lemma rest_Limit:
  "[| ALL (xy::('a::ms_rs * 'a::ms_rs)). distance xy = distance_rs xy ;
      ALL n. y .|. n = (xs n) .|. n |]
   ==> (xs::'a::ms_rs infinite_seq) convergeTo y"
apply (simp add: convergeTo_def)
apply (intro allI impI)

apply (subgoal_tac "EX n. ((1::real) / 2) ^ n < eps")  (* ... 1 *)
apply (erule exE)
apply (rule_tac x="n" in exI)
apply (intro allI impI)
apply (rename_tac eps N n)

apply (drule_tac x="n" in spec)
apply (simp add: distance_rs_le_1)

apply (subgoal_tac "((1::real) / 2) ^ n <= (1 / 2) ^ N")  (* ... 2 *)
apply (simp (no_asm_simp))  (* modified for Isabelle2020 *)

(* 2 *)
apply (simp)

(* 1 *)
apply (simp add: pow_convergence)
done


(*----------------------------------------------------------*
 |                                                          |
 |              Metric Fixed point induction                |
 |                                                          |
 |               constructive & continuous                  |
 |                                                          |
 *----------------------------------------------------------*)

definition
  constructive_rs :: "('a::ms_rs => 'b::ms_rs) => bool"
  where
  constructive_rs_def :
     "constructive_rs f == 
        (ALL x y n. x .|. n = y .|. n 
                    --> (f x) .|. (Suc n) = (f y) .|. (Suc n))"
definition  
  continuous_rs   :: "('a::ms_rs => bool) => bool"
  where
  continuous_rs_def :
     "continuous_rs R ==
          (ALL x. ~ R x --> (EX n. ALL y. y .|. n = x .|. n --> ~ R y))"

(********************************************************** 
              Construction --> Contraction
 **********************************************************)

lemma contst_to_contra_alpha:
  "[| ALL (xy::('a::ms_rs * 'a::ms_rs)). distance xy = distance_rs xy ;
      ALL (xy::('b::ms_rs * 'b::ms_rs)). distance xy = distance_rs xy ;
      constructive_rs (f::('a::ms_rs => 'b::ms_rs)) |]
   ==> contraction_alpha f (1/2)"
apply (simp add: contraction_alpha_def map_alpha_def)
apply (intro allI)

apply (case_tac "x=y", simp)
apply (case_tac "f x = f y", simp)

apply (simp add: distance_iff)
apply (simp add: constructive_rs_def)

apply (rotate_tac 1)
apply (drule_tac x="x" in spec)
apply (rotate_tac -1)
apply (drule_tac x="y" in spec)
apply (simp add: distance_nat_le_1)
apply (drule_tac x="distance_nat (x, y)" in spec)
apply (simp)

apply (subgoal_tac 
      "((1::real)/2) ^ distance_nat (f x, f y) 
    <= ((1::real)/2) ^ (Suc (distance_nat (x, y)))")  (* ... 1 *)
apply (simp)

      (* 1 *)
apply (rule power_decreasing)
by (simp_all)

(*** contractive ***)

lemma contst_to_contra: 
  "[| ALL (xy::('a::ms_rs * 'a::ms_rs)). distance xy = distance_rs xy ;
      ALL (xy::('b::ms_rs * 'b::ms_rs)). distance xy = distance_rs xy ;
      constructive_rs (f::('a::ms_rs => 'b::ms_rs)) |]
   ==> contraction f"
apply (simp add: contraction_def)
apply (rule_tac x="1/2" in exI)
apply (simp add: contst_to_contra_alpha)
done

(********************************************************** 
              Construction --> Contraction
 **********************************************************)

lemma contra_alpha_to_contst:
  "[| ALL (xy::('a::ms_rs * 'a::ms_rs)). distance xy = distance_rs xy ;
      ALL (xy::('b::ms_rs * 'b::ms_rs)). distance xy = distance_rs xy ;
     contraction_alpha (f::('a::ms_rs => 'b::ms_rs)) (1/2) |]
   ==> constructive_rs f"
apply (simp add: constructive_rs_def)
apply (intro allI impI)

apply (simp add: contraction_alpha_def map_alpha_def)
apply (rotate_tac 2)
apply (drule_tac x="x" in spec)
apply (rotate_tac -1)
apply (drule_tac x="y" in spec)

by (simp add: distance_rs_le_1)

(*========================================================*
 |            Metric Fixed Point Induction                |
 *========================================================*)

theorem cms_fixpoint_induction:
  "[| ALL (xy::('a::cms_rs * 'a::cms_rs)). distance xy = distance_rs xy ;
      ALL (xy::('b::ms_rs * 'b::ms_rs)). distance xy = distance_rs xy ;
      (R::'a::cms_rs => bool) x ; continuous_rs R ;
      constructive_rs f ; inductivefun R f |]
   ==> f hasUFP & R (UFP f)"
apply (insert Banach_thm[of f x])
apply (simp add: contst_to_contra)
apply (erule conjE)

      (* to use a contradiction *)
apply (case_tac "R (UFP f)", simp)

apply (simp add: continuous_rs_def)
apply (drule_tac x="UFP f" in spec, simp)
apply (erule exE)

apply (simp add: convergeTo_def)
apply (drule_tac x="(1/2)^n" in spec, simp)
apply (elim conjE exE)
apply (drule_tac x="na" in spec, simp)
apply (simp add: distance_rs_less_1[THEN sym])

apply (rotate_tac -2)
apply (drule_tac x="(f ^^ na) x" in spec)      (* isabelle 2009-1 *)
apply (drule mp)
apply (rule rest_equal_preserve_Suc, simp)

by (simp add: inductivefun_all_n)


theorem cms_fixpoint_induction_imp:
  "((ALL (xy::('a::cms_rs * 'a::cms_rs)). distance xy = distance_rs xy) &
    (ALL (xy::('b::ms_rs * 'b::ms_rs)). distance xy = distance_rs xy) &
    (R::'a::cms_rs => bool) x & continuous_rs R &
      constructive_rs f & inductivefun R f)
   --> f hasUFP & R (UFP f)"
by (auto simp add: cms_fixpoint_induction)

theorem cms_fixpoint_induction_R:
  "[| ALL (xy::('a::cms_rs * 'a::cms_rs)). distance xy = distance_rs xy ;
      ALL (xy::('b::ms_rs * 'b::ms_rs)). distance xy = distance_rs xy ;
     (R::'a::cms_rs => bool) x ; continuous_rs R ;
      constructive_rs f ; inductivefun R f |]
   ==> R (UFP f)"
by (simp add: cms_fixpoint_induction)


(*----------------------------------------------------------*
 |                                                          |
 |      !!!     order and restriction space     !!!         |
 |                                                          |
 *----------------------------------------------------------*)

class ms_rs_order0 = ms_rs + order

class ms_rs_order = ms_rs_order0 +
assumes  rs_order_iff: 
    "ALL (x::'a::ms_rs_order0) y.
        (ALL n. x .|. n <= y .|. n) = (x <= y)"

(* class ms_rs_order = ms + rs_order *)

class cms_rs_order = cms_rs + ms_rs_order

lemma not_rs_orderI:
 "~ x .|. n <= y .|. n ==> ~ ((x::'a::ms_rs_order) <= y)"
apply (insert rs_order_iff)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
by (auto)

lemma rs_order_if:
 "((x::'a::ms_rs_order) <= y) ==> x .|. n <= y .|. n"
apply (insert rs_order_iff)
apply (drule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
by (auto)

(*----------------------------------------------------------*
 |                                                          |
 |       Fixed point induction for refinement (CMS)         |
 |                                                          |
 *----------------------------------------------------------*)

(************************************************************
             continuity lemma for refinement
 ************************************************************)

lemma continuous_rs_Ref_fun: "continuous_rs (Ref_fun (z::'a::ms_rs_order))"
apply (simp add: continuous_rs_def)
apply (intro allI impI)
apply (simp add: Ref_fun_def)
apply (simp)
apply (subgoal_tac "~ (ALL n. z .|. n <= x .|. n)")
apply (simp)
apply (elim conjE exE)
apply (rule_tac x="n" in exI)
apply (intro allI impI)
apply (rotate_tac -1)
apply (drule sym)
apply (rule not_rs_orderI)
apply (simp)

apply (simp add: rs_order_iff)
done

(************************************************************
         continuity lemma for (Reverse) refinement
 ************************************************************)

lemma continuous_rs_Rev_fun: "continuous_rs (Rev_fun (z::'a::ms_rs_order))"
apply (simp add: continuous_rs_def)
apply (intro allI impI)
apply (simp add: Rev_fun_def)

apply (subgoal_tac "~ (ALL n. x .|. n <= z .|. n)")
apply (simp)
apply (elim conjE exE)
apply (rule_tac x="n" in exI)
apply (intro allI impI)
apply (rotate_tac -1)
apply (drule sym)
apply (rule not_rs_orderI)
apply (simp)

apply (simp add: rs_order_iff)
done

(************************************************************
          Metric Fixed Point Induction for refinement
 ************************************************************)

theorem cms_fixpoint_induction_ref:
  "[| ALL (xy::('a::cms_rs_order * 'a::cms_rs_order)). distance xy = distance_rs xy ;
      ALL (xy::('b::ms_rs * 'b::ms_rs)). distance xy = distance_rs xy ;
      constructive_rs f ; mono f ; X <= f X ; Y = f Y |]
   ==> (X::'a::cms_rs_order) <= Y"
apply (insert cms_fixpoint_induction_imp[of "Ref_fun X" X f])
 apply (drule mp)
  apply (simp)
  apply (rule conjI)
  apply (blast)
  apply (simp add: continuous_rs_Ref_fun)
  apply (simp add: Ref_fun_def)

      (* inductiveness *)
  apply (simp add: inductivefun_def)
  apply (intro allI impI)
  apply (simp add: mono_def)
  apply (rotate_tac 3)
  apply (drule_tac x="X" in spec)
  apply (rotate_tac -1)
  apply (drule_tac x="x" in spec)
  apply (simp)

apply (insert UFP_is[of f])
apply (simp add: isUFP_def)
apply (simp add: Ref_fun_def)
done

(************************************************************
        Metric Fixed Point Induction for refinement (rev)
 ************************************************************)

theorem cms_fixpoint_induction_rev:
 "[| ALL (xy::('a::cms_rs_order * 'a::cms_rs_order)). distance xy = distance_rs xy ;
     ALL (xy::('b::ms_rs * 'b::ms_rs)). distance xy = distance_rs xy ;
     constructive_rs f ; mono f ; f X <= X ; Y = f Y |]
   ==> (Y::'a::cms_rs_order) <= X"
apply (insert cms_fixpoint_induction_imp[of "Rev_fun X" X f])

 apply (drule mp)
  apply (simp)
  apply (rule conjI)
  apply (blast)
  apply (simp add: continuous_rs_Rev_fun)
  apply (simp add: Rev_fun_def)

      (* inductiveness *)
  apply (simp add: inductivefun_def)
  apply (intro allI impI)
  apply (simp add: mono_def)
  apply (rotate_tac 3)
  apply (drule_tac x="x" in spec)
  apply (drule_tac x="X" in spec)
  apply (drule_tac x="X" in spec)
  apply (simp)

apply (insert UFP_is[of f], simp)
apply (simp add: isUFP_def)
apply (simp add: Rev_fun_def)
done


end
