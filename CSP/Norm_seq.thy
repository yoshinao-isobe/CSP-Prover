           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  March 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2020         |
            |                  April 2020  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Norm_seq
imports CMS
begin

(*****************************************************************

         1. Definition of Normarized sequences
         2. Properties of Normarized sequences
         3. How to transform each Cauchy sequence to NF
         4. The same limit between xs and NF(xs)

 *****************************************************************)

definition
  normal :: "'a::ms infinite_seq => bool"
  where
  normal_def : 
    "normal xs == ALL (n::nat) (m::nat). 
        distance(xs n, xs m) <= (1/2)^(min n m)"
  
definition  
  Nset   :: "'a::ms infinite_seq => real => nat set"
  where
  Nset_def :
    "Nset xs delta == 
     {N. ALL n m. (N <= m & N <= n) --> distance(xs n, xs m) <= delta}"
  
definition  
  Nmin   :: "'a::ms infinite_seq => real => nat"
  where
  Nmin_def :
    "Nmin xs delta == Min (Nset xs delta)"
  
definition  
  NF     :: "'a::ms infinite_seq => 'a::ms infinite_seq"
  where
  NF_def :
    "NF xs == (%n. xs (Nmin xs ((1/2)^n)))"

(********************************************************************
                          Normalization
 ********************************************************************)

(*** normalized sequence --> Cauchy sequence ***)


lemma normal_cauchy: "normal xs ==> cauchy xs"

  apply (simp add: cauchy_def)
  apply (intro allI impI)
  apply (subgoal_tac "EX n. (1/2) ^ n < delta")
  apply (erule exE)
  apply (rule_tac x="n" in exI)
  apply (intro allI impI)
  apply (simp add: normal_def)
  apply (drule_tac x="i" in spec)
  apply (drule_tac x="j" in spec)
  
  apply (rule le_less_trans)   (* modified for Isabelle2020 *)
  apply (simp)
  apply (rule le_less_trans[of _ "(1 / 2) ^ _"])
  apply (simp)
  apply (simp)
  apply (simp add: pow_convergence)
done

(*
declare realpow_Suc          [simp del]
in isabelle2008
*)

declare power_Suc          [simp del]

lemma normal_Limit: 
  "[| normal xs ; xs convergeTo y |]
        ==> distance(xs (Suc n), y) < (1/2)^n"
apply (simp add: convergeTo_def)
apply (drule_tac x="(1/2)^(Suc n)" in spec)
apply (simp)
apply (erule exE)

apply (rename_tac N)
apply (case_tac "N <= Suc n")
 apply (drule_tac x="Suc n" in spec)
 apply (simp add: symmetry_ms)

 apply (rule less_le_trans)   (* modified for Isabelle2020 *)
 apply (simp)
 apply (subgoal_tac "((1::real) / 2) ^ Suc n <= (1 / 2) ^ n")
 apply (simp)
 apply (simp add: power_decreasing)

(* else (i.e. Suc n < N *)
 apply (drule_tac x="N" in spec)
 apply (simp)
 apply (insert triangle_inequality_ms)
 apply (drule_tac x="xs (Suc n)" in spec)
 apply (drule_tac x="xs N" in spec)
 apply (drule_tac x="y" in spec)

 apply (simp add: normal_def)
 apply (drule_tac x="Suc n" in spec)
 apply (drule_tac x="N" in spec)
 apply (simp add: symmetry_ms)
 apply (simp add: power_Suc)
done

(*
declare realpow_Suc          [simp]
*)
declare power_Suc          [simp]

(********************************************************************
                                Nmin
 ********************************************************************)

(*** Nmin exists ***)

lemma Nmin_exists: 
  "[| 0 < delta ; cauchy xs |] ==> EX N. N isMIN (Nset xs delta)"
apply (simp add: cauchy_def)
apply (drule_tac x="delta" in spec)
apply (simp)
apply (erule exE)

apply (rule EX_MIN_nat)
apply (simp add: Nset_def)
apply (rule_tac x="n" in exI)
apply (intro allI impI)
apply (drule_tac x="na" in spec)
apply (drule_tac x="m" in spec)
by (simp)

lemma Nset_hasMIN: 
  "[| 0 < delta ; cauchy xs |] ==> (Nset xs delta) hasMIN"
apply (simp add: hasMIN_def)
apply (rule Nmin_exists)
by (simp)

(*** Nmin unique ***)

lemma Nmin_unique: 
  "[| N isMIN (Nset xs delta) ; M isMIN (Nset xs delta) |] ==> N = M"
by (simp add: MIN_unique)

(*-----------------------*
 |       the Nmin        |
 *-----------------------*)

lemma Nset_to_Nmin : 
  "[| 0 < delta ; cauchy xs |]
   ==> (N isMIN (Nset xs delta)) = (Nmin xs delta = N)"
apply (simp add: Nmin_def)
apply (rule iffI)

apply (simp add: Min_def Nset_hasMIN)
apply (rule the_equality)
apply (simp)
apply (simp add: Nmin_unique)

by (simp add: MIN_iff Nset_hasMIN)

lemmas Nmin_to_Nset = Nset_to_Nmin[THEN sym]

lemma Nmin_to_Nset_sym :
    "[| 0 < delta ; cauchy xs |] 
     ==> (N = Nmin xs delta) = (N isMIN (Nset xs delta))"
by (auto simp add: Nset_to_Nmin)

lemmas Nmin_iff = Nmin_to_Nset Nmin_to_Nset_sym

(*-----------------------*
 |      property         |
 *-----------------------*)

lemma Nmin_cauchy_lm:
  "[| 0 < delta ; cauchy xs ; Nmin xs delta = N |]
   ==> (ALL n m. (N <= m & N <= n) --> distance(xs n, xs m) <= delta)"
by (simp add: Nmin_iff Nset_def isMIN_def)

lemma Nmin_cauchy:
  "[| 0 < delta ; cauchy xs ; Nmin xs delta <= m ; Nmin xs delta <= n |]
   ==> distance(xs n, xs m) <= delta"
by (simp add: Nmin_cauchy_lm)

(*-----------------------*
 |   min_number_cauchy   |
 *-----------------------*)

(*** Nmin order (check) ***)

lemma min_number_cauchy_lm:
  "[| 0 < delta1 ; delta1 <= delta2 ; cauchy xs |]
   ==> Nset xs delta1 <= Nset xs delta2"
apply (simp add: Nset_def)
apply (rule subsetI)
apply (simp)
apply (intro allI impI)
apply (drule_tac x="n" in spec)
apply (drule_tac x="m" in spec)
by (simp)

(*** Nmin order ***)

lemma min_number_cauchy:
  "[| 0 < delta1 ; delta1 <= delta2 ; cauchy xs ;
      Nmin xs delta1 = N1 ; Nmin xs delta2 = N2 |]
   ==> N2 <= N1"
apply (simp add: Nmin_iff)
by (simp add: isMIN_subset min_number_cauchy_lm)

(*** Nmin order half ***)

lemma min_number_cauchy_half:
  "[| n <= m ; cauchy xs ; Nmin xs ((1/2)^n) = N1 ; Nmin xs ((1/2)^m) = N2 |]
   ==> N1 <= N2"
apply (rule min_number_cauchy)
by (simp_all add: power_decreasing)

(*------------------------*
 | normal_form_seq_normal |
 *------------------------*)

lemma normal_form_seq_normal: "cauchy xs ==> normal (NF(xs))"
apply (simp add: normal_def NF_def)
apply (intro allI)

apply (case_tac "n <= m")
 apply (simp add: min_def)
 apply (rule Nmin_cauchy, simp_all)
 apply (rule min_number_cauchy_half, simp_all)

(* else *)
 (*apply (simp add: min_def)*)
 apply (rule Nmin_cauchy, simp_all)
 apply (rule min_number_cauchy_half, simp_all)
done

(*----------------------------*
 | normal_form_seq_same_Limit |
 *----------------------------*)

(*** only if part ***)

lemma normal_form_seq_same_Limit_only_if:
  "[| cauchy xs ; xs convergeTo y |] ==> NF(xs) convergeTo y"
apply (simp add: convergeTo_def)
apply (intro allI impI)
apply (drule_tac x="eps/2" in spec)
apply (simp)
apply (erule exE)

apply (subgoal_tac "EX n. (1 / 2) ^ n < eps/2")
apply (erule exE)
apply (rename_tac eps N M)

apply (rule_tac x="M" in exI)
apply (intro allI impI)

apply (case_tac "N <= Nmin xs ((1/2)^m)")

 apply (drule_tac x="Nmin xs ((1/2)^m)" in spec)
 apply (simp add: NF_def)

(* else *)
 apply (insert triangle_inequality_ms)
 apply (drule_tac x="y" in spec)
 apply (drule_tac x="xs N" in spec)
 apply (drule_tac x="(NF xs) m" in spec)

 apply (drule_tac x="N" in spec)
 apply (simp add: NF_def)

 apply (subgoal_tac "distance (xs N, xs (Nmin xs ((1 / 2) ^ m))) <= (1 / 2) ^ m")
 apply (subgoal_tac "((1::real) / 2) ^ m <= (1 / 2) ^ M")
 apply (simp (no_asm_simp))  (* modified for Isabelle2020 *)
 apply (simp) 
 apply (rule Nmin_cauchy)
 apply (simp, simp, simp, simp)
 apply (rule pow_convergence)
 apply (simp_all)
done

(*** if part ***)

lemma normal_form_seq_same_Limit_if:
  "[| cauchy xs ; NF (xs) convergeTo y |] ==> xs convergeTo y"
apply (simp add: convergeTo_def)
apply (intro allI impI)
apply (drule_tac x="eps/2" in spec)
apply (simp)
apply (erule exE)

apply (subgoal_tac "EX n. (1 / 2) ^ n < eps/2")
apply (erule exE)
apply (rename_tac eps N M)

apply (rule_tac x="Nmin xs ((1/2)^(max N M))" in exI)
apply (intro allI impI)

apply (insert triangle_inequality_ms)
apply (drule_tac x="y" in spec)
apply (drule_tac x="xs (Nmin xs ((1/2)^(max N M)))" in spec)
apply (drule_tac x="xs m" in spec)

apply (drule_tac x="max N M" in spec)
(* apply (simp add: le_maxI1) *)
apply (simp add: NF_def)

(* *)
 apply (subgoal_tac 
   "distance(xs (Nmin xs ((1 / 2) ^ max N M)), xs m) <= (1 / 2) ^ max N M")
 apply (subgoal_tac "((1::real) / 2) ^ max N M <= (1 / 2) ^ M")
 apply (simp (no_asm_simp) add: max_def power_decreasing)   (* modified for 2020 *)
 apply (simp)
 
 apply (rule Nmin_cauchy)
 apply (simp, simp, simp, simp)
 apply (rule pow_convergence)
 apply (simp_all)
done

(*** iff ***)

lemma normal_form_seq_same_Limit:
  "cauchy xs ==> xs convergeTo y = NF(xs) convergeTo y"
apply (rule iffI)
apply (simp add: normal_form_seq_same_Limit_only_if)
apply (simp add: normal_form_seq_same_Limit_if)
done

end
