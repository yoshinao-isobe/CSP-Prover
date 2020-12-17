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
            |        CSP-Prover on Isabelle2018         |
            |               February 2019  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Infra_order
imports Infra_common
begin

(*****************************************************
                    order
 *****************************************************)

lemma order_antisymE:
  "[| (a::'a::order) = b ; [| a <= b ; b <= a |] ==> P |] ==> P"
apply (simp)
done

(*****************************************************
            Upper Bound and Lower Bound
 *****************************************************)

(* isabelle 2013: 
consts
  isUB  :: "'a::order => 'a::order set => bool"  ("_ isUB _" [55,55] 55)
  isLUB :: "'a::order => 'a::order set => bool"  ("_ isLUB _"[55,55] 55)
  isLB  :: "'a::order => 'a::order set => bool"  ("_ isLB _" [55,55] 55)
  isGLB :: "'a::order => 'a::order set => bool"  ("_ isGLB _"[55,55] 55)

def
  isUB_def  : "x isUB X  == ALL y. y:X --> y <= x"
  isLUB_def : "x isLUB X == (x isUB X) & (ALL y. y isUB X --> x <= y)"
  isLB_def  : "x isLB X  == ALL y. y:X --> x <= y"
  isGLB_def : "x isGLB X == (x isLB X) & (ALL y. y isLB X --> y <= x)"
*)

definition
    isUB  :: "'a::order => 'a::order set => bool"  ("_ isUB _" [55,55] 55)
  where
  "x isUB X  == (ALL y. y:X --> y <= x)"

definition
  isLUB :: "'a::order => 'a::order set => bool"  ("_ isLUB _"[55,55] 55)
  where
  "x isLUB X == (x isUB X) & (ALL y. y isUB X --> x <= y)"

definition
  isLB  :: "'a::order => 'a::order set => bool"  ("_ isLB _" [55,55] 55)
  where
  "x isLB X  == ALL y. y:X --> x <= y"
  
definition
  isGLB :: "'a::order => 'a::order set => bool"  ("_ isGLB _"[55,55] 55)
  where
  "x isGLB X == (x isLB X) & (ALL y. y isLB X --> y <= x)"

 (* isGLB_def : "x isGLB X == (x isLB X) & (ALL y. y isLB X --> y <= x)" *)
  
  
(* test  
lemma "0 isUB {0}"
apply (simp add: isUB_def)
done
*)

(* Isabelle 2013

consts
  hasLUB :: "'a::order set => bool" ("_ hasLUB" [1000] 55) 
  hasGLB :: "'a::order set => bool" ("_ hasGLB" [1000] 55) 

defs
  hasLUB_def: "X hasLUB == (EX x. x isLUB X)"
  hasGLB_def: "X hasGLB == (EX x. x isGLB X)"

consts
  LUB    :: "'a::order set => 'a::order"
  GLB    :: "'a::order set => 'a::order"

defs
  LUB_def    : "LUB X == if (X hasLUB) then THE x. (x isLUB X) else the None"
  GLB_def    : "GLB X == if (X hasGLB) then THE x. (x isGLB X) else the None"
*)

definition
  hasLUB :: "'a::order set => bool" ("_ hasLUB" [1000] 55) 
  where
  "X hasLUB == (EX x. x isLUB X)"
  
definition
  hasGLB :: "'a::order set => bool" ("_ hasGLB" [1000] 55) 
  where
  "X hasGLB == (EX x. x isGLB X)"
  
definition
  LUB    :: "'a::order set => 'a::order"
  where
  "LUB X == if (X hasLUB) then THE x. (x isLUB X) else the None"
  
definition
  GLB    :: "'a::order set => 'a::order"
  where
  "GLB X == if (X hasGLB) then THE x. (x isGLB X) else the None"

(*** LUB is unique ***)

lemma LUB_unique : "[| x isLUB X ; y isLUB X |] ==> x = y"
apply (unfold isLUB_def)
apply (elim conjE)
apply (drule_tac x="y" in spec)
apply (drule_tac x="x" in spec)
by (simp)

(*** GLB is unique ***)

lemma GLB_unique : "[| x isGLB X ; y isGLB X |] ==> x = y"
apply (unfold isGLB_def)
apply (elim conjE)
apply (drule_tac x="y" in spec)
apply (drule_tac x="x" in spec)
by (simp)

(*-----------------------*
 |       the LUB         |
 *-----------------------*)

lemma isLUB_to_LUB : "X hasLUB ==> x isLUB X = (x = LUB X)"
apply (simp add: LUB_def)
apply (rule iffI)

apply (rule sym)
apply (rule the_equality)
apply (simp)
apply (simp add: LUB_unique)

apply (simp add: hasLUB_def)
apply (erule exE)
apply (rule theI[of "(%x. x isLUB X)"])
apply (simp)
apply (simp add: LUB_unique)
done

lemmas LUB_to_isLUB = isLUB_to_LUB[THEN sym]

lemma LUB_to_isLUB_sym :
    "X hasLUB ==> (LUB X = x) = x isLUB X"
by (auto simp add: isLUB_to_LUB)

lemmas LUB_iff = LUB_to_isLUB LUB_to_isLUB_sym

lemma LUB_is: "X hasLUB ==> (LUB X) isLUB X"
apply (insert LUB_to_isLUB[of X "LUB X"])
by (simp)

lemma isLUB_LUB : "x isLUB X ==> (LUB X = x)"
apply (subgoal_tac "X hasLUB")
apply (simp add: LUB_iff)
apply (simp add: hasLUB_def)
apply (rule_tac x="x" in exI, simp)
done

(*-----------------------*
 |       the GLB         |
 *-----------------------*)

lemma isGLB_to_GLB : "X hasGLB ==> x isGLB X = (x = GLB X)"
apply (simp add: GLB_def)
apply (rule iffI)

apply (rule sym)
apply (rule the_equality)
apply (simp)
apply (simp add: GLB_unique)

apply (simp add: hasGLB_def)
apply (erule exE)
apply (rule theI[of "(%x. x isGLB X)"])
apply (simp)
apply (simp add: GLB_unique)
done

lemmas GLB_to_isGLB = isGLB_to_GLB[THEN sym]

lemma GLB_to_isGLB_sym :
    "X hasGLB ==> (GLB X = x) = x isGLB X"
by (auto simp add: isGLB_to_GLB)

lemmas GLB_iff = GLB_to_isGLB GLB_to_isGLB_sym

lemma GLB_is: "X hasGLB ==> (GLB X) isGLB X"
apply (insert GLB_to_isGLB[of X "GLB X"])
by (simp)

lemma isGLB_GLB : "x isGLB X ==> (GLB X = x)"
apply (subgoal_tac "X hasGLB")
apply (simp add: GLB_iff)
apply (simp add: hasGLB_def)
apply (rule_tac x="x" in exI, simp)
done

(*-----------------------*
 |     LUB subset        |
 *-----------------------*)

lemma isLUB_subset : "[| x isLUB X ; y isLUB Y ; X <= Y |] ==> x <= y"
apply (simp add: isLUB_def)
apply (elim conjE)

apply (drule_tac x="y" in spec)
apply (rotate_tac -1)
apply (drule mp)

apply (simp add: isUB_def)
apply (intro allI impI)
apply (rotate_tac 2)
apply (drule_tac x="ya" in spec)
apply (force)
by (simp)

(*-----------------------*
 |     GLB subset        |
 *-----------------------*)

lemma isGLB_subset : "[| x isGLB X ; y isGLB Y ; X <= Y |] ==> y <= x"
apply (simp add: isGLB_def)
apply (elim conjE)

apply (drule_tac x="y" in spec)
apply (rotate_tac -1)
apply (drule mp)

apply (simp add: isLB_def)
apply (intro allI impI)
apply (rotate_tac 2)
apply (drule_tac x="ya" in spec)
apply (force)
by (simp)

(*--------------------------*
 |  GLB exists for nat set  |
 *--------------------------*)

lemma EX_GLB_nat_lm: 
  "ALL m m'. m' <= m & m' : (X::nat set) --> (EX n. n isGLB X & n:X)"
apply (rule allI)
apply (induct_tac m)

(* base *)
apply (intro allI impI)
apply (rule_tac x="0" in exI)
apply (erule conjE)
apply (simp add: isGLB_def isLB_def)
apply (intro allI impI)
apply (drule_tac x="0" in spec)
apply (simp)

(* step *)
apply (intro allI impI)
apply (case_tac "EX m''. m'' <= n & m'':X")
apply (erule exE)
apply (drule_tac x="m''" in spec)
apply (simp)

apply (rule_tac x="m'" in exI)
apply (simp add: isGLB_def isLB_def)
apply (intro allI impI)

apply (case_tac "y < m'")
apply (drule_tac x="y" in spec)
by (auto)

(*** EX ***)

lemma EX_GLB_nat: 
  "(X::nat set) ~= {} ==> (EX n. n isGLB X & n:X)"
apply (subgoal_tac "EX m. m:X")
apply (erule exE)
apply (insert EX_GLB_nat_lm[of X])
apply (drule_tac x="m" in spec)
apply (drule_tac x="m" in spec)
apply (simp)
by (auto)

(*--------------------------*
 |       LUB is least       |
 *--------------------------*)

lemma LUB_least: "[| ALL x:X. x <= Y ; X hasLUB |]==> LUB X <= Y"
apply (insert LUB_is[of X])
apply (simp add: isLUB_def)
apply (elim conjE)
apply (drule_tac x="Y" in spec)
apply (simp add: isUB_def)
done

(*--------------------------*
 |       GLB is great       |
 *--------------------------*)

lemma GLB_great: "[| ALL x:X. Y <= x ; X hasGLB |]==> Y <= GLB X"
apply (insert GLB_is[of X])
apply (simp add: isGLB_def)
apply (elim conjE)
apply (drule_tac x="Y" in spec)
apply (simp add: isLB_def)
done

(*--------------------------*
 |       Union isLUB        |
 *--------------------------*)

(* Union X is an upper bound of X *)

lemma Union_isUB : "(Union X) isUB X"
apply (simp add: isUB_def)
apply (simp add: subset_iff)
apply (intro allI impI)
apply (rule_tac x=y in bexI)
by (auto)

(* UnionT Ts is the least upper bound of Ts *)

lemma Union_isLUB : "Union X isLUB X"
apply (simp add: isLUB_def Union_isUB)
apply (simp add: isUB_def)
apply (simp add: subset_iff)
apply (intro allI impI)
apply (erule bexE)
apply (drule_tac x="Xa" in spec)
by (simp)

(* the least upper bound of X is Union X *)

lemma isLUB_Union_only_if: "x isLUB X ==> x = Union X"
apply (insert Union_isLUB[of X])
apply (rule LUB_unique)
by (simp_all)

(* iff *)

lemma isLUB_Union : "(x isLUB X) = (x = Union X)"
apply (rule iffI)
apply (simp add: isLUB_Union_only_if)
apply (simp add: Union_isLUB)
done

(* LUB is Union X *)

lemma LUB_Union : "LUB X = Union X"
by (simp add: isLUB_LUB Union_isLUB)

(*****************************************************
                   MIN and MAX
 *****************************************************)
(* Isabelle 2013
consts
  isMAX :: "'a::order => 'a::order set => bool"  ("_ isMAX _"[55,55] 55)
  isMIN :: "'a::order => 'a::order set => bool"  ("_ isMIN _"[55,55] 55)

defs
  isMAX_def : "x isMAX X == (x isUB X) & (x : X)"
  isMIN_def : "x isMIN X == (x isLB X) & (x : X)"
*)

definition
  isMAX :: "'a::order => 'a::order set => bool"  ("_ isMAX _"[55,55] 55)
  where
  "x isMAX X == (x isUB X) & (x : X)"

definition
  isMIN :: "'a::order => 'a::order set => bool"  ("_ isMIN _"[55,55] 55)
  where
  "x isMIN X == (x isLB X) & (x : X)"

(* Isabelle 2013  
consts
  hasMAX :: "'a::order set => bool" ("_ hasMAX" [1000] 55) 
  hasMIN :: "'a::order set => bool" ("_ hasMIN" [1000] 55) 

defs
  hasMAX_def: "X hasMAX == (EX x. x isMAX X)"
  hasMIN_def: "X hasMIN == (EX x. x isMIN X)"
*)

definition
  hasMAX :: "'a::order set => bool" ("_ hasMAX" [1000] 55) 
  where
  "X hasMAX == (EX x. x isMAX X)"
  
definition
  hasMIN :: "'a::order set => bool" ("_ hasMIN" [1000] 55) 
  where
  "X hasMIN == (EX x. x isMIN X)"

(* Isabelle 2013
consts
  MAX    :: "'a::order set => 'a::order"
  MIN    :: "'a::order set => 'a::order"

defs
  MAX_def    : "MAX X == if (X hasMAX) then THE x. (x isMAX X) else the None"
  MIN_def    : "MIN X == if (X hasMIN) then THE x. (x isMIN X) else the None"
*)              

definition
  Max    :: "'a::order set => 'a::order"
  where
  "Max X == if (X hasMAX) then THE x. (x isMAX X) else the None"

definition
  Min    :: "'a::order set => 'a::order"
  where
  "Min X == if (X hasMIN) then THE x. (x isMIN X) else the None"

(*** MAX is unique ***)

lemma MAX_unique : "[| x isMAX X ; y isMAX X |] ==> x = y"
                                 apply (unfold isMAX_def isUB_def)
apply (elim conjE)
apply (drule_tac x="y" in spec)
apply (drule_tac x="x" in spec)
by (simp)

(*** MIN is unique ***)

lemma MIN_unique : "[| x isMIN X ; y isMIN X |] ==> x = y"
apply (unfold isMIN_def isLB_def)
apply (elim conjE)
apply (drule_tac x="y" in spec)
apply (drule_tac x="x" in spec)
by (simp)

(*-----------------------*
 |       the MAX         |
 *-----------------------*)

lemma isMAX_to_MAX : "X hasMAX ==> x isMAX X = (x = Max X)"
apply (simp add: Max_def)
apply (rule iffI)

apply (rule sym)
apply (rule the_equality)
apply (simp)
apply (simp add: MAX_unique)

apply (simp add: hasMAX_def)
apply (erule exE)
apply (rule theI[of "(%x. x isMAX X)"])
apply (simp)
apply (simp add: MAX_unique)
done

lemmas MAX_to_isMAX = isMAX_to_MAX[THEN sym]

lemma MAX_to_isMAX_sym :
    "X hasMAX ==> (Max X = x) = x isMAX X"
by (auto simp add: isMAX_to_MAX)

lemmas MAX_iff = MAX_to_isMAX MAX_to_isMAX_sym

(*-----------------------*
 |       the MIN         |
 *-----------------------*)

lemma isMIN_to_MIN : "X hasMIN ==> x isMIN X = (x = Min X)"
apply (simp add: Min_def)
apply (rule iffI)

apply (rule sym)
apply (rule the_equality)
apply (simp)
apply (simp add: MIN_unique)

apply (simp add: hasMIN_def)
apply (erule exE)
apply (rule theI[of "(%x. x isMIN X)"])
apply (simp)
apply (simp add: MIN_unique)
done

lemmas MIN_to_isMIN = isMIN_to_MIN[THEN sym]

lemma MIN_to_isMIN_sym :
    "X hasMIN ==> (Min X = x) = x isMIN X"
by (auto simp add: isMIN_to_MIN)

lemmas MIN_iff = MIN_to_isMIN MIN_to_isMIN_sym

(*-----------------------*
 |     MAX subset        |
 *-----------------------*)

lemma isMAX_subset : "[| x isMAX X ; y isMAX Y ; X <= Y |] ==> x <= y"
apply (simp add: isMAX_def isUB_def)
apply (elim conjE)

apply (rotate_tac 3)
apply (drule_tac x="x" in spec)
by (force)

(*-----------------------*
 |     MIN subset        |
 *-----------------------*)

lemma isMIN_subset : "[| x isMIN X ; y isMIN Y ; X <= Y |] ==> y <= x"
apply (simp add: isMIN_def isLB_def)
apply (elim conjE)

apply (rotate_tac 3)
apply (drule_tac x="x" in spec)
by (force)

(*--------------------------*
 |  MIN exists for nat set  |
 *--------------------------*)

lemma EX_MIN_nat_lm: 
  "ALL m m'. m' <= m & m' : (X::nat set) --> (EX n. n isMIN X)"
apply (rule allI)
apply (induct_tac m)

(* base *)
apply (intro allI impI)
apply (rule_tac x="0" in exI)
apply (erule conjE)
apply (simp add: isMIN_def isLB_def)

(* step *)
apply (intro allI impI)
apply (case_tac "EX m''. m'' <= n & m'':X")
apply (erule exE)
apply (drule_tac x="m''" in spec)
apply (simp)

apply (rule_tac x="m'" in exI)
apply (simp add: isMIN_def isLB_def)
apply (intro allI impI)

apply (case_tac "y < m'")
apply (drule_tac x="y" in spec)
by (auto)

(*** EX ***)

lemma EX_MIN_nat: 
  "(X::nat set) ~= {} ==> EX n. n isMIN X"
apply (subgoal_tac "EX m. m:X")
apply (erule exE)
apply (insert EX_MIN_nat_lm[of X])
apply (drule_tac x="m" in spec)
apply (drule_tac x="m" in spec)
apply (simp)
by (auto)

(*****************************************************
                   Fixed Point
 *****************************************************)

(* Isabelle 2013
consts
 isUFP :: "'a        => ('a       => 'a        ) => bool" (infixl "isUFP" 55) 
 isLFP :: "'a::order => ('a::order => 'a::order) => bool" (infixl "isLFP" 55)
 isGFP :: "'a::order => ('a::order => 'a::order) => bool" (infixl "isGFP" 55)

defs
  isUFP_def : "x isUFP f == (x = f x & (ALL y. y = f y --> x  = y))"
  isLFP_def : "x isLFP f == (x = f x & (ALL y. y = f y --> x <= y))"
  isGFP_def : "x isGFP f == (x = f x & (ALL y. y = f y --> y <= x))"

consts
  hasUFP:: "('a        => 'a       ) => bool" ("_ hasUFP" [1000] 55) 
  hasLFP:: "('a::order => 'a::order) => bool" ("_ hasLFP" [1000] 55) 
  hasGFP:: "('a::order => 'a::order) => bool" ("_ hasGFP" [1000] 55) 

defs
  hasUFP_def: "f hasUFP == (EX x. x isUFP f)"
  hasLFP_def: "f hasLFP == (EX x. x isLFP f)"
  hasGFP_def: "f hasGFP == (EX x. x isGFP f)"

consts
  UFP    :: "('a        => 'a       ) => 'a"
  LFP    :: "('a::order => 'a::order) => 'a::order"
  GFP    :: "('a::order => 'a::order) => 'a::order"

defs
  UFP_def : "UFP f == if (f hasUFP) then (THE x. x isUFP f) else the None"
  LFP_def : "LFP f == if (f hasLFP) then (THE x. x isLFP f) else the None"
  GFP_def : "GFP f == if (f hasGFP) then (THE x. x isGFP f) else the None"

*)

definition
  isUFP :: "'a        => ('a       => 'a        ) => bool" (infixl "isUFP" 55)
  where
  "x isUFP f == (x = f x & (ALL y. y = f y --> x  = y))"
 
definition 
  isLFP :: "'a::order => ('a::order => 'a::order) => bool" (infixl "isLFP" 55)
  where
  "x isLFP f == (x = f x & (ALL y. y = f y --> x <= y))"

definition
  isGFP :: "'a::order => ('a::order => 'a::order) => bool" (infixl "isGFP" 55)
  where
  "x isGFP f == (x = f x & (ALL y. y = f y --> y <= x))"

definition
  hasUFP:: "('a        => 'a       ) => bool" ("_ hasUFP" [1000] 55)
  where
  "f hasUFP == (EX x. x isUFP f)"

definition
  hasLFP:: "('a::order => 'a::order) => bool" ("_ hasLFP" [1000] 55)
  where
  "f hasLFP == (EX x. x isLFP f)"
  
definition
  hasGFP:: "('a::order => 'a::order) => bool" ("_ hasGFP" [1000] 55)
  where
  "f hasGFP == (EX x. x isGFP f)"

definition
  UFP    :: "('a        => 'a       ) => 'a"
  where
  "UFP f == if (f hasUFP) then (THE x. x isUFP f) else the None"

definition
  LFP    :: "('a::order => 'a::order) => 'a::order"
  where
  "LFP f == if (f hasLFP) then (THE x. x isLFP f) else the None"
  
definition
  GFP    :: "('a::order => 'a::order) => 'a::order"
  where
  "GFP f == if (f hasGFP) then (THE x. x isGFP f) else the None"

(*******************************
            lemmas 
 *******************************)

(*** UFP is unique ***)

lemma UFP_unique : "[| x isUFP f ; y isUFP f |] ==> x = y"
by (simp add: isUFP_def)

(*** LFP is unique ***)

lemma LFP_unique : "[| x isLFP f ; y isLFP f |] ==> x = y"
apply (unfold isLFP_def)
apply (erule conjE)+
apply (drule_tac x="y" in spec)
apply (drule_tac x="x" in spec)
by (simp)

(*** GFP is unique ***)

lemma GFP_unique : "[| x isGFP f ; y isGFP f |] ==> x = y"
apply (unfold isGFP_def)
apply (erule conjE)+
apply (drule_tac x="y" in spec)
apply (drule_tac x="x" in spec)
by (simp)

(*-----------------------*
 |       the UFP         |
 *-----------------------*)

lemma isUFP_to_UFP : "f hasUFP ==> x isUFP f = (x = UFP f)"
apply (simp add: UFP_def)
apply (rule iffI)

apply (rule sym)
apply (rule the_equality)
apply (simp)
apply (simp add: UFP_unique)

apply (simp add: hasUFP_def)
apply (erule exE)
apply (rule theI[of "(%x. x isUFP f)"])
apply (simp)
apply (simp add: UFP_unique)
done

lemmas UFP_to_isUFP = isUFP_to_UFP[THEN sym]

lemma UFP_to_isUFP_sym :
    "f hasUFP ==> (UFP f = x) = x isUFP f"
by (auto simp add: isUFP_to_UFP)

lemmas UFP_iff = UFP_to_isUFP UFP_to_isUFP_sym

(*** UFP is ***)

lemma UFP_is : "f hasUFP ==> (UFP f) isUFP f"
by (simp add: isUFP_to_UFP)

lemma isUFP_UFP : "x isUFP f ==> (UFP f = x)"
apply (subgoal_tac "f hasUFP")
apply (simp add: UFP_iff)
apply (simp add: hasUFP_def)
apply (rule_tac x="x" in exI, simp)
done

(*** UFP is fixed point ***)

lemma UFP_fp_lm : "[| f hasUFP ; x = UFP f |] ==> f x = x"
apply (simp add: UFP_iff)
apply (simp add: isUFP_def)
done

lemma UFP_fp : "f hasUFP ==> f (UFP f) = UFP f"
by (simp add: UFP_fp_lm)

(*** unique solution ***)

lemma hasUFP_unique_solution : 
  "[| f hasUFP ; f x = x ; f y = y |] ==> x = y"
apply (simp add: hasUFP_def)
apply (erule exE)
apply (simp add: isUFP_def)
apply (erule conjE)
apply (frule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (simp)
done

(*-----------------------*
 |       the LFP         |
 *-----------------------*)

lemma isLFP_to_LFP : "f hasLFP ==> x isLFP f = (x = LFP f)"
apply (simp add: LFP_def)
apply (rule iffI)

apply (rule sym)
apply (rule the_equality)
apply (simp)
apply (simp add: LFP_unique)

apply (simp add: hasLFP_def)
apply (erule exE)
apply (rule theI[of "(%x. x isLFP f)"])
apply (simp)
apply (simp add: LFP_unique)
done

lemmas LFP_to_isLFP = isLFP_to_LFP[THEN sym]

lemma LFP_to_isLFP_sym :
    "f hasLFP ==> (LFP f = x) = x isLFP f"
by (auto simp add: isLFP_to_LFP)

lemmas LFP_iff = LFP_to_isLFP LFP_to_isLFP_sym

(*** LFP is ***)

lemma LFP_is : "f hasLFP ==> (LFP f) isLFP f"
by (simp add: isLFP_to_LFP)

lemma isLFP_LFP : "x isLFP f ==> (LFP f = x)"
apply (subgoal_tac "f hasLFP")
apply (simp add: LFP_iff)
apply (simp add: hasLFP_def)
apply (rule_tac x="x" in exI, simp)
done

(*** LFP is fixed point ***)

lemma LFP_fp_lm : "[| f hasLFP ; x = LFP f |] ==> f x = x"
apply (simp add: LFP_iff)
apply (simp add: isLFP_def)
done

lemma LFP_fp : "f hasLFP ==> f (LFP f) = LFP f"
by (simp add: LFP_fp_lm)

(*** LFP is least ***)

lemma LFP_least : "[| f hasLFP ; f x = x |] ==> LFP f <= x"
apply (insert LFP_is[of f])
apply (simp add: isLFP_def)
done

(*-----------------------*
 |       the GFP         |
 *-----------------------*)

lemma isGFP_to_GFP : "f hasGFP ==> x isGFP f = (x = GFP f)"
apply (simp add: GFP_def)
apply (rule iffI)

apply (rule sym)
apply (rule the_equality)
apply (simp)
apply (simp add: GFP_unique)

apply (simp add: hasGFP_def)
apply (erule exE)
apply (rule theI[of "(%x. x isGFP f)"])
apply (simp)
apply (simp add: GFP_unique)
done

lemmas GFP_to_isGFP = isGFP_to_GFP[THEN sym]

lemma GFP_to_isGFP_sym :
    "f hasGFP ==> (GFP f = x) = x isGFP f"
by (auto simp add: isGFP_to_GFP)

lemmas GFP_iff = GFP_to_isGFP GFP_to_isGFP_sym

(*** GFP is ***)

lemma GFP_is : "f hasGFP ==> (GFP f) isGFP f"
by (simp add: isGFP_to_GFP)

lemma isGFP_GFP : "x isGFP f ==> (GFP f = x)"
apply (subgoal_tac "f hasGFP")
apply (simp add: GFP_iff)
apply (simp add: hasGFP_def)
apply (rule_tac x="x" in exI, simp)
done

(*** GFP is fixed point ***)

lemma GFP_fp_lm : "[| f hasGFP ; x = GFP f |] ==> f x = x"
apply (simp add: GFP_iff)
apply (simp add: isGFP_def)
done

lemma GFP_fp : "f hasGFP ==> f (GFP f) = GFP f"
by (simp add: GFP_fp_lm)

(*** GFP is greatest ***)

lemma GFP_greatest : "[| f hasGFP ; f x = x |] ==> x <= GFP f"
apply (insert GFP_is[of f])
apply (simp add: isGFP_def)
done

(*-----------------------*
 |     UFP --> LFP       |
 *-----------------------*)

lemma hasUFP_hasLFP: "f hasUFP ==> f hasLFP"
apply (simp add: hasUFP_def hasLFP_def)
apply (simp add: isUFP_def isLFP_def)
by (auto)

lemma hasUFP_LFP_UFP: "f hasUFP ==> LFP f = UFP f"
apply (simp add: isUFP_to_UFP[THEN sym])
apply (insert LFP_is[of f])
apply (simp add: hasUFP_hasLFP)
apply (simp add: hasUFP_def)
apply (simp add: isUFP_def isLFP_def)
apply (intro allI impI)
apply (elim conjE exE)
apply (rotate_tac -1)
apply (frule_tac x="y" in spec)
apply (drule_tac x="LFP f" in spec)
by (simp)

(*-----------------------*
 |     UFP --> GFP       |
 *-----------------------*)

lemma hasUFP_hasGFP: "f hasUFP ==> f hasGFP"
apply (simp add: hasUFP_def hasGFP_def)
apply (simp add: isUFP_def isGFP_def)
by (auto)

lemma hasUFP_GFP_UFP: "f hasUFP ==> GFP f = UFP f"
apply (simp add: isUFP_to_UFP[THEN sym])
apply (insert GFP_is[of f])
apply (simp add: hasUFP_hasGFP)
apply (simp add: hasUFP_def)
apply (simp add: isUFP_def isGFP_def)
apply (intro allI impI)
apply (elim conjE exE)
apply (rotate_tac -1)
apply (frule_tac x="y" in spec)
apply (drule_tac x="GFP f" in spec)
by (simp)

end
