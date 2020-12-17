           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009-2       |
            |                October 2010  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Domain_T_cpo 
imports Domain_T CSP.CPO
begin

(*****************************************************************

         1. Domain_T is a pointed cpo.
         2. 
         3. 
         4. 

 *****************************************************************)

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  Union (B ` A) = (UN x:A. B x)                      *)
(*                  Inter (B ` A) = (INT x:A. B x)                     *)

(*
declare Union_image_eq [simp del]
declare Inter_image_eq [simp del]
*)
(* no simp rules in Isabelle 2017 
declare Sup_image_eq [simp del]
declare Inf_image_eq [simp del]
*)

(*********************************************************
                      Bottom in Dom_T
 *********************************************************)
(* isabelle 2009-1
instance domT :: (type) bot0
by (intro_classes)

defs (overloaded)
  bottom_domT_def   :  "Bot == {<>}t"
*)

instantiation domT :: (type) bot0
begin

definition
  bottom_domT_def : "Bot == {<>}t"

instance ..

end


lemma bottom_domT : "Bot <= (T::'a domT)"
by (simp add: bottom_domT_def)

instance domT :: (type) bot
apply (intro_classes)
by (simp add: bottom_domT)

(********************************************************** 
      lemmas used in a proof that domain_T is a cpo.
 **********************************************************)

(* UnionT Ts is an upper bound of Ts *)

lemma UnionT_isUB : "(UnionT Ts) isUB Ts"
apply (simp add: isUB_def)
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (subgoal_tac "Ts ~= {}")
apply (simp)
apply (rule_tac x=y in bexI)
by (auto)

(* UnionT Ts is the least upper bound of Ts *)

lemma UnionT_isLUB : "Ts ~= {} ==> UnionT Ts isLUB Ts"
apply (simp add: isLUB_def UnionT_isUB)
apply (simp add: isUB_def)
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (erule bexE)
apply (drule_tac x="T" in spec)
by (simp)

(* the least upper bound of Ts is UnionT Ts *)

lemma isLUB_UnionT_only_if: "[| Ts ~= {} ; T isLUB Ts |] ==> T = UnionT Ts"
apply (insert UnionT_isLUB[of Ts])
apply (simp)
apply (rule LUB_unique)
by (simp_all)

(* iff *)

lemma isLUB_UnionT : "Ts ~= {} ==> (T isLUB Ts) = (T = UnionT Ts)"
apply (rule iffI)
apply (simp add: isLUB_UnionT_only_if)
apply (simp add: UnionT_isLUB)
done

(* LUB is UnionT Ts *)

lemma LUB_UnionT : "Ts ~= {} ==> LUB Ts = UnionT Ts"
by (simp add: isLUB_LUB UnionT_isLUB)

(********************************************************** 
                 ( domT, <= ) is a CPO
 **********************************************************)

instance domT :: (type) cpo
apply (intro_classes)
apply (simp add: hasLUB_def)
apply (rule_tac x="UnionT X" in exI)
apply (simp add: directed_def UnionT_isLUB)
done

(********************************************************** 
              ( domT, <= ) is a pointed CPO
 **********************************************************)

instance domT :: (type) cpo_bot
by (intro_classes)

(****************** to add them again ******************)

(*
declare Union_image_eq [simp]
declare Inter_image_eq [simp]
*)
(*
declare Sup_image_eq [simp]
declare Inf_image_eq [simp]
*)

end
