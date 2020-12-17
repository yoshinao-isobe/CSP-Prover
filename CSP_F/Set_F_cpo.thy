           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                 August 2005  (modified)   |
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

theory Set_F_cpo
imports Set_F CSP.CPO
begin

(*****************************************************************

         1. Set_F is a pointed cpo.
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
                      Bottom in Set_T
 *********************************************************)
(*
instance setF :: (type) bot0
by (intro_classes)
*)


instantiation setF :: (type) bot0
begin

definition
  bottom_setF_def : "Bot == {}f"
instance ..
end

(*

defs (overloaded)
  bottom_setF_def : "Bot == {}f"
*)

lemma bottom_setF : "ALL (F::'a setF). Bot <= F"
by (simp add: bottom_setF_def)

instance setF :: (type) bot
apply (intro_classes)
by (simp add: bottom_setF)

(********************************************************** 
      lemmas used in a proof that set_F is a cpo.
 **********************************************************)

(* UnionF Fs is an upper bound of Fs *)

lemma UnionF_isUB : "(UnionF Fs) isUB Fs"
apply (simp add: isUB_def)
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (rule_tac x=y in bexI)
by (auto)

(* UnionF Fs is the least upper bound of Fs *)

lemma UnionF_isLUB : "UnionF Fs isLUB Fs"
apply (simp add: isLUB_def UnionF_isUB)
apply (simp add: isUB_def)
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (erule bexE)
apply (drule_tac x="F" in spec)
by (simp)

(* the least upper bound of Fs is UnionF Fs *)

lemma isLUB_UnionF_only_if: "F isLUB Fs ==> F = UnionF Fs"
apply (insert UnionF_isLUB[of Fs])
apply (rule LUB_unique)
by (simp_all)

(* iff *)

lemma isLUB_UnionF : "(F isLUB Fs) = (F = UnionF Fs)"
apply (rule iffI)
apply (simp add: isLUB_UnionF_only_if)
apply (simp add: UnionF_isLUB)
done

(* LUB is UnionF Fs *)

lemma LUB_UnionF : "LUB Fs = UnionF Fs"
by (simp add: isLUB_LUB UnionF_isLUB)

(********************************************************** 
                 ( setF, <= ) is a CPO
 **********************************************************)

instance setF :: (type) cpo
apply (intro_classes)
apply (simp add: hasLUB_def)
apply (rule_tac x="UnionF X" in exI)
apply (simp add: directed_def UnionF_isLUB)
done

(********************************************************** 
              ( setF, <= ) is a pointed CPO
 **********************************************************)

instance setF :: (type) cpo_bot
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
