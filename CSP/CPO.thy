           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
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
            |        CSP-Prover on Isabelle2020         |
            |                  April 2020  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CPO
imports Infra
begin

(*****************************************************************

         1. Complete partial order (cpo)
         2. Continuity
         3. Tarski Theorem

 *****************************************************************)

definition
  directed ::  "'a::order set => bool"
  where
  directed_def : "directed X == ((X ~= {}) &
                                 (ALL x y. x : X & y : X -->
                                    (EX z. z : X & x <= z & y <= z)))"
(* 2009-1
axclass bot0 < order
consts Bot :: "'a::bot0"  (* Bottom *)

axclass
  bot < bot0
  bottom_bot : "Bot <= (x::'a::bot0)"
*)

class bot0 = 
fixes Bot :: "'a::order"  ("Bot") (* Bottom *)

class bot = bot0 + 
assumes bottom_bot : "Bot <= x"

(*
class Bot =
fixes Bot :: "'a::order"  (* Bottom *)

class bot = Bot +
assumes bottom_bot : "Bot <= x"
*)

(* 2009-1
axclass
  cpo < order
  complete_cpo : "(directed (X::'a::order set)) ==> X hasLUB"
*)

class cpo = ord +
assumes complete_cpo : "(directed (X::'a::order set)) ==> X hasLUB"

(*** pointed cpo ***)

(*
axclass cpo_bot < cpo, bot
*)

class cpo_bot = cpo + bot

definition
  continuous  :: "('a::cpo => 'b::cpo) => bool"
  where
  continuous_def : "continuous f == ALL X. 
                      directed X --> ((f ` X) hasLUB & LUB (f ` X) = f (LUB X))"
definition
  admissible  :: "('a::cpo => bool) => bool"
  where
  admissible_def : "admissible P == ALL X. 
                      directed X --> (ALL x:X. P x) --> P (LUB X)"

(********************************************************** 
                    small lemmas
 **********************************************************)

lemma complete_cpo_lm:
  "ALL (X::'a::cpo set). directed X --> X hasLUB"
by (simp add: complete_cpo)

(*** another definition of continuous ***)

lemma continuous_only_if: "continuous f ==>
          directed X --> (EX x. ((f x) isLUB (f ` X) & x isLUB X))"
apply (intro allI impI)
apply (insert complete_cpo_lm)
apply (drule_tac x="X" in spec)
apply (simp)
apply (insert LUB_is[of X], simp)

apply (simp add: hasLUB_def)
apply (erule exE)
apply (rule_tac x="x" in exI)

apply (simp add: continuous_def)
apply (drule_tac x="X" in spec)
apply (simp)

apply (erule conjE)
apply (simp add: LUB_iff)

apply (insert LUB_unique[of "LUB X" X])
by (simp)

lemma continuous_if: 
    "ALL X. directed X --> (EX x. ((f x) isLUB (f ` X) & x isLUB X))
     ==> continuous f"
apply (simp add: continuous_def)
apply (intro allI impI)
apply (drule_tac x="X" in spec)
apply (simp)
apply (elim conjE exE)

apply (subgoal_tac "(f ` X) hasLUB", simp)
apply (simp add: LUB_iff)
apply (subgoal_tac "x = LUB X", simp)
apply (rule LUB_unique)
apply (simp)
apply (rule LUB_is)

apply (simp add: hasLUB_def)
apply (rule_tac x="x" in exI, simp)

apply (simp add: hasLUB_def)
apply (rule_tac x="f x" in exI, simp)
done

(*** iff ***)

lemma continuous_iff: "continuous f =
   (ALL X. directed X --> (EX x. ((f x) isLUB (f ` X) & x isLUB X)))"
apply (rule iffI)
apply (simp add: continuous_only_if)
apply (simp add: continuous_if)
done

(********************************************************** 
             lemmas and theorems for Tarski
 **********************************************************)

(* LUB is not affected by Bot *)

lemma LUB_with_Bot: 
  "((x::('a::cpo_bot)) isLUB {x. f x | x = Bot}) = (x isLUB {x. f x})"
apply (rule iffI)

apply (simp add: isLUB_def isUB_def)
apply (erule conjE)
apply (intro allI impI)
apply (rotate_tac 1)
apply (drule_tac x="y" in spec)
apply (rotate_tac -1)
apply (drule mp)
apply (intro allI)
apply (drule_tac x="ya" in spec)
apply (simp add: bottom_bot)
apply (assumption)

apply (simp add: isLUB_def isUB_def bottom_bot)
done

(************************************************************)

(* if x<=y then {x,y} is a directed set. *)
(* this is used in a proof for continuous_mono *)

lemma directed_x_y: "x <= y ==> directed {x, y}"
apply (simp add: directed_def)
apply (intro allI impI)
apply (rule_tac x="y" in exI)
by (auto)

(* the least upper bound of a set {x,y} *)
(* this is used in a proof for continuous_mono *)

lemma LUB_x_y: "[| x <= y ; z isLUB {x, y} |] ==> z = y"
apply (simp only: isUB_def isLUB_def)
apply (elim conjE)
apply (drule_tac x="y" in spec, simp)
apply (drule_tac x="y" in spec, simp)
done

(************************ continuity *****************************)

(* f is continuous --> f is monotonic *)

lemma continuous_mono: "continuous f ==> mono f"
apply (simp add: continuous_iff mono_def)
apply (intro allI impI)
apply (rename_tac A B)
apply (drule_tac x="{A,B}" in spec)
apply (simp add: directed_x_y)
apply (erule exE)
apply (erule conjE)

apply (subgoal_tac "x = B")
apply (simp add: isUB_def isLUB_def)
apply (simp add: LUB_x_y)
done

(* directed and functions *)

lemma directed_continuous: 
  "[| continuous f ; directed X |] ==> directed (f ` X)"
apply (insert continuous_mono[of f])
apply (simp add: continuous_iff directed_def)
apply (drule_tac x="X" in spec)
apply (simp)
apply (intro allI impI)
apply (simp add: in_image_set)
apply (elim conjE exE)

apply (drule_tac x="ya" in spec)
apply (drule_tac x="yb" in spec)
apply (simp)
apply (elim conjE exE)

apply (rule_tac x="z" in bexI)   (* modified for 2020 *)
apply (simp add: mono_def) 
apply (simp add: mono_def) 
done

(* composition of continuous functions *)

lemma compo_continuous: 
  "[| continuous f ; continuous g |] ==> continuous (g o f)"
apply (insert directed_continuous[of f])

apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="X" in spec)
apply (drule_tac x="f ` X" in spec)
apply (simp)
apply (elim conjE exE)
apply (rule_tac x="x" in exI)
(* Isabelle 2013  apply (simp add: image_compose) *)
apply (simp add: image_comp)

apply (subgoal_tac "xa = f x", simp)
apply (simp add: LUB_unique)
done

(*********************** Tarski continuous ****************************)

lemma Tarski_directed_lm1:
  "mono (f::('a::cpo_bot => 'a::cpo_bot)) ==> (f ^^ n) Bot <= (f ^^ (n+1)) Bot"
apply (induct_tac n)
apply (simp add: bottom_bot)
apply (simp add: mono_def)
done

lemma Tarski_directed_lm2:
  "mono (f::('a::cpo_bot => 'a::cpo_bot)) ==> (f ^^ n) Bot <= (f ^^ (n+m)) Bot"
apply (induct_tac m)
apply (simp)
apply (insert Tarski_directed_lm1[of f])
apply (rule order_trans)
apply (simp)
apply (simp)
done

lemma Tarski_directed:
  "mono (f::('a::cpo_bot => 'a::cpo_bot)) ==> directed {x. EX n. x = (f^^n) Bot}"
apply (simp add: directed_def)

apply (rule conjI)
apply (rule_tac x="Bot" in exI)
apply (rule_tac x="0" in exI)
apply (simp)

apply (intro allI impI)
apply (elim conjE exE)

apply (rename_tac x y n m)
apply (case_tac "m <= n")

apply (rule_tac x="x" in exI)
apply (rule conjI)
apply (rule_tac x="n" in exI)
apply (assumption)

apply (simp)
apply (subgoal_tac "(f ^^ m) Bot <= (f ^^ (m + (n-m))) Bot", simp)
apply (rule Tarski_directed_lm2, simp)

apply (rule_tac x="y" in exI)
apply (rule conjI)
apply (rule_tac x="m" in exI)
apply (assumption)

      (* ~ m <= n *)
apply (simp)
apply (subgoal_tac "(f ^^ n) Bot <= (f ^^ (n + (m-n))) Bot", simp)
apply (rule Tarski_directed_lm2, simp)
done

lemma Tarski_image_expand_lm:
  "f ` {x. EX n. x = (f ^^ n) Bot} = {x. EX n. x = f ((f ^^ n) Bot)}"
apply (auto simp add: image_Collect)
done

lemma Tarski_by_continuity:
  "continuous (f::('a::cpo_bot => 'a::cpo_bot)) ==> 
    (EX x. f x isLUB {x. EX n. x = f((f^^n) Bot)} &
             x isLUB {x. EX n. x =   (f^^n) Bot })"
apply (insert continuous_mono[of f])
apply (simp)

apply (simp add: continuous_iff)
apply (drule_tac x="{x. EX n. x = (f ^^ n) Bot}" in spec)
apply (simp add: Tarski_directed)
apply (erule exE)
apply (rule_tac x="x" in exI)
apply (simp add: Tarski_image_expand_lm)
done

(******)

lemma Tarski_LUB_lm:
  "(EX n. (x = ((f::('a::cpo_bot => 'a::cpo_bot)) ^^ n) Bot) )
   = ((EX n. x = (f ^^ (Suc n)) Bot) | x = Bot)"
apply (rule iffI)

(* ==> *)
apply (erule exE)
apply (insert nat_zero_or_Suc)
apply (drule_tac x="n" in spec)
apply (erule disjE)
apply (simp)

apply (erule exE)
apply (rule disjI1)
apply (rule_tac x="m" in exI)
apply (simp)

(* <== *)
apply (erule disjE)
apply (erule exE)
apply (rule_tac x="Suc n" in exI)
apply (simp)
apply (rule_tac x="0" in exI)
apply (simp)
done

(******)

lemma Tarski_LUB:
  "ALL (f::('a::cpo_bot => 'a::cpo_bot)) x.
    (x::'a::cpo_bot) isLUB {x. EX n. x = f((f^^n) Bot)} =
                   x isLUB {x. EX n. x =   (f^^n) Bot }"
apply (simp add: Tarski_LUB_lm LUB_with_Bot)
done

(******)

lemma Tarski_least_lm:
  "[| mono (f::('a::cpo_bot => 'a::cpo_bot)) ; y = f y |]
   ==> (f^^n) Bot <= y"
apply (induct_tac n)
apply (simp add: bottom_bot)
apply (simp add: mono_def)
apply (drule_tac x="(f ^^ n) Bot" in spec)
apply (drule_tac x="y" in spec)
by (simp)

lemma Tarski_least:
  "[| mono (f::('a::cpo_bot => 'a::cpo_bot)) ;
      x isLUB {x. EX n. x = (f^^n) Bot } ; y = f y |]
   ==> x <= y"
apply (simp add: isLUB_def)
apply (erule conjE)
apply (drule_tac x="y" in spec)
apply (drule mp)
apply (simp add: isUB_def)
apply (intro allI impI)
apply (erule exE)
apply (simp add: Tarski_least_lm)
by (assumption)

(*-------------------*
 |       Tarski      |
 *-------------------*)

theorem Tarski_thm:
  "continuous (f::('a::cpo_bot => 'a::cpo_bot)) ==>
    f hasLFP & LFP f isLUB {x. EX n. x = (f^^n) Bot}"
apply (insert Tarski_by_continuity[of f])
apply (simp add: Tarski_LUB)
apply (erule exE)

apply (subgoal_tac "x isLFP f")        (* ...1 *)
apply (simp add: isLFP_LFP hasLFP_def)
apply (rule_tac x="x" in exI, simp)

      (* 1 *)
apply (simp add: isLFP_def)
apply (erule conjE)
apply (simp add: LUB_unique)
apply (intro allI impI)
apply (rule Tarski_least[of f])
apply (simp_all add: continuous_mono)
done

(*-------------------*
 |    Tarski LUB     |
 *-------------------*)

theorem Tarski_thm_LFP_LUB:
  "continuous (f::('a::cpo_bot => 'a::cpo_bot)) ==>
    LFP f = LUB {x. EX n. x = (f^^n) Bot}"
apply (insert Tarski_thm[of f])
apply (auto simp add: isLUB_LUB)
done

(*--------------------*
 | Tarski (existency) |
 *--------------------*)

theorem Tarski_thm_EX:
  "continuous (f::('a::cpo_bot => 'a::cpo_bot)) ==> f hasLFP"
by (simp add: Tarski_thm)

(*========================================================*
 |           Fixed Point Induction (pointed CPO)          |
 *========================================================*)

theorem cpo_fixpoint_induction:
  "[| (R::'a::cpo_bot => bool) Bot ; continuous f ; admissible R ;
     inductivefun R f |]
   ==> f hasLFP & R (LFP f)"
apply (insert Tarski_thm[of f], simp)
apply (simp add: admissible_def)
apply (drule_tac x="{x. EX n. x = (f^^n) Bot }" in spec)
apply (simp add: Tarski_directed continuous_mono)
apply (auto simp add: inductivefun_all_n)
apply (simp add: isLUB_LUB)
done

theorem cpo_fixpoint_induction_R:
  "[| (R::'a::cpo_bot => bool) Bot ; continuous f ; admissible R ;
     inductivefun R f |]
   ==> R (LFP f)"
by (simp add: cpo_fixpoint_induction)

(*----------------------------------------------------------*
 |                                                          |
 |       Fixed point induction for refinement (CPO)         |
 |                                                          |
 *----------------------------------------------------------*)

(************************************************************
         admissibility lemma for refinement for cpo
 ************************************************************)

lemma admissible_Rev_fun: "admissible (Rev_fun X)"
apply (simp add: Rev_fun_def)
apply (simp add: admissible_def)
by (auto simp add: LUB_least complete_cpo)

(*** Bot ***)

lemma Rev_fun_Bot: "Rev_fun (X::'a::bot) Bot"
by (simp add: Rev_fun_def bottom_bot)

(************************************************************
         Fixed Point Induction (CPO) for refinement
 ************************************************************)

theorem cpo_fixpoint_induction_rev:
  "[| continuous f ; f X <= X |] 
   ==> LFP f <= (X::'a::cpo_bot)"
apply (insert cpo_fixpoint_induction[of "(Rev_fun X)" f])
apply (simp add: admissible_Rev_fun Rev_fun_Bot)
apply (subgoal_tac "inductivefun (Rev_fun X) f")
apply (simp add: Rev_fun_def)

      (* inductiveness *)
apply (simp add: inductivefun_def Rev_fun_def)
apply (intro allI impI)
apply (insert continuous_mono[of f])
apply (simp add: mono_def)
apply (drule_tac x="x" in spec)
apply (drule_tac x="X" in spec)
by (simp)

(*** EX version ***)

theorem cpo_fixpoint_induction_rev_EX:
  "[| continuous f ; f X <= X ; Y isLFP f |]
   ==> Y <= (X::'a::cpo_bot)"
apply (insert cpo_fixpoint_induction_rev[of f X])
by (auto simp add: isLFP_LFP)

(*****************************************************************)

end
