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
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2020         |
            |                  April 2020  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CPO_pair
imports CPO
begin

(*****************************************************************

         1. Pairs of CPO are also CPO.
         2. 
         3. 
         4. 

 *****************************************************************)

(*  Take care the following rules automatically applied                *)
(*                                                                     *)
(*          split_paired_Ex:  (EX x. P x) = (EX a b. P (a, b))         *)
(*          split_paired_All: (ALL x. P x) = (ALL a b. P (a, b))       *)

(********************************************************** 
              def: pair of bot
 **********************************************************)

instantiation prod :: (bot, bot) bot0
begin

definition
  pair_Bot_def : "Bot == (Bot, Bot)"

instance ..

end

(* isabelle 2009-1
defs (overloaded)
  pair_Bot_def : "Bot == (Bot, Bot)"
*)

(************************************************************
                   Pairuct bot ==> bot
 ************************************************************)

(*** pair Bot ***)

lemma pair_Bot:
  "ALL (x::('x::bot * 'y::bot)). Bot <= x"
apply (simp add: order_pair_def)
by (auto simp add: pair_Bot_def bottom_bot)

(*****************************
       Pair bot => bot
 *****************************)

instance prod :: (bot, bot) bot
apply (intro_classes)
by (simp add: pair_Bot)

(*
definition
  pair_Bot_def : "Bot == (Bot, Bot)"

  instance proof
  fix x :: "'a * 'b"
  show "Bot <= x"
   apply (simp add: pair_Bot_def)
   apply (simp add: order_pair_def)
   apply (auto simp add: bottom_bot)
   done
  qed
*)

(************************************************************
                   Pair CPO ==> CPO
 ************************************************************)

(*** pair directed decompo ***)

declare split_paired_Ex  [simp del]
declare split_paired_All [simp del]

lemma pair_directed_decompo_fst:
  "directed (Xc::('x::cpo * 'y::cpo) set) ==> directed (fst ` Xc)"
apply (simp add: directed_def)
apply (intro allI impI)
apply (simp add: in_image_set)
apply (elim conjE exE)
apply (drule_tac x="ya" in spec)
apply (drule_tac x="yb" in spec)
apply (simp)

apply (elim conjE exE)
apply (rule_tac x="z" in bexI)
apply (auto simp add: order_pair_def)
done

lemma pair_directed_decompo_snd:
  "directed (Xc::('x::cpo * 'y::cpo) set) ==> directed (snd ` Xc)"
apply (simp add: directed_def)
apply (intro allI impI)
apply (simp add: in_image_set)
apply (elim conjE exE)
apply (drule_tac x="ya" in spec)
apply (drule_tac x="yb" in spec)
apply (simp)

apply (elim conjE exE)
apply (rule_tac x="z" in bexI)    (* modified for Isabelle2020 *)
apply (auto simp add: order_pair_def)
done

declare split_paired_Ex  [simp]
declare split_paired_All [simp]

(*** pair cpo lemma ***)

lemma pair_cpo_lm:
  "directed (Xc::('x::cpo * 'y::cpo) set) ==> Xc hasLUB"
apply (simp add: hasLUB_def)
apply (rule_tac x="LUB (fst ` Xc)" in exI)
apply (rule_tac x="LUB (snd ` Xc)" in exI)
apply (simp add: pair_LUB_decompo)

apply (insert pair_directed_decompo_fst[of Xc])
apply (insert pair_directed_decompo_snd[of Xc])
apply (simp)

apply (insert complete_cpo_lm)
apply (drule_tac x="fst ` Xc" in spec)
apply (insert complete_cpo_lm)
apply (drule_tac x="snd ` Xc" in spec)
by (simp add: isLUB_to_LUB)

(*****************************
       Pair CPO => CPO
 *****************************)

instance prod :: (cpo,cpo) cpo
apply (intro_classes)
by (simp add: pair_cpo_lm del: split_paired_Ex)

(************************************************************
                Pairuct CPO_BOT ==> CPO_BOT
 ************************************************************)

instance prod :: (cpo_bot,cpo_bot) cpo_bot
by (intro_classes)

(************************************************************
                     fst continuity
 ************************************************************)

lemma fst_continuous: "continuous fst"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (insert complete_cpo_lm)
apply (drule_tac x="X" in spec)
apply (simp add: hasLUB_def)

apply (elim exE)
apply (rule_tac x="a" in exI)
apply (simp add: pair_LUB_decompo)
apply (rule_tac x="b" in exI)
by (simp)

lemma snd_continuous: "continuous snd"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (insert complete_cpo_lm)
apply (drule_tac x="X" in spec)
apply (simp add: hasLUB_def)

apply (elim exE)
apply (rule_tac x="a" in exI)
apply (rule_tac x="b" in exI)
by (simp add: pair_LUB_decompo)

(************************************************************
                   Pair continuity
 ************************************************************)

lemma pair_continuous_only_if: 
  "continuous h
   ==> (continuous (fst o h) & continuous (snd o h))"
by (simp add: fst_continuous snd_continuous compo_continuous)

lemma pair_continuous_if: 
  "[| continuous (fst o h) ; continuous (snd o h) |]
   ==> continuous h"
apply (simp add: continuous_iff)
apply (insert complete_cpo_lm)
apply (intro allI impI)
apply (drule_tac x="X" in spec)
apply (simp)

apply (erule exE)
apply (rule_tac x="x" in exI)
apply (simp)

apply (simp add: pair_LUB_decompo)
apply (erule conjE)
apply (drule_tac x="X" in spec)
apply (drule_tac x="X" in spec)
apply (simp)

apply (elim exE)
(* apply (simp add: image_compose) *)
apply (simp add: image_comp)
apply (subgoal_tac "x = xa", simp)
by (simp add: LUB_unique)

lemma pair_continuous: 
  "continuous h = (continuous (fst o h) & continuous (snd o h))"
apply (rule iffI)
apply (simp add: pair_continuous_only_if)
apply (simp add: pair_continuous_if)
done

end

