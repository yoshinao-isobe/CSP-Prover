           (*-------------------------------------------*
            |                CSP-Prover                 |
            |               December 2004               |
            |                                           |
            |        CSP-Prover on Isabelle2009-2       |
            |                October 2010  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CPO_prod
imports CPO
begin

(*****************************************************************

         1. Productions of CPO are also CPO.
         2. 
         3. 
         4. 

 *****************************************************************)

(********************************************************** 
              def: prod of bot
 **********************************************************)

instantiation "fun" :: (type, bot) bot0
begin

definition
  prod_Bot_def : "Bot == (%i. Bot)"
  instance proof qed
end

(*  isabelle 2009-1

instance "fun" :: (type, bot) bot0
apply (intro_classes)
done

defs (overloaded)
  prod_Bot_def : "Bot == (%i. Bot)"
*)

(************************************************************
                   Product bot ==> bot
 ************************************************************)

(*** prod Bot ***)

lemma prod_Bot:
  "ALL (x::('i => 'x::bot)). Bot <= x"
apply (simp add: le_fun_def)
apply (simp add: prod_Bot_def)
apply (simp add: bottom_bot)
done

(*****************************
       Prod bot => bot
 *****************************)

instance "fun" :: (type,bot) bot
apply (intro_classes)
by (simp add: prod_Bot)

(*

instantiation "fun" :: (type, bot) bot
begin

definition
  prod_Bot_def : "Bot == (%i. Bot)"

  instance proof
  fix x :: "'a => 'b"
  show "Bot <= x"
   apply (simp add: prod_Bot_def)
   apply (simp add: le_fun_def)
   apply (auto simp add: bottom_bot)
   done
  qed

end
*)



(************************************************************
                   Product CPO ==> CPO
 ************************************************************)

(*** prod directed decompo ***)

lemma prod_directed_decompo:
  "directed (Xp::('i => 'x::cpo) set) ==> ALL i. directed {xp i |xp. xp : Xp}"
apply (simp add: directed_def)
apply (intro allI impI)
apply (elim conjE exE)
apply (rename_tac i x y xp yp)

apply (drule_tac x="xp" in spec)
apply (drule_tac x="yp" in spec)
apply (simp)
apply (elim conjE exE)

apply (rule_tac x="z i" in exI)
by (auto simp add: le_fun_def)

(*** prod cpo lemma ***)

lemma prod_cpo_lm:
  "directed (Xp::('i => 'x::cpo) set) ==> (EX x. x isLUB Xp)"
apply (rule_tac x="(%i. LUB {xp i |xp. xp : Xp})" in exI)
apply (simp add: prod_LUB_decompo)
apply (intro allI)

apply (insert prod_directed_decompo[of Xp])
apply (simp)
apply (drule_tac x="i" in spec)

apply (simp add: proj_fun_def)

apply (insert complete_cpo_lm)
apply (drule_tac x="{xp i |xp. xp : Xp}" in spec)
apply (subgoal_tac "(%x. x i) ` Xp = {xp i |xp. xp : Xp}")
apply (simp add: LUB_is)

by (auto)

(*****************************
       Prod CPO => CPO
 *****************************)

instance "fun" :: (type,cpo) cpo
apply (intro_classes)
by (simp add: hasLUB_def prod_cpo_lm)

(************************************************************
                Product CPO_BOT ==> CPO_BOT
 ************************************************************)

instance "fun" :: (type,cpo_bot) cpo_bot
by (intro_classes)

(************************************************************
                   Project continuity
 ************************************************************)

lemma proj_continuous: "continuous (proj_fun i)"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (insert complete_cpo_lm)
apply (drule_tac x="X" in spec)
apply (simp add: hasLUB_def)

apply (erule exE)
apply (rule_tac x="x" in exI)
apply (simp add:  prod_LUB_decompo)
done

(************************************************************
                   Product continuity
 ************************************************************)

lemma prod_continuous_only_if: 
  "continuous (h :: (('x::cpo) => ('i =>('y::cpo))))
   ==> continuous ((proj_fun i) o h)"
by (simp add: proj_continuous compo_continuous)

lemma prod_continuous_if: 
  "(ALL i. continuous ((proj_fun i) o h)) 
   ==> continuous (h :: (('x::cpo) => ('i =>('y::cpo))))"
apply (simp add: continuous_iff)
apply (insert complete_cpo_lm)
apply (intro allI impI)
apply (drule_tac x="X" in spec)
apply (simp add: hasLUB_def)

apply (erule exE)
apply (rule_tac x="x" in exI)
apply (simp)

apply (simp add: prod_LUB_decompo)
apply (intro allI)
apply (drule_tac x="i" in spec)
apply (drule_tac x="X" in spec)
apply (simp)

apply (erule exE)
apply (subgoal_tac "xa = x")
(* apply (simp add: image_compose) *)
apply (simp add: image_comp)
apply (erule conjE)
by (simp add: LUB_unique)

lemma prod_continuous: 
  "continuous (h :: (('x::cpo) => ('i =>('y::cpo))))
   = (ALL i. continuous ((proj_fun i) o h))"
apply (rule iffI)
apply (simp add: prod_continuous_only_if)
apply (simp add: prod_continuous_if)
done

(************************************************************
                    prod_variable continuity
 ************************************************************)

lemma continuous_prod_variable: "continuous (%f. f pn)"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (insert complete_cpo_lm)
apply (drule_tac x="X" in spec, simp)
apply (simp add: hasLUB_def)
apply (erule exE)
apply (rule_tac x="x" in exI, simp)

apply (simp add: prod_LUB_decompo)
apply (drule_tac x="pn" in spec)
apply (simp add: proj_fun_def)
done

end

