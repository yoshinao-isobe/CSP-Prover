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

theory Infra_pair
imports Infra_order
begin

(*****************************************************
                         Pair
 *****************************************************)

 (* Isabelle 2016
consts
  pair_fun :: "('x => 'y) => ('x => 'z) => ('x => ('y * 'z))" 
                                           ("(2_ **/ _)" [51,52] 52)
defs
  pair_fun_def : "f ** g == (%x. (f x, g x))"
*)

definition
  pair_fun :: "('x => 'y) => ('x => 'z) => ('x => ('y * 'z))" 
                                           ("(2_ **/ _)" [51,52] 52)
  where "f ** g == (%x. (f x, g x))"

(*** lemmas ***)

lemma fst_pair_fun[simp]: "fst o (f ** g) = f"
by (simp add: fun_eq_iff pair_fun_def)
(* by (simp add: expand_fun_eq pair_fun_def) *)

lemma snd_pair_fun[simp]: "snd o (f ** g) = g"
by (simp add: fun_eq_iff pair_fun_def)
(* by (simp add: expand_fun_eq pair_fun_def) *)

lemma pair_eq_decompo:
  "ALL (xc::('x * 'y)) (yc::('x * 'y)).
      (xc = yc) = ((fst xc = fst yc) & (snd xc = snd yc))"
by (simp)

lemma pair_neq_decompo:
  "ALL (xc::('x * 'y)) (yc::('x * 'y)).
      (xc ~= yc) = ((fst xc ~= fst yc) | (snd xc ~= snd yc))"
by (simp)

(*******************************
         <= in pair
 *******************************)

instantiation prod :: (order,order) ord 
(* instantiation "*" :: (order,order) ord  *)
begin
definition
  order_pair_def:
     "xc <= yc  ==  (fst xc <= fst yc) & (snd xc <= snd yc)"
definition
  order_less_pair_def:
     "xc <  yc  ==  (fst xc <= fst yc) & (snd xc <=  snd yc) &
                   ((fst xc ~= fst yc) | (snd xc ~=  snd yc))"
instance ..
end

(*
instance "*" :: (order,order) ord 
by (intro_classes)

defs
  order_pair_def:
     "xc <= yc  ==  (fst xc <= fst yc) & (snd xc <= snd yc)"
  order_less_pair_def:
     "xc <  yc  ==  (fst xc <= fst yc) & (snd xc <=  snd yc) &
                   ((fst xc ~= fst yc) | (snd xc ~=  snd yc))"
*)

(*** order in pair ***)

instance prod :: (order,order) order
(* instance * :: (order,order) order *)
apply (intro_classes)
apply (unfold order_pair_def order_less_pair_def)
apply (auto simp add: pair_neq_decompo)
done

(*** LUB is decomposed for * ***)

(* only if *)

lemma pair_LUB_decompo_fst_only_if:
  "xc isLUB (Xc::('x::order * 'y::order) set)
   ==> (fst xc isLUB fst ` Xc)"
apply (simp add: isLUB_def isUB_def)
apply (simp add: image_def)
apply (rule conjI)

      (* UB *)
apply (intro allI impI)
apply (simp add: order_pair_def)
apply (erule bexE)
apply (elim conjE)
apply (drule_tac x="fst x" in spec)
apply (drule_tac x="snd x" in spec)
apply (simp)

      (* LUB *)
apply (intro allI impI)
apply (simp add: order_pair_def)
apply (elim conjE)
apply (rotate_tac -1)
apply (drule_tac x="y" in spec)
apply (rotate_tac -1)
apply (drule_tac x="snd xc" in spec)
apply (drule mp)

 apply (intro allI impI)
 apply (drule_tac x="a" in spec)
 apply (drule mp)
  apply (rule_tac x="(a, b)" in bexI, simp)
 apply (simp)

 apply (drule_tac x="a" in spec)
 apply (drule_tac x="b" in spec)
 apply (simp)
 apply (simp)
done

lemma pair_LUB_decompo_snd_only_if:
  "xc isLUB (Xc::('x::order * 'y::order) set)
   ==> (snd xc isLUB snd ` Xc)"
apply (simp add: isLUB_def isUB_def)
apply (simp add: image_def)
apply (rule conjI)

      (* UB *)
apply (intro allI impI)
apply (simp add: order_pair_def)
apply (erule bexE)
apply (elim conjE)
apply (drule_tac x="fst x" in spec)
apply (drule_tac x="snd x" in spec)
apply (simp)

      (* LUB *)
apply (intro allI impI)
apply (simp add: order_pair_def)
apply (elim conjE)
apply (rotate_tac -1)
apply (drule_tac x="fst xc" in spec)
apply (rotate_tac -1)
apply (drule_tac x="y" in spec)
apply (drule mp)

 apply (intro allI impI)
 apply (drule_tac x="b" in spec)
 apply (drule mp)
  apply (rule_tac x="(a, b)" in bexI, simp)
 apply (simp)

 apply (drule_tac x="a" in spec)
 apply (drule_tac x="b" in spec)
 apply (simp)
 apply (simp)
done

(* if *)

lemma pair_LUB_decompo_if:
  "(fst xc isLUB fst ` Xc) & (snd xc isLUB snd ` Xc)
          ==> xc isLUB (Xc::('x::order * 'y::order) set)"
apply (simp add: isLUB_def isUB_def)
apply (simp add: image_def)
apply (rule conjI)

apply (intro allI impI)
apply (simp add: order_pair_def)
apply (elim conjE)
apply (drule_tac x="a" in spec)
apply (drule mp)
apply (rule_tac x="(a, b)" in bexI)
apply (simp)
apply (simp)

apply (rotate_tac 1)
apply (drule_tac x="b" in spec)
apply (drule mp)
apply (rule_tac x="(a, b)" in bexI)
apply (simp)
apply (simp)
apply (simp)

(*** least ***)

apply (intro allI impI)
apply (elim conjE)
apply (rotate_tac 2)
apply (drule_tac x="a" in spec)
apply (rotate_tac 1)
apply (drule_tac x="b" in spec)

apply (drule mp)
apply (intro allI impI)
apply (erule bexE)
apply (drule_tac x="y" in spec)
apply (rotate_tac -1)
apply (drule_tac x="snd x" in spec)
apply (simp add: order_pair_def)

apply (drule mp)
apply (intro allI impI)
apply (erule bexE)
apply (drule_tac x="fst x" in spec)
apply (rotate_tac -1)
apply (drule_tac x="y" in spec)
apply (simp add: order_pair_def)

apply (simp add: order_pair_def)
done

(* iff *)

lemma pair_LUB_decompo:
  "xc isLUB (Xc::('x::order * 'y::order) set)
   = ((fst xc isLUB fst ` Xc) & (snd xc isLUB snd ` Xc))"
apply (rule iffI)
apply (simp add: pair_LUB_decompo_fst_only_if pair_LUB_decompo_snd_only_if)
apply (simp add: pair_LUB_decompo_if)
done

end
