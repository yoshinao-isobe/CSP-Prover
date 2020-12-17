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
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory RS_prod
imports RS
begin

(*****************************************************************

         1. Productions of RS are also RS.
         2. 
         3. 
         4. 

 *****************************************************************)

(********************************************************** 
              def: prod of restriction space
 **********************************************************)


instantiation "fun" :: (type, rs) rs0
begin

definition
  prod_restriction_def : 
(*    "xp .|. n == (%i. ((xp i) .|. n))" *)
      "(xp::('a::type => 'b::rs)) .|. n == (%i. ((xp i) .|. n))"  (* note the name of type variable *)

  instance proof qed
end

definition
  prod_Limit :: "(('i => 'a::ms_rs) infinite_seq) => ('i => 'a::ms_rs)"
  where
  prod_Limit_def :"prod_Limit xps == (%i. Limit ((proj_fun i) o xps))"

(************************************************************
                           Basics
 ************************************************************)

lemma rest_to_prod_rest:
    "(ALL i. ((xp::('i => 'a::rs)) i) .|. n = (yp i) .|. n) 
     ==> xp .|. n = yp .|. n"
by (simp add: prod_restriction_def)

(************************************************************
                     Product RS ==> RS 
 ************************************************************)

(*** prod_zero_eq_rs ***)

lemma prod_zero_eq_rs:
  "(xp::('i => 'a::rs)) .|. 0 = yp .|. 0"
apply (simp add: prod_restriction_def)
by (simp add: fun_eq_iff)
(* by (simp add: expand_fun_eq) *)

(*** prod_min_rs ***)

lemma prod_min_rs: 
  "((xp::('i => 'a::rs)) .|. m) .|. n = xp .|. (min m n)"
apply (simp add: prod_restriction_def)
apply (simp add: fun_eq_iff)
(* apply (simp add: expand_fun_eq) *)
by (simp add: min_rs)

(*** prod_diff_rs ***)

lemma prod_diff_rs: 
  "((xp::('i => 'a::rs)) ~= yp) ==> (EX n. xp .|. n ~= yp .|. n)"
apply (simp add: prod_restriction_def)
apply (simp add: fun_eq_iff)
(* apply (simp add: expand_fun_eq) *)
apply (erule exE)

apply (insert diff_rs)
apply (drule_tac x="xp x" in spec)
apply (drule_tac x="yp x" in spec)
by (auto)

(*****************************
       Prod RS => RS
 *****************************)

instance "fun" :: (type,rs) rs
apply (intro_classes)
apply (simp add: prod_zero_eq_rs)
apply (simp add: prod_min_rs)
apply (simp add: prod_diff_rs)
done

(************************************************************
                   Product RS ==> MS 
 ************************************************************)


instantiation "fun" :: (type, rs) ms0
begin

definition
  prod_distance_def: "distance (f::(('a=>'b::rs)*('a=>'b::rs))) = distance_rs f"

  instance proof qed
end


instance "fun" :: (type,rs) ms
apply (intro_classes)
apply (simp_all add: prod_distance_def)
apply (simp add: diagonal_rs)
apply (simp add: symmetry_rs)
apply (simp add: triangle_inequality_rs)
done

(************************************************************
             i.e.  Product RS ==> MS & RS 
 ************************************************************)

instance "fun" :: (type,rs) ms_rs
apply (intro_classes)
apply (simp add: prod_distance_def)
done

(************************************************************
                    distance
 ************************************************************)

lemma prod_distance_nat_le:
      "xp i ~= yp i
       ==> distance_nat ((xp::('i => 'a::rs)), yp)
        <= distance_nat (xp i, yp i)"
apply (case_tac "xp = yp", simp)
apply (simp add: distance_nat_le_1[THEN sym])

apply (insert distance_nat_is[of xp yp], simp)
apply (simp add: isMAX_def)
apply (simp add: distance_nat_set_def)
apply (simp add: prod_restriction_def)
by (simp add: fun_eq_iff)
(* by (simp add: expand_fun_eq) *)

lemma prod_distance_def_le:
      "distance (xp i, yp i) <= distance ((xp::('i => 'a::ms0_rs)), yp)"
apply (case_tac "xp i = yp i", simp)
apply (case_tac "xp = yp", simp)
apply (simp_all add: to_distance_rs)
apply (case_tac "xp = yp", simp)
apply (simp add: distance_iff)
(* apply (rule power_decreasing, simp_all)    not necessary for Isabelle2020 *)
by (simp add: prod_distance_nat_le)

(*** prod_distance (Upper Bound) ***)

lemma prod_distance_UB: 
  "distance((xp::('i => 'a::ms0_rs)), yp) isUB {u. EX i. u = distance (xp i, yp i)}"
apply (simp add: isUB_def)
apply (intro allI impI)
apply (erule exE)
by (simp add: prod_distance_def_le)

(*** prod_distance (Least) ***)

lemma prod_distance_least: 
   "ALL i. distance (xp i, yp i) <= u
    ==> distance((xp::('i => 'a::ms0_rs)), yp) <= u"
apply (case_tac "xp = yp")
apply (simp add: to_distance_rs)

(* to use a contradiction *)
apply (case_tac "distance (xp, yp) <= u", simp)
apply (simp add: linorder_not_le)

 apply (insert rest_to_prod_rest[of xp "Suc (distance_nat (xp, yp))" yp])
 apply (subgoal_tac "ALL i. xp i .|. Suc (distance_nat (xp, yp)) =
                            yp i .|. Suc (distance_nat (xp, yp))") (* ...1 *)
 apply (simp add: distance_nat_less_1)

  apply (rule allI)
  apply (case_tac "xp i = yp i", simp)
  apply (drule_tac x="i" in spec)
  apply (simp add: to_distance_rs)
  apply (simp add: distance_iff)
  apply (simp add: distance_nat_less_1)
  apply (rule rev_power_decreasing_strict[of "1/2"])
  apply (simp)
  apply (simp)
  apply (rule le_less_trans)   (* modified for Isabelle2020 *)
  apply (simp)
  apply (simp)
done

(*** prod_distance (Least Upper Bound) ***)

lemma prod_distance: 
   "distance((xp::('i => 'a::ms0_rs)), yp) isLUB {u. EX i. u = distance (xp i, yp i)}"
apply (simp add: isLUB_def)
apply (simp add: prod_distance_UB)

apply (intro allI impI)
apply (rule prod_distance_least)
apply (simp add: isUB_def)
apply (rule allI)
apply (drule_tac x="distance (xp i, yp i)" in spec)
apply (auto)
done

lemma ALL_prod_distance: 
   "ALL xp yp.
    distance((xp::('i => 'a::ms0_rs)), yp) isLUB {u. EX i. u = distance (xp i, yp i)}"
by (simp add: prod_distance)

(*************************************************************
                        product maps
 *************************************************************)

(*** proj_fun ***)

lemma proj_non_expand: "non_expanding ((proj_fun::('i => ('i => 'a::ms_rs) => 'a)) i)"
apply (simp add: non_expanding_def)
apply (simp add: map_alpha_def)
apply (simp add: proj_fun_def)
apply (simp add: prod_distance_def_le)
done

(*---------------------*
 |    non_expanding    |
 *---------------------*)

(* only_if *)

lemma prod_non_expand_only_if:
  "non_expanding (fp::('a::ms_rs => ('i => 'b::ms_rs)))
   ==> ALL i. non_expanding ((proj_fun i) o fp)"
by (simp add: compo_non_expand proj_non_expand)

(* if *)

lemma prod_non_expand_if:
  "ALL i. non_expanding ((proj_fun i) o fp)
   ==> non_expanding (fp::('a::ms_rs => ('i => 'b::ms_rs)))"
apply (simp add: non_expanding_def map_alpha_def)
apply (intro allI)
apply (insert ALL_prod_distance)
apply (drule_tac x="fp x" in spec)
apply (drule_tac x="fp y" in spec)
apply (simp add: isLUB_def)
apply (erule conjE)
apply (drule_tac x="distance (x, y)" in spec)
apply (drule mp)

 apply (simp add: isUB_def)
 apply (intro allI impI)
 apply (erule exE)
 apply (drule_tac x="i" in spec)
 apply (drule_tac x="x" in spec)
 apply (drule_tac x="y" in spec)
 apply (simp add: proj_fun_def)

by (simp)

(* iff *)

lemma prod_non_expand:
  "non_expanding (fp::('a::ms_rs => ('i => 'b::ms_rs)))
   = (ALL i. non_expanding ((proj_fun i) o fp))"
apply (rule iffI)
apply (simp add: prod_non_expand_only_if)
apply (simp add: prod_non_expand_if)
done

(*---------------------*
 |  alpha_contraction  |
 *---------------------*)

(* only_if *)

lemma prod_contra_alpha_only_if:
  "contraction_alpha (fp::('a::ms_rs => ('i => 'b::ms_rs))) alpha
   ==> ALL i. contraction_alpha ((proj_fun i) o fp) alpha"
by (simp add: compo_non_expand_contra_alpha proj_non_expand)

(* if *)

lemma prod_contra_alpha_if:
  "ALL i. contraction_alpha ((proj_fun i) o fp) alpha
   ==> contraction_alpha (fp::('a::ms_rs => ('i => 'b::ms_rs))) alpha"
apply (simp add: contraction_alpha_def map_alpha_def)
apply (intro allI)
apply (insert ALL_prod_distance)
apply (drule_tac x="fp x" in spec)
apply (drule_tac x="fp y" in spec)
apply (simp add: isLUB_def)
apply (elim conjE)
apply (drule_tac x="alpha * distance (x, y)" in spec)
apply (drule mp)

 apply (simp add: isUB_def)
 apply (intro allI impI)
 apply (erule exE)
 apply (drule_tac x="i" in spec)
 apply (drule_tac x="x" in spec)
 apply (drule_tac x="y" in spec)
 apply (simp add: proj_fun_def)

by (simp)

(* iff *)

lemma prod_contra_alpha:
  "contraction_alpha (fp::('a::ms_rs => ('i => 'b::ms_rs))) alpha
   = (ALL i. contraction_alpha ((proj_fun i) o fp) alpha)"
apply (rule iffI)
apply (simp add: prod_contra_alpha_only_if)
apply (simp add: prod_contra_alpha_if)
done

(************************************************************
                       Lemmas (limit)
 ************************************************************)

(*** cauchy ***)

lemma prod_cauchy_seq:
  "cauchy (xps::(('i => 'b::ms_rs) infinite_seq)) 
   ==> cauchy ((proj_fun i) o xps)"
apply (simp add: cauchy_def)
apply (intro allI impI)

apply (drule_tac x="delta" in spec)
apply (simp)
apply (erule exE)
apply (rule_tac x="n" in exI)
apply (intro allI impI)
apply (rename_tac delta N n m)
apply (drule_tac x="n" in spec)
apply (drule_tac x="m" in spec)
apply (simp add: proj_fun_def)

apply (insert ALL_prod_distance)
apply (drule_tac x="xps n" in spec)
apply (drule_tac x="xps m" in spec)

apply (simp add: isLUB_def)
apply (simp add: isUB_def)
apply (erule conjE)+
apply (drule_tac x="distance ((xps n) i, (xps m) i)" in spec)
apply (drule mp)

apply (rule_tac x="i" in exI)
by (simp_all)

(*** normal ***)

lemma prod_normal_seq:
  "normal (xps::(('i => 'b::ms_rs) infinite_seq)) 
    ==> normal ((proj_fun i) o xps)"
apply (simp add: normal_def)
apply (intro allI)

apply (drule_tac x="n" in spec)
apply (drule_tac x="m" in spec)
apply (simp add: proj_fun_def)

apply (insert ALL_prod_distance)
apply (drule_tac x="xps n" in spec)
apply (drule_tac x="xps m" in spec)

apply (simp add: isLUB_def)
apply (simp add: isUB_def)
apply (erule conjE)+
apply (drule_tac x="distance ((xps n) i, (xps m) i)" in spec)
apply (drule mp)

apply (rule_tac x="i" in exI)
by (simp_all)

lemma prod_normal_seq_only_if:
  "ALL i. normal ((proj_fun i) o xps)
    ==> normal (xps::(('i => 'b::ms_rs) infinite_seq))"
apply (simp add: normal_def)
apply (intro allI)
apply (rule prod_distance_least)
apply (intro allI)
apply (drule_tac x="i" in spec)
apply (drule_tac x="n" in spec)
apply (drule_tac x="m" in spec)
apply (simp add: proj_fun_def)
done

(* iff *)

lemma prod_normal_seq_iff:
  "normal (xps::(('i => 'b::ms_rs) infinite_seq))
   = (ALL i. normal ((proj_fun i) o xps))"
apply (rule)
apply (simp add: prod_normal_seq)
apply (simp add: prod_normal_seq_only_if)
done

(*-----------------------*
 |   product of limits   |
 *-----------------------*)

(*** limit (single <-- prod) ***)

lemma prod_convergeTo_only_if:
  "(xps::(('i => 'b::ms_rs) infinite_seq)) convergeTo yp 
   ==> ALL i. ((proj_fun i) o xps) convergeTo (yp i)"
apply (simp add: convergeTo_def)
apply (intro allI impI)

apply (drule_tac x="eps" in spec)
apply (simp)
apply (erule exE)
apply (rule_tac x="n" in exI)
apply (intro allI impI)
apply (rename_tac i eps N n)
apply (drule_tac x="n" in spec)
apply (simp add: proj_fun_def)

apply (insert ALL_prod_distance)
apply (drule_tac x="yp" in spec)
apply (drule_tac x="xps n" in spec)
apply (simp add: isLUB_def isUB_def)

apply (erule conjE)+
apply (drule_tac x="distance (yp i, (xps n) i)" in spec)
apply (drule mp)

apply (rule_tac x="i" in exI)
by (simp_all)

(*** limit (single --> prod) (note: ms_rs) ***)

lemma prod_convergeTo_if:
  "[| normal xps ; ALL i. ((proj_fun i) o xps) convergeTo (yp i) |]
   ==> (xps::(('i => 'b::ms_rs) infinite_seq)) convergeTo yp"
apply (simp (no_asm) add: convergeTo_def)
apply (intro allI impI)

apply (subgoal_tac "EX n. ((1::real)/2) ^ n < eps")  (* ...1 *)
 apply (erule exE)
 apply (rename_tac eps M)

 apply (rule_tac x="Suc M" in exI)
 apply (intro allI impI)

 apply (insert ALL_prod_distance)
 apply (drule_tac x="yp" in spec)
 apply (drule_tac x="xps m" in spec)

 apply (simp add: isLUB_def)
 apply (erule conjE)+
 apply (drule_tac x="(1 / 2) ^ M" in spec)
 apply (drule mp)  (* mp *)

  apply (simp add: isUB_def)
  apply (intro allI impI)
  apply (erule exE)
  apply (simp)
  apply (drule_tac x="i" in spec)

  apply (subgoal_tac "EX n. M <= n & m = Suc n")  (* ...2 *)
   apply (erule exE)
   apply (simp)

   apply (subgoal_tac "distance((proj_fun i o xps) (Suc n), yp i) < (1/2)^n") (* ...3 *)
   apply (simp add: proj_fun_def)

   apply (subgoal_tac "distance (xps (Suc n) i, yp i) = distance (yp i, xps (Suc n) i)") 
     (* added for Isabelle2020 *)(* 4 *)
    apply (simp)
    apply (rule less_imp_le)
    apply (rule less_le_trans[of _ "(1/2) ^ _"])
    apply (simp)
    apply (simp)
    (* 4 *)
    apply (simp add: symmetry_ms)

   (* 3 *)
   apply (rule normal_Limit)
   apply (simp add: prod_normal_seq del: o_apply)
   apply (simp del: o_apply)

  (* 2 *)
  apply (insert nat_zero_or_Suc)
  apply (drule_tac x="m" in spec)
  apply (erule disjE, simp)
  apply (erule exE)
  apply (rule_tac x="ma" in exI)
  apply (simp)

 (* mp *)
 apply (simp)

(* 1 *)
by (simp add: pow_convergence)

(*** iff ***)

lemma prod_convergeTo:
  "normal xps
   ==> (xps::(('i => 'b::ms_rs) infinite_seq)) convergeTo yp 
     = (ALL i. ((proj_fun i) o xps) convergeTo (yp i))"
apply (rule iffI)
apply (simp add: prod_convergeTo_only_if)
apply (simp add: prod_convergeTo_if)
done

(*****************************************
      limit (cms and normal --> limit)
 *****************************************)

lemma prod_cms_normal_Limit:
  "normal (xps::(('i => 'b::cms_rs) infinite_seq))
   ==> xps convergeTo prod_Limit xps"
apply (simp add: prod_convergeTo prod_Limit_def)
by (simp add: prod_normal_seq normal_cauchy Limit_is)

(*****************************************
      limit (cms and cauchy --> limit)
 *****************************************)

lemma prod_cms_cauchy_Limit:
  "cauchy (xps::(('i => 'b::cms_rs) infinite_seq))
   ==> xps convergeTo prod_Limit (NF xps)"
by (simp add: prod_cms_normal_Limit normal_form_seq_normal 
              normal_form_seq_same_Limit)

(*****************************************
     Product Complete Metric Space (RS)
 *****************************************)

lemma prod_cms_rs:
  "cauchy (xps::(('i => 'b::cms_rs) infinite_seq)) 
   ==> (EX yp. xps convergeTo yp)"
apply (rule_tac x="prod_Limit (NF xps)" in exI)
by (simp add: prod_cms_cauchy_Limit)

(************************************************************
                   Product RS ==> CMS and RS
 ************************************************************)

instance "fun" :: (type,cms_rs) cms
apply (intro_classes)
by (simp add: prod_cms_rs)

instance "fun" :: (type,cms_rs) cms_rs
by (intro_classes)

(************************************************************
                       prod_variable 
 ************************************************************)

lemma non_expanding_prod_variable:
  "non_expanding (%(f::('i => 'a::ms_rs)). f pn)"
apply (simp add: non_expanding_def map_alpha_def)
apply (simp add: prod_distance_def_le)
done

(************************************************************
               Banach theorem for production
 ************************************************************)

theorem Banach_thm_prod:
  "[| normal (%n. (f^^n) x0) ;
      contraction (f::(('i => 'a::cms_rs) => ('i => 'a))) |]
     ==> f hasUFP & (ALL i. (%n. (f^^n) x0 i) convergeTo (UFP f) i)"
apply (insert Banach_thm[of f x0])
apply (simp)
apply (erule conjE)
apply (rule allI)
apply (simp add: prod_convergeTo)
apply (drule_tac x="i" in spec)
apply (simp add: proj_fun_def)
apply (simp add: comp_def)
done

(*----------------------------------------------------------*
 |                                                          |
 |                Continuity on Metric space                |
 |                                                          |
 *----------------------------------------------------------*)

lemma prod_continuous_rs:
  "(ALL i. continuous_rs (R i)) 
       ==> continuous_rs (%xp. (ALL i. (R i) (xp i)))"
apply (simp add: continuous_rs_def)
apply (intro allI impI)
apply (erule exE)
apply (drule_tac x="i" in spec)
apply (drule_tac x="x i" in spec)
apply (simp)

apply (erule exE)
apply (rule_tac x="n" in exI)
apply (intro allI impI)
apply (drule_tac x="y i" in spec)
apply (rule_tac x="i" in exI)
apply (simp add: prod_restriction_def)
apply (simp add: fun_eq_iff)
(* apply (simp add: expand_fun_eq) *)
done

(*----------------------------------------------------------*
 |                                                          |
 |      !!!     order and restriction space     !!!         |
 |                                                          |
 *----------------------------------------------------------*)

instance "fun" :: (type,ms_rs_order) ms_rs_order0
by (intro_classes)

instance "fun" :: (type,ms_rs_order) ms_rs_order
apply (intro_classes)
apply (simp add: le_fun_def prod_restriction_def)
apply (intro allI)
apply (rule iffI)
apply (intro allI)
apply (erule exchange_forall_orderE)
apply (drule_tac x="xa" in spec)
apply (simp add: rs_order_iff)

apply (intro allI)
apply (drule_tac x="xa" in spec)
apply (insert rs_order_iff)
apply (drule_tac x="x xa" in spec)
apply (drule_tac x="y xa" in spec)
apply (fast)
done

(*** cms rs order ***)

instance "fun" :: (type,cms_rs_order) cms_rs_order
by (intro_classes)

end
