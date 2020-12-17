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
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |

            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Domain_T_cms
imports Domain_T CSP.RS
begin

(*****************************************************************

         1. 
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

(**********************************************************
           Definitions (Restriction in domT)
 **********************************************************)

(*
instance domT :: (type) ms0
by (intro_classes)
*)

definition
  restT      :: "'a domT => nat => 'a trace set" ("_ restT _" [84,900] 84)
  where
  restT_def  : "T restT n == {s. s :t T & (lengtht s) <= n}"

(* ("_ restT _" [55,56] 55) in Isabelle 2005 *)

definition
  LimitT     :: "'a domT infinite_seq => 'a trace set"
  where
  LimitT_def : "LimitT Ts == {s. s :t Ts (lengtht s)}"
  
definition  
  Limit_domT :: "'a domT infinite_seq => 'a domT"
  where
  Limit_domT_def    : "Limit_domT Ts    == Abs_domT (LimitT Ts)"

(* isabelle 2009-2 *)

instantiation domT :: (type) rs0
begin

definition
  rest_domT_def : "T .|. n == Abs_domT (T restT n)"

  instance ..

end

(* isabelle 2009-1
defs (overloaded)
  rest_domT_def : "T .|. n == Abs_domT (T restT n)"
*)



(**********************************************************
              Lemmas (Restriction in Dom_T)
 **********************************************************)

(*** restT_def in domT ***)

lemma restT_in[simp] : "T restT n : domT"
apply (simp add: restT_def)
apply (simp add: domT_def HC_T1_def)
apply (rule conjI)
apply (rule_tac x="<>" in exI, simp)

apply (simp add: prefix_closed_def)
apply (intro allI impI)
apply (elim conjE exE)

apply (rule conjI)
apply (rule memT_prefix_closed, simp_all)

apply (subgoal_tac "lengtht s <= lengtht t", simp)
apply (rule length_of_prefix)
apply (simp)
done

(*** restT in domT ***)

lemmas restT_def_in = restT_in[simplified memT_def restT_def]

(*********************************************************
                     .|. on dom_T
 *********************************************************)

lemma rest_domT_iff: "T .|. n = {s. s :t T & lengtht s <= n}t"
apply (simp add: rest_domT_def)
apply (simp add: restT_in[simplified restT_def] Abs_domT_inject)
apply (simp add: restT_def)
done

lemma in_rest_domT: "s :t T .|. n = (s :t T & lengtht s <= n)"
apply (simp add: memT_def rest_domT_def)
apply (simp add: Abs_domT_inverse)
apply (simp add: memT_def restT_def)
done

lemma rest_domT_eq_iff:
   "(T .|. n = S .|. m) =
    (ALL s. (s :t T & lengtht s <= n) = (s :t S & lengtht s <= m))"
apply (simp add: rest_domT_def Abs_domT_inject)
apply (simp add: restT_def)
by (auto)

(*********************************************************
                     Dom_T --> RS
 *********************************************************)

(*******************************
        zero_eq_rs_domT
 *******************************)

(*** restT 0 ***)

lemma zero_domT: "T restT 0 = {<>}"
apply (simp add: restT_def)
apply (rule order_antisym)

apply (rule subsetI)
apply (simp)
apply (erule conjE)
apply (simp add: lengtht_zero)
by (simp)

(*** zero_eq_rs_domT ***)

lemma zero_rs_domT: "T .|. 0 = {<>}t"
apply (simp add: rest_domT_def)
apply (simp add: Abs_domT_inject)
apply (simp add: zero_domT)
done

lemma zero_eq_rs_domT: "(T::'a domT) .|. 0 = S .|. 0"
apply (simp add: zero_rs_domT)
done

(*******************************
         min_rs_domT
 *******************************)

lemma min_rs_domT: "((T::'a domT) .|. m) .|. n = T .|. (min m n)"
apply (simp add: rest_domT_def)
apply (simp add: Abs_domT_inject)

apply (simp add: restT_def memT_def)
apply (simp add: restT_in[simplified memT_def restT_def]
                 Abs_domT_inverse)
done

(*******************************
         diff_rs_domT
 *******************************)

(*** contra = ***)

lemma contra_diff_rs_domT: 
  "(ALL n. (T::'a domT) .|. n = S .|. n) ==> T = S"
apply (simp add: rest_domT_eq_iff)
apply (rule order_antisym)
by (auto)

(*** diff_rs_domT ***)

lemma diff_rs_domT: 
  "(T::'a domT) ~= S ==> (EX n. T .|. n ~= S .|. n)"
apply (erule contrapos_pp)
apply (simp)
apply (rule contra_diff_rs_domT, simp)
done

(***************************************************************
                       domT ==> RS
 ***************************************************************)

instance domT :: (type) rs
apply (intro_classes)
apply (simp add: zero_eq_rs_domT)
apply (simp add: min_rs_domT)
apply (simp add: diff_rs_domT)
done

(************************************************************
                        domT ==> MS
 ************************************************************)


instantiation domT :: (type) ms0
begin

definition
  domT_distance_def:
     "distance (TT::('a domT * 'a domT)) = distance_rs TT"
  instance ..
end

instance domT :: (type) ms
apply (intro_classes)
apply (simp_all add: domT_distance_def)
apply (simp add: diagonal_rs)
apply (simp add: symmetry_rs)
apply (simp add: triangle_inequality_rs)
done

(************************************************************
                 i.e.  domT ==> MS & RS 
 ************************************************************)

instance domT :: (type) ms_rs
apply (intro_classes)
apply (simp add: domT_distance_def)
done

(***********************************************************
                      lemmas (Limit)
 ***********************************************************)

(*** normal_seq lemma ***)

lemma normal_seq_domT:
  "[| normal Ts ; lengtht s <= n |]
   ==> (s :t Ts (lengtht s)) = (s :t Ts n)"
apply (simp add: normal_def)
apply (drule_tac x="lengtht s" in spec)
apply (drule_tac x="n" in spec)
apply (simp add: min_is)

apply (simp add: to_distance_rs)
apply (simp add: distance_rs_le_1[THEN sym])
apply (simp add: rest_domT_eq_iff)
apply (drule_tac x="s" in spec)
by (simp)

lemma normal_seq_domT_only_if:
  "[| normal Ts ; lengtht s <= n ; s :t Ts (lengtht s) |]
   ==> s :t Ts n"
by (simp add: normal_seq_domT)

lemma normal_seq_domT_if:
  "[| normal Ts ; lengtht s <= n ; s :t Ts n |]
   ==>  s :t Ts (lengtht s)"
by (simp add: normal_seq_domT)

(*** LimitT_def in domT ***)

lemma LimitT_in[simp]:
  "normal (Ts::'a domT infinite_seq) ==> LimitT Ts : domT"
apply (simp add: domT_def HC_T1_def)
apply (rule conjI)

apply (simp add: LimitT_def)
apply (rule_tac x="<>" in exI)
apply (simp)

apply (simp add: prefix_closed_def LimitT_def)
apply (intro allI impI)
apply (elim conjE exE)

apply (subgoal_tac "lengtht s <= lengtht t")
apply (rule normal_seq_domT_if)
apply (simp_all)
apply (rule memT_prefix_closed, simp_all)
apply (rule length_of_prefix)
apply (simp)
done

(*** :t Limit_domT ***)

lemma Limit_domT_memT: 
  "normal (Ts::'a domT infinite_seq)
   ==> (s :t Limit_domT Ts) = (s :t Ts (lengtht s))"
apply (simp add: memT_def)
apply (simp add: Limit_domT_def)
apply (simp add: Abs_domT_inverse)
apply (simp add: LimitT_def memT_def)
done

(*** Limit_domT lemma ***)

lemma Limit_domT_Limit_lm:
  "normal (Ts::'a domT infinite_seq)
   ==> (ALL n. (Limit_domT Ts) .|. n = (Ts n) .|. n)"
apply (intro allI)
apply (simp add: rest_domT_eq_iff)
apply (simp add: Limit_domT_memT)
by (auto simp add: normal_seq_domT)

(*** (normal) Ts converges to (Limit_domT Ts) ***)

lemma Limit_domT_Limit:
  "normal (Ts::'a domT infinite_seq) ==> Ts convergeTo (Limit_domT Ts)"
by (simp add: to_distance_rs Limit_domT_Limit_lm rest_Limit)

(*** (cauchy) Ts converges to (Limit_domT NF Ts) ***)

lemma cauchy_Limit_domT_Limit:
  "cauchy (Ts::'a domT infinite_seq) ==> Ts convergeTo (Limit_domT (NF Ts))"
apply (simp add: normal_form_seq_same_Limit)
apply (simp add: Limit_domT_Limit normal_form_seq_normal)
done

(***************************************
     Dom_T --> Complete Metric Space
 ***************************************)

lemma domT_cms:
  "cauchy (Ts::'a domT infinite_seq) ==> (EX T. Ts convergeTo T)"
apply (rule_tac x="Limit_domT (NF Ts)" in exI)
by (simp add: cauchy_Limit_domT_Limit)

(************************************************************
                   domT ==> CMS and RS
 ************************************************************)

instance domT :: (type) cms
apply (intro_classes)
by (simp add: domT_cms)

instance domT :: (type) cms_rs
by (intro_classes)

(*** (normal) Limit Ts = Limit_domT Ts ***)

lemma Limit_domT_Limit_eq:
  "normal (Ts::'a domT infinite_seq) ==> Limit Ts = Limit_domT Ts"
apply (insert unique_convergence[of Ts "Limit Ts" "Limit_domT Ts"])
by (simp add: Limit_domT_Limit Limit_is normal_cauchy)

(*----------------------------------------------------------*
 |                                                          |
 |                       cms rs order                       |
 |                                                          |
 *----------------------------------------------------------*)

instance domT :: (type) ms_rs_order0
apply (intro_classes)
done

instance domT :: (type) ms_rs_order
apply (intro_classes)
apply (intro allI)
apply (rule iffI)
apply (simp add: rest_domT_def)
apply (simp add: subdomT_def)
apply (simp add: Abs_domT_inverse)
apply (fold subdomT_def)
apply (rule)
apply (drule_tac x="lengtht t" in spec)
apply (simp add: restT_def)
apply (force)

apply (intro allI)
apply (simp add: rest_domT_def)
apply (simp add: subdomT_def)
apply (simp add: Abs_domT_inverse)
apply (fold subdomT_def)
apply (rule)
apply (simp add: restT_def)
apply (force)
done

instance domT :: (type) cms_rs_order
by (intro_classes)

(*----------------------------------------------------------*
 |                                                          |
 |  i.e. lemma "continuous_rs (Ref_fun (S::'a domT))"       |
 |       by (simp add: continuous_rs_Ref_fun)               |
 |                                                          |
 |  see RS.thy                                              |
 |                                                          |
 *----------------------------------------------------------*)

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
