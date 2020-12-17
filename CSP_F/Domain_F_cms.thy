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
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2018         |
            |               February 2019  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Domain_F_cms
imports Domain_F CSP_T.Domain_T_cms Set_F_cms 
        CSP.RS_pair CSP.RS_prod
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

(*********************************************************
                 Restriction in Dom_F
 *********************************************************)

(*
instance domF :: (type) ms0
by (intro_classes)
*)

definition
 restTF  :: "'a domF => nat => 'a domTsetF" ("_ restTF _" [84,900] 84)
 where
 restTF_def  : 
   "F restTF n == (Rep_domF F) .|. n"
 
definition
 LimitTF :: "'a domF infinite_seq => 'a domTsetF"
 where
  LimitTF_def : 
   "LimitTF Fs == pair_Limit (Rep_domF o Fs)"
 
definition 
 Limit_domF     :: "'a domF infinite_seq => 'a domF"
 where
  Limit_domF_def     :
   "Limit_domF Fs == Abs_domF (LimitTF Fs)"

(* isabelle 2009-2 *)

instantiation domF :: (type) rs0
begin

definition
  rest_domF_def : "F .|. n == Abs_domF (F restTF n)"
  instance ..
end

(*
defs (overloaded)
  rest_domF_def : "F .|. n == Abs_domF (F restTF n)"
*)

(*********************************************************
              Lemmas (Restriction in Dom_F)
 *********************************************************)

(*** restTF (T2) ***)

lemma restTF_T2: "HC_T2 (F restTF n)"
apply (simp add: HC_T2_def restTF_def)
apply (intro allI impI)
apply (simp add: pair_restriction_def)

apply (simp add: in_rest_domT)
apply (simp add: in_rest_setF)
by (auto simp add: domTsetF_T2)

(*** restTF (F3) ***)

lemma restTF_F3: "HC_F3 (F restTF n)"
apply (simp add: HC_F3_def restTF_def)
apply (intro allI impI)
apply (simp add: pair_restriction_def)

apply (simp add: in_rest_domT)
apply (simp add: in_rest_setF)
by (auto simp add: domTsetF_F3)

(*** restTF (T3_F4) ***)

lemma restTF_T3_F4: "HC_T3_F4 (F restTF n)"
apply (simp add: HC_T3_F4_def restTF_def)
apply (intro allI impI)
apply (simp add: pair_restriction_def)

apply (simp add: in_rest_domT)
apply (simp add: in_rest_setF)
apply (elim conjE)
by (auto simp add: domTsetF_T3 domTsetF_F4)

(*** restTF in domF ***)

lemma restTF_in[simp]: "F restTF n : domF"
apply (simp add: domF_iff)
apply (simp add: restTF_T2)
apply (simp add: restTF_F3)
apply (simp add: restTF_T3_F4)
done

(*********************************************************
                     Dom_F --> RS
 *********************************************************)

(*** rest_domF --> restTF ***)

lemma Rep_rest_domF: 
  "((F::'a domF) .|. n = E .|. m) =
   ((Rep_domF F) .|. n = (Rep_domF E) .|. m)"
apply (simp add: rest_domF_def)
apply (simp add: Abs_domF_inject)
apply (simp add: restTF_def)
done

(*** zero_eq_rs_domF ***)

lemma zero_eq_rs_domF: "(F::'a domF) .|. 0 = E .|. 0"
by (simp add: Rep_rest_domF)

(*** min_rs_domF ***)

lemma min_rs_domF:
  "((F::'a domF) .|. m) .|. n = F .|. (min m n)"
apply (simp add: Rep_rest_domF)
apply (simp add: rest_domF_def)
apply (simp add: Abs_domF_inverse)
apply (simp add: restTF_def)
apply (simp add: min_rs)
done

(*** diff_rs_domF ***)

lemma diff_rs_domF: 
  "(F::'a domF) ~= E ==> (EX (n::nat). F .|. n ~= E .|. n)"
apply (simp add: Rep_rest_domF)
apply (simp add: Rep_domF_inject[THEN sym])
apply (simp add: diff_rs)
done

(***************************************************************
                        domF ==> RS
 ***************************************************************)

instance domF :: (type) rs
apply (intro_classes)
apply (simp add: zero_eq_rs_domF)
apply (simp add: min_rs_domF)
apply (simp add: diff_rs_domF)
done

(************************************************************
                        domF ==> MS
 ************************************************************)

instantiation domF :: (type) ms0
begin

definition
  domF_distance_def:
     "distance (FF::('a domF * 'a domF)) = distance_rs FF"
  instance ..
end

instance domF :: (type) ms
apply (intro_classes)
apply (simp_all add: domF_distance_def)
apply (simp add: diagonal_rs)
apply (simp add: symmetry_rs)
apply (simp add: triangle_inequality_rs)
done

(************************************************************
                 i.e.  domF ==> MS & RS 
 ************************************************************)

instance domF :: (type) ms_rs
apply (intro_classes)
apply (simp add: domF_distance_def)
done


(********************************************************** 
                      .|. decompo 
 **********************************************************)

lemma rest_decompo_domF:
   "(SF1 .|. n = SF2 .|. m)
   = ((fstF SF1 .|. n = fstF SF2 .|. m &
       sndF SF1 .|. n = sndF SF2 .|. m))"
apply (simp add: rest_domF_def)
apply (simp add: Abs_domF_inject)
apply (simp add: restTF_def)
apply (simp add: pair_restriction_def)
apply (simp add: fold_fstF)
apply (simp add: fold_sndF)
done

(***********************************************************
                    lemmas (distance)
 ***********************************************************)

(*** distance ***)

lemma distance_Rep_domF:
  "distance((F::'a domF), E) = distance(Rep_domF F, Rep_domF E)"
apply (simp add: to_distance_rs)
apply (simp add: Rep_rest_domF rest_distance_eq)
done

lemma distance_Abs_domF:
  "[| (T1, F1) : domF ; (T2, F2) : domF |]
   ==> distance (Abs_domF (T1, F1), Abs_domF (T2, F2))
     = distance ((T1, F1), T2, F2)"
by (simp add: distance_Rep_domF Abs_domF_inverse)

(*** normal ***)

lemma normal_domF:
  "normal (Fs::'a domF infinite_seq) = normal (Rep_domF o Fs)"
by (simp add: normal_def distance_Rep_domF)

lemma normal_domF_only_if:
  "normal (Fs::'a domF infinite_seq) ==> normal (Rep_domF o Fs)"
by (simp add: normal_domF)

(* T and F *)

lemma normal_of_domF:
  "normal (Fs::'a domF infinite_seq)
   ==> (normal (fstF o Fs) & normal (sndF o Fs))"
apply (simp add: normal_domF)
apply (simp add: fstF_def sndF_def)
apply (simp add: o_assoc[THEN sym])
apply (simp add: pair_normal_seq)
done

(*** cauchy ***)

lemma cauchy_domF:
  "cauchy (Fs::'a domF infinite_seq) = cauchy (Rep_domF o Fs)"
by (simp add: cauchy_def distance_Rep_domF)

lemma cauchy_domF_only_if:
  "cauchy (Fs::'a domF infinite_seq) ==> cauchy (Rep_domF o Fs)"
by (simp add: cauchy_domF)

(* T and F *)

lemma cauchy_of_domF:
  "cauchy (Fs::'a domF infinite_seq)
   ==> (cauchy (fstF o Fs) & cauchy (sndF o Fs))"
apply (simp add: cauchy_domF)
apply (simp add: fstF_def sndF_def)
apply (simp add: o_assoc[THEN sym])
apply (simp add: pair_cauchy_seq)
done

(***********************************************************
                      lemmas (Limit)
 ***********************************************************)

(*** convergeTo domF ***)

lemma convergeTo_domF:
  "[| (Rep_domF o Fs) convergeTo TF ; TF : domF |]
   ==> Fs convergeTo Abs_domF TF"
apply (simp add: convergeTo_def)
apply (intro allI impI)
apply (drule_tac x="eps" in spec)
apply (simp)
apply (erule exE)
apply (rule_tac x="n" in exI)
apply (intro allI impI)
apply (drule_tac x="m" in spec)

apply (simp add: distance_Rep_domF)
apply (simp add: Abs_domF_inverse)
done

(*** LimitTF ***)

lemma LimitTF_iff:
  "normal (Rep_domF o Fs) 
      ==> pair_Limit (Rep_domF o Fs)
           = (Limit_domT (fstF o Fs) , Limit_setF (sndF o Fs))"
apply (simp add: pair_Limit_def)
apply (simp add: fstF_def sndF_def)
apply (simp add: o_assoc[THEN sym])
apply (simp add: pair_normal_seq Limit_domT_Limit_eq Limit_setF_Limit_eq)
done

(*******************************
      LimitTF in domF
 *******************************)

(*** F4 ***)

lemma LimitTF_F4:
  "normal Fs ==> HC_F4 (Limit_domT (fstF o Fs) , Limit_setF (sndF o Fs))"
apply (simp add: HC_F4_def)
apply (intro allI impI)

apply (simp add: normal_of_domF Limit_domT_memT)
apply (simp add: normal_of_domF Limit_setF_memF)

apply (subgoal_tac "(Rep_domF (Fs (lengtht (s ^^^ <Tick>)))) : domF")
apply (simp add: domF_def HC_F4_def)
apply (elim conjE)
apply (drule_tac x="s" in spec)
apply (simp add: fstF_def sndF_def)
by (simp)

(*** T3 ***)

lemma LimitTF_T3:
  "normal Fs ==> HC_T3 (Limit_domT (fstF o Fs) , Limit_setF (sndF o Fs))"
apply (simp add: HC_T3_def)
apply (intro allI impI)
apply (simp add: normal_of_domF Limit_domT_memT)
apply (simp add: normal_of_domF Limit_setF_memF)

apply (subgoal_tac "(Rep_domF (Fs (lengtht (s ^^^ <Tick>)))) : domF")
apply (simp add: domF_def HC_T3_def)
apply (elim conjE)
apply (drule_tac x="s" in spec)
apply (simp add: fstF_def sndF_def)
apply (rule disjI2)
apply (rule_tac x="s" in exI)
apply (simp)
by (simp)

(*** F3 ***)

lemma LimitTF_F3:
  "normal Fs ==> HC_F3 (Limit_domT (fstF o Fs) , Limit_setF (sndF o Fs))"
apply (simp add: HC_F3_def)
apply (intro allI impI)

apply (simp add: normal_of_domF Limit_domT_memT)
apply (simp add: normal_of_domF Limit_setF_memF)
apply (elim conjE disjE)

apply (subgoal_tac "(Rep_domF (Fs (Suc (lengtht s)))) : domF")
apply (simp add: domF_def HC_F3_def)
apply (elim conjE)
apply (drule_tac x="s" in spec)
apply (drule_tac x="X" in spec)
apply (drule_tac x="Y" in spec)
apply (simp add: fstF_def sndF_def)
apply (simp)

apply (erule exE)
apply (simp)
done

(*** T2 ***)

lemma LimitTF_T2:
  "normal Fs ==> HC_T2 (Limit_domT (fstF o Fs) , Limit_setF (sndF o Fs))"
apply (simp add: HC_T2_def)
apply (intro allI impI)

apply (simp add: normal_of_domF Limit_domT_memT)
apply (simp add: normal_of_domF Limit_setF_memF)
apply (elim exE disjE)

apply (subgoal_tac "(Rep_domF (Fs (Suc (lengtht s)))) : domF")
apply (simp add: domF_def HC_T2_def)
apply (elim conjE)
apply (drule_tac x="s" in spec)
apply (simp add: fstF_def sndF_def)
apply (drule mp)
apply (rule_tac x="X" in exI, simp)
apply (rule normal_seq_domT_if)
 apply (subgoal_tac "(%u. fst (Rep_domF (Fs u))) = (fstF o Fs )")
 apply (simp add: normal_of_domF)
 apply (simp add: fun_eq_iff fstF_def)
 apply (simp_all)

(* *)

apply (elim conjE exE)
apply (subgoal_tac "(Rep_domF (Fs (lengtht s))) : domF")
apply (simp add: domF_def HC_T2_def)
apply (elim conjE)
apply (drule_tac x="s" in spec)
apply (simp add: fstF_def sndF_def)
apply (drule mp)
apply (rule_tac x="X" in exI, simp)
apply (simp_all)
done

(*** Limit_domFpari_in ***)

lemma LimitTF_in:
  "normal Fs ==> LimitTF Fs : domF"
apply (simp add: LimitTF_def)
apply (simp add: LimitTF_iff normal_domF_only_if)
apply (simp add: domF_def)
apply (simp add: LimitTF_F4)
apply (simp add: LimitTF_T3)
apply (simp add: LimitTF_F3)
apply (simp add: LimitTF_T2)
done

(*** (normal) Fs converges to (Limit_domF Fs) ***)

lemma Limit_domF_Limit: "normal Fs ==> Fs convergeTo (Limit_domF Fs)"
apply (simp add: Limit_domF_def)
apply (rule convergeTo_domF)
apply (simp add: LimitTF_def)
apply (simp add: pair_cms_cauchy_Limit normal_cauchy normal_domF)

by (simp add: LimitTF_in)

(*** (cauchy) Fs converges to (Limit_domF NF Fs) ***)

lemma cauchy_Limit_domF_Limit:
  "cauchy Fs ==> Fs convergeTo (Limit_domF (NF Fs))"
by (simp add: Limit_domF_Limit normal_form_seq_same_Limit normal_form_seq_normal)

(**************************************
    Dom_F --> Complete Metric Space
 **************************************)

lemma domF_cms:
  "cauchy (Fs::'a domF infinite_seq) ==> (EX F. Fs convergeTo F)"
apply (rule_tac x="Limit_domF (NF Fs)" in exI)
by (simp add: cauchy_Limit_domF_Limit)

(************************************************************
                   domF ==> CMS and RS
 ************************************************************)

instance domF :: (type) cms
apply (intro_classes)
by (simp add: domF_cms)

instance domF :: (type) cms_rs
by (intro_classes)

(*** (normal) Limit Fs = Limit_domF Fs ***)

lemma Limit_domF_Limit_eq:
  "normal (Fs::'a domF infinite_seq) ==> Limit Fs = Limit_domF Fs"
apply (rule unique_convergence[of Fs])
by (simp_all add: Limit_domF_Limit Limit_is normal_cauchy)

(************************************************************
                 .|. domF decompostion
 ************************************************************)

lemma rest_domF_decompo_sub:
   "ALL x. (f x, g x): domF ==>
     ((f x1 ,, g x1) .|. n <= ((f x2 ,, g x2) .|. n))
   = (f x1 .|. n <= f x2 .|. n &
      g x1 .|. n <= g x2 .|. n)"
apply (simp add: rest_domF_def)
apply (simp add: subdomF_def)
apply (simp add: Abs_domF_inverse)

apply (simp add: pairF_def)
apply (simp add: restTF_def)
apply (simp add: Abs_domF_inverse)
apply (simp add: pair_restriction_def)
apply (simp add: order_pair_def)
done

lemma rest_domF_decompo:
   "ALL x. (f x, g x): domF ==>
     ((f x1 ,, g x1) .|. n = ((f x2 ,, g x2) .|. n))
   = (f x1 .|. n = f x2 .|. n &
      g x1 .|. n = g x2 .|. n)"
apply (rule)
apply (simp add: order_eq_iff)
apply (simp add: rest_domF_decompo_sub)
apply (simp add: order_eq_iff)
apply (simp add: rest_domF_decompo_sub)
done

(************************************************************
                  map domF decompostion
 ************************************************************)

(* Abs_domF *)

lemma map_alpha_Abs_domF:
  "ALL x. (f x, g x): domF ==>
   map_alpha (%x. (f x,, g x)) alpha = map_alpha (f ** g) alpha"
apply (simp add: pairF_def)
apply (simp add: contraction_alpha_def map_alpha_def)
apply (simp add: pair_fun_def)
apply (simp add: distance_Abs_domF)
done

(* decompo *)

lemma map_alpha_domF_decompo:
  "ALL (x::'a::ms_rs). (f x, g x): domF ==>
   map_alpha  (%x. (f x,, g x)) alpha = 
   (map_alpha f alpha & map_alpha g alpha)"
apply (simp add: map_alpha_Abs_domF)
apply (simp add: pair_map_alpha_compo)
done

lemma non_expanding_domF_decompo:
  "ALL (x::'a::ms_rs). (f x, g x): domF ==>
   non_expanding (%x. (f x,, g x)) =
   (non_expanding f & non_expanding g)"
apply (simp add: non_expanding_def)
apply (simp add: map_alpha_domF_decompo)
done

lemma contraction_alpha_domF_decompo:
  "ALL (x::'a::ms_rs). (f x, g x): domF ==>
   contraction_alpha (%x. (f x,, g x)) alpha =
   (contraction_alpha f alpha & contraction_alpha g alpha)"
apply (simp add: contraction_alpha_def)
apply (simp add: map_alpha_domF_decompo)
apply (auto)
done

(********************************************************** 
                non expanding (op o fstF)
 **********************************************************)

lemma non_expanding_Rep_domF: "non_expanding Rep_domF"
apply (simp add: non_expanding_def)
apply (simp add: map_alpha_def)
apply (simp add: distance_Rep_domF)
done

lemma non_expanding_fstF: "non_expanding fstF"
apply (simp add: fstF_def)
apply (rule compo_non_expand)
apply (simp add: fst_non_expand)
apply (simp add: non_expanding_Rep_domF)
done

lemma non_expanding_sndF: "non_expanding sndF"
apply (simp add: sndF_def)
apply (rule compo_non_expand)
apply (simp add: snd_non_expand)
apply (simp add: non_expanding_Rep_domF)
done

lemma non_expanding_op_fstF: "non_expanding ((o) fstF)"
apply (simp add: prod_non_expand)
apply (insert non_expanding_fstF)
apply (simp add: proj_fun_def)
apply (simp add: non_expanding_def)
apply (simp add: map_alpha_def)
apply (intro allI)
apply (drule_tac x="x i" in spec)
apply (drule_tac x="y i" in spec)
apply (rule order_trans)
apply (simp)

apply (subgoal_tac "non_expanding (proj_fun i)")
apply (simp add: non_expanding_def)
apply (simp add: map_alpha_def)
apply (simp add: proj_fun_def)
apply (fast)

apply (simp add: proj_non_expand)
done

lemma non_expanding_op_sndF: "non_expanding ((o) sndF)"
apply (simp add: prod_non_expand)
apply (insert non_expanding_sndF)
apply (simp add: proj_fun_def)
apply (simp add: non_expanding_def)
apply (simp add: map_alpha_def)
apply (intro allI)
apply (drule_tac x="x i" in spec)
apply (drule_tac x="y i" in spec)
apply (rule order_trans)
apply (simp)

apply (subgoal_tac "non_expanding (proj_fun i)")
apply (simp add: non_expanding_def)
apply (simp add: map_alpha_def)
apply (simp add: proj_fun_def)
apply (fast)

apply (simp add: proj_non_expand)
done

(*** distance ***)

declare [[show_sorts]]


lemma distance_fstF_compo_le: 
  "distance (fstF o x, fstF o y) <= distance (x, y)"
apply (insert non_expanding_op_fstF)
apply (simp add: non_expanding_def)
apply (simp add: map_alpha_def)
apply (auto)
done

lemma alpha_distance_fstF_compo_le: 
  "0 <= alpha ==> alpha * distance (fstF o x, fstF o y) <= alpha * distance (x, y)"
apply (insert mult_left_mono
       [of "distance (fstF o x, fstF o y)" "distance (x, y)" "alpha" ])
apply (simp add: distance_fstF_compo_le)
done

(*----------------------------------------------------------*
 |                                                          |
 |                       cms rs order                       |
 |                                                          |
 *----------------------------------------------------------*)

instance domF :: (type) ms_rs_order0
apply (intro_classes)
done

instance domF :: (type) ms_rs_order
apply (intro_classes)
apply (intro allI)
apply (rule iffI)
apply (simp add: rest_domF_def)
apply (simp add: subdomF_def)
apply (simp add: Abs_domF_inverse)
apply (simp add: restTF_def)
apply (simp add: pair_restriction_def)
apply (simp add: order_pair_def)
apply (erule dist_ALL_conjE)
apply (simp add: rs_order_iff)

apply (intro allI)
apply (simp add: rest_domF_def)
apply (simp add: subdomF_def)
apply (simp add: Abs_domF_inverse)
apply (simp add: restTF_def)
apply (simp add: pair_restriction_def)
apply (simp add: order_pair_def)
apply (simp add: rs_order_if)
done

instance domF :: (type) cms_rs_order
by (intro_classes)

(*----------------------------------------------------------*
 |                                                          |
 |  i.e. lemma "continuous_rs (Ref_fun (S::'a domF))"       |
 |       by (simp add: continuous_rs_Ref_fun)               |
 |                                                          |
 |  see RS.thy                                              |
 |                                                          |
 *----------------------------------------------------------*)

end
