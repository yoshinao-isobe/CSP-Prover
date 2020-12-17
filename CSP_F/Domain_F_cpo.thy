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
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Domain_F_cpo
imports Domain_F CSP_T.Domain_T_cpo Set_F_cpo 
        CSP.CPO_pair CSP_T.CSP_T_continuous
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
                      Bottom in Dom_F
 *********************************************************)
(*
instance domF :: (type) bot0
by (intro_classes)
*)


instantiation domF :: (type) bot0
begin
definition
  bottom_domF_def : "Bot == ({<>}t ,, {}f)"
instance ..
end

(*
defs (overloaded)
  bottom_domF_def : "Bot == ({<>}t ,, {}f)"
*)

lemma bottom_domF: "Bot <= (F::'a domF)"
apply (simp add: bottom_domF_def pairF_def)
apply (simp add: subdomF_def Abs_domF_inverse)
done

instance domF :: (type) bot
apply (intro_classes)
by (simp add: bottom_domF)

(*** fstF and sndF ***)

lemma fstF_bottom_domF[simp]: "(fstF o Bot) = Bot"
apply (simp add: prod_Bot_def)
apply (simp add: bottom_domF_def)
apply (simp add: bottom_domT_def)
apply (simp add: comp_def pairF)
done

lemma sndF_bottom_domF[simp]: "(sndF o Bot) = Bot"
apply (simp add: prod_Bot_def)
apply (simp add: bottom_domF_def)
apply (simp add: bottom_setF_def)
apply (simp add: comp_def pairF)
done

(********************************************************** 
      lemmas used in a proof that domain_F is a cpo.
 **********************************************************)

(* LUB_TF TFs is an upper bound of TFs *)

definition
  LUB_TF :: "'a domTsetF set => 'a domTsetF"
  where
  LUB_TF_def : "LUB_TF TFs == (UnionT (fst ` TFs), UnionF (snd ` TFs))"
  
definition  
  LUB_domF :: "'a domF set => 'a domF"
  where
  LUB_domF_def : "LUB_domF Fs == Abs_domF (LUB_TF (Rep_domF ` Fs))"

(************* LUB_TF *************)

(*** LUB_TF --> LUB ***)

lemma LUB_TF_isLUB:
  "TFs ~= {} ==> LUB_TF TFs isLUB TFs"
apply (simp add: pair_LUB_decompo)
apply (simp add: LUB_TF_def)
apply (simp add: isLUB_UnionT isLUB_UnionF)
done

(*** LUB --> LUB_TF ***)

lemma isLUB_LUB_TF_only_if:
  "[| TFs ~= {} ; TF isLUB TFs |] ==> TF = LUB_TF TFs"
apply (insert LUB_TF_isLUB[of TFs])
by (simp add: LUB_unique)

(* iff *)

lemma isLUB_LUB_TF : "TFs ~= {} ==> TF isLUB TFs = (TF = LUB_TF TFs)"
apply (rule iffI)
apply (simp add: isLUB_LUB_TF_only_if)
apply (simp add: LUB_TF_isLUB)
done

(*** LUB TF = LUB_TF ***)

lemma LUB_LUB_TF:
  "TFs ~= {} ==> LUB TFs = LUB_TF TFs"
by (simp add: isLUB_LUB LUB_TF_isLUB)

(****** LUB_TF TFs in domF ******)

(* T3_F4 *)

lemma LUB_TF_in_T3_F4: 
  "[| TFs ~= {} ; ALL TF:TFs. TF:domF |] ==> HC_T3_F4 (LUB_TF TFs)"
apply (simp add: LUB_TF_def HC_T3_F4_def)
apply (intro allI impI)
apply (elim bexE conjE)
apply (drule_tac x="x" in bspec, simp)

apply (simp add: domF_iff HC_T3_F4_def)
by (auto)

(* F3 *)

lemma LUB_TF_in_F3: 
  "[| TFs ~= {} ; ALL TF:TFs. TF:domF |] ==> HC_F3 (LUB_TF TFs)"
apply (simp add: LUB_TF_def HC_F3_def)
apply (intro allI impI)

apply (elim bexE conjE)
apply (drule_tac x="x" in bspec, simp)

apply (simp add: domF_def HC_F3_def)
apply (elim conjE)
apply (drule_tac x="s" in spec)
apply (drule_tac x="X" in spec)
apply (drule_tac x="Y" in spec)
by (auto)

(* T2 *)

lemma LUB_TF_in_T2: 
  "[| TFs ~= {} ; ALL TF:TFs. TF:domF |] ==> HC_T2 (LUB_TF TFs)"
apply (simp add: LUB_TF_def HC_T2_def)
apply (intro allI impI)

apply (elim exE bexE)
apply (drule_tac x="x" in bspec, simp)

apply (simp add: domF_def HC_T2_def)
apply (elim conjE)
apply (drule_tac x="s" in spec)
by (auto)

(*** LUB_TF TFs in domF ***)

lemma LUB_TF_in: 
  "[| TFs ~= {} ; ALL TF:TFs. TF:domF |] ==> (LUB_TF TFs): domF"
apply (simp (no_asm) add: domF_iff)
apply (simp add: LUB_TF_in_T2)
apply (simp add: LUB_TF_in_F3)
apply (simp add: LUB_TF_in_T3_F4)
done

lemma LUB_TF_in_Rep: 
  "Fs ~= {} ==> (LUB_TF (Rep_domF ` Fs)): domF"
apply (rule LUB_TF_in)
apply (auto)
done

(************* LUB_domF *************)

(* isLUB lemma *)

lemma TF_isLUB_domFs:
  "[| TF:domF ; TF isLUB Rep_domF ` Fs |] ==> Abs_domF TF isLUB Fs"
apply (simp add: isUB_def isLUB_def)
apply (rule conjI)

(* ub *)
apply (intro allI impI)
apply (elim bexE conjE)
apply (drule_tac x="fst (Rep_domF y)" in spec)
apply (drule_tac x="snd (Rep_domF y)" in spec)
apply (simp add: subdomF_def Abs_domF_inverse)

(* lub *)
apply (intro allI impI)
apply (elim bexE conjE)
apply (rotate_tac -1)
apply (drule_tac x="fst (Rep_domF y)" in spec)
apply (rotate_tac -1)
apply (drule_tac x="snd (Rep_domF y)" in spec)
apply (simp)
apply (drule mp)
 apply (intro allI impI)
 apply (simp add: image_def)
 apply (elim bexE conjE)
 apply (drule_tac x="x" in spec)
 apply (simp)
 apply (simp add: subdomF_def)
apply (simp add: subdomF_def Abs_domF_inverse)
done

(*** LUB_domF --> LUB ***)

lemma LUB_domF_isLUB:
  "Fs ~= {} ==> LUB_domF Fs isLUB Fs"
apply (simp add: LUB_domF_def)
apply (rule TF_isLUB_domFs)
apply (simp add: LUB_TF_in)
apply (simp add: LUB_TF_isLUB)
done

lemma LUB_domF_isLUB_I:
  "[| Fs ~= {} ; F = LUB_domF Fs |] ==> F isLUB Fs"
by (simp add: LUB_domF_isLUB)

(*** LUB --> LUB_domF ***)

lemma isLUB_LUB_domF_only_if:
  "[| Fs ~= {} ; F isLUB Fs |] ==> F = LUB_domF Fs"
apply (insert LUB_domF_isLUB[of Fs])
by (simp add: LUB_unique)

(* iff *)

lemma isLUB_LUB_domF : "Fs ~= {} ==> F isLUB Fs = (F = LUB_domF Fs)"
apply (rule iffI)
apply (simp add: isLUB_LUB_domF_only_if)
apply (simp add: LUB_domF_isLUB)
done

(********************************************************** 
                ( domF, <= ) is a CPO
 **********************************************************)

instance domF :: (type) cpo
apply (intro_classes)
apply (simp add: hasLUB_def)
apply (rule_tac x="LUB_domF X" in exI)
by (simp add: directed_def LUB_domF_isLUB)

(********************************************************** 
             ( domF, <= ) is a pointed CPO
 **********************************************************)

instance domF :: (type) cpo_bot
by (intro_classes)

(********************************************************** 
                 continuity of Abs_domF
 **********************************************************)

(*** Abs_domF ***)

lemma continuous_Abs_domF:
 "[| ALL x. f x: domF ; continuous f |] ==> continuous (Abs_domF o f)"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (drule_tac x="X" in spec, simp)
apply (elim conjE exE)
apply (rule_tac x="x" in exI, simp)
apply (rule TF_isLUB_domFs)
apply (simp)

apply (subgoal_tac "Rep_domF ` (Abs_domF o f) ` X = f ` X")
by (auto simp add: image_def Abs_domF_inverse)

(*** Rep_domF ***)

lemma cont_Rep_domF: "continuous Rep_domF"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (rule_tac x="LUB_domF X" in exI)

apply (simp add: directed_def LUB_domF_isLUB)
apply (simp add: isLUB_LUB_TF)
apply (simp add: LUB_domF_def)
apply (simp add: LUB_TF_in Abs_domF_inverse)
done

(*** fstF and sndF ***)

lemma fstF_continuous: "continuous fstF"
apply (simp add: fstF_def)
apply (rule compo_continuous)
apply (simp add: cont_Rep_domF)
apply (simp add: fst_continuous)
done

lemma sndF_continuous: "continuous sndF"
apply (simp add: sndF_def)
apply (rule compo_continuous)
apply (simp add: cont_Rep_domF)
apply (simp add: snd_continuous)
done

(********************************************************** 
                continuity decomposition
 **********************************************************)

(*** if ***)

lemma continuous_domF:
 "[| ALL x. (f x, g x): domF ; continuous f ; continuous g |]
  ==> continuous (%x. (f x ,, g x))"
apply (simp add: pairF_def)
apply (subgoal_tac "(%x. Abs_domF (f x, g x)) = Abs_domF o (%x. (f x, g x))")
apply (simp)
apply (rule continuous_Abs_domF)
apply (simp)
apply (simp add: pair_continuous)
apply (simp add: comp_def)
apply (simp add: fun_eq_iff)
done

lemmas continuous_domF_decompo_if = continuous_domF

(*** only if ***)

lemma continuous_domF_decompo_only_if_lm:
  "[| ALL x. (f x, g x) : domF; continuous (%x. (f x , g x)) |]
       ==> continuous f & continuous g"
apply (simp add: pair_continuous)
apply (simp add: comp_def)
done

lemma continuous_domF_decompo_only_if:
  "[| ALL x. (f x, g x) : domF; continuous (%x. (f x ,, g x)) |]
   ==> continuous f & continuous g"
apply (rule continuous_domF_decompo_only_if_lm)
apply (simp)
apply (simp add: pairF_def)
apply (insert compo_continuous
       [of "(%x. Abs_domF (f x, g x))" "Rep_domF" ])
apply (simp add: comp_def)
apply (simp add: cont_Rep_domF)
apply (simp add: Abs_domF_inverse)
done

lemma continuous_domF_decompo:
  "ALL x. (f x, g x) : domF
   ==> continuous (%x. (f x ,, g x)) = (continuous f & continuous g)"
apply (rule)
apply (simp add: continuous_domF_decompo_only_if)
apply (simp add: continuous_domF_decompo_if)
done

(********************************************************** 
                continuity of (op o fstF)
 **********************************************************)

(* lemma continuous_op_fstF: "continuous (op o fstF)" *)
lemma continuous_op_fstF: "continuous ((o) fstF)"
apply (simp add: continuous_iff)
apply (intro allI impI)
apply (insert complete_cpo_lm)
apply (drule_tac x="X" in spec)
apply (simp add: hasLUB_def)

apply (elim exE)
apply (rule_tac x="x" in exI)
apply (simp)
apply (simp add: image_def)
apply (simp add: isLUB_def)
apply (simp add: isUB_def)
apply (rule)

 (* UB *)
 apply (intro allI impI)
 apply (elim conjE bexE) 
 apply (simp)
 apply (drule_tac x="xa" in spec)
 apply (simp add: order_prod_def)
 apply (simp add: mono_fstF[simplified mono_def])

 (* LUB *)
 apply (intro allI impI)
 apply (elim conjE)

 apply (rotate_tac -1)
 apply (drule_tac x="(%pn. (y pn ,, maxFof (y pn)))" in spec)
 apply (drule mp)

  apply (intro allI impI)
  apply (drule_tac x="fstF o ya" in spec)
  apply (drule mp, fast)
  apply (simp add: order_prod_def)
  apply (intro allI impI)
  apply (drule_tac x="xa" in spec)
  apply (simp add: subdomF_decompo)
  apply (simp add: pairF maxFof_domF)
  apply (rule)
  apply (simp add: subdomT_iff)
  apply (drule_tac x="s" in spec)
  apply (simp add: pairF_domF_T2)
  apply (simp add: maxFof_max)

 apply (simp add: order_prod_def)
 apply (simp add: subdomF_decompo)
 apply (simp add: pairF maxFof_domF)
done

(********************************************************** 
              fstF-distribution over LUB
 **********************************************************)

lemma dist_fstF_LUB:
  "X ~= {} ==> fstF o LUB X = LUB (((o) fstF) ` X)"
(*  "X ~= {} ==> fstF o LUB X = LUB ((op o fstF) ` X)" *)
apply (subgoal_tac "X hasLUB")
apply (rule sym)
apply (rule isLUB_LUB)
apply (simp add: isLUB_def isUB_def)
apply (rule)

(* UB *)
 apply (intro allI impI)
 apply (simp add: image_iff)
 apply (simp add: comp_def)
 apply (elim bexE)
 apply (simp add: order_prod_def)
 apply (intro allI)
 apply (subgoal_tac "x <= LUB X")

  apply (simp add: order_prod_def)
  apply (simp add: mono_fstF[simplified mono_def])
  apply (subgoal_tac "LUB X isLUB X")
  apply (simp add: isLUB_def isUB_def)
  apply (simp add: LUB_is)

(* LUB *)
 apply (intro allI impI)
 apply (simp add: order_prod_def)
 apply (intro allI impI)
 apply (subgoal_tac "(LUB X) isLUB X")

  apply (simp add: prod_LUB_decompo)
  apply (simp add: proj_fun_def)
  apply (drule_tac x="x" in spec)
  apply (subgoal_tac "(%xa. xa x) ` X ~= {}")

   apply (simp add: isLUB_LUB_domF)
   apply (simp add: LUB_domF_def)
   apply (simp add: fstF_def)
   apply (simp add: LUB_TF_in_Rep Abs_domF_inverse)
   apply (simp add: LUB_TF_def)
   apply (rule subdomTI)
   apply (simp)
   apply (elim conjE bexE)
   apply (drule_tac x="fstF o xa" in spec)
   apply (drule mp)
    apply (simp add: image_iff)
    apply (rule_tac x="xa" in bexI)
    apply (simp add: fstF_def)
    apply (simp)
   apply (drule_tac x="x" in spec)
   apply (simp add: subdomT_iff)
   apply (drule_tac x="t" in spec)
   apply (simp add: fstF_def)

  apply (force)
 apply (rule LUB_is)
 apply (simp)

apply (simp add: hasLUB_def)
apply (simp add: prod_LUB_decompo)
apply (simp add: proj_fun_def)
apply (rule_tac x="(%i. LUB_domF ((%x. x i) ` X))" in exI)
apply (simp add: isLUB_LUB_domF)
done

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
