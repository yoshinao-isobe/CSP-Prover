           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               February 2005               |
            |                   June 2005  (modified)   |
            |                 August 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_law_fp
imports CSP_T_law_ufp
begin

(*****************************************************************

         1. cpo fixed point theory in CSP-Prover
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

(*=======================================================*
 |                                                       |
 |                        CPO                            |
 |                                                       |
 *=======================================================*)

(*-------------*
 |  existency  |
 *-------------*)

lemma semT_hasLFP_cpo: 
 "Pf = PNfun ==> [[Pf]]Tfun hasLFP"
apply (rule Tarski_thm_EX)
apply (rule continuous_semTfun)
done

lemma semT_LFP_cpo:
  "[| Pf = PNfun ;
      FPmode = CPOmode | FPmode = MIXmode |]
  ==> [[$p]]T = LFP [[Pf]]Tfun p"
apply (simp add: semT_def semTf_def)
apply (simp add: traces_iff)
apply (simp add: MT_def)
apply (simp add: semTfix_def)
apply (force)
done

lemma semT_LFP_fun_cpo:
  "[| Pf = PNfun ;
      FPmode = CPOmode | FPmode = MIXmode |]
  ==> (%p. [[$p]]T) = LFP [[Pf]]Tfun"
apply (simp (no_asm) add: fun_eq_iff)
apply (simp add: semT_LFP_cpo)
done

(*---------*
 |    MT   |
 *---------*)

lemma MT_fixed_point_cpo:
      "[| (Pf::'p=>('p,'a) proc) = PNfun; FPmode = CPOmode | FPmode = MIXmode |]
        ==> [[Pf]]Tfun (MT::'p => 'a domT) = (MT::'p => 'a domT)"
apply (simp add: MT_def)
apply (simp add: semTfix_def)
apply (erule disjE)
apply (simp_all)
apply (rule LFP_fp)
apply (simp add: semT_hasLFP_cpo)
apply (rule LFP_fp)
apply (simp add: semT_hasLFP_cpo)
done

(*-------------*
 |  greatest   |
 *-------------*)

lemma ALL_cspT_greatest_cpo:
  "[| Pf = PNfun ;
       FPmode = CPOmode ;
       ALL p. (Pf p) << f =T f p |] ==> ALL p. f p <=T $p"
apply (simp add: eqT_def refT_def)
apply (fold semT_def)
apply (simp add: fun_eq_iff[THEN sym])
apply (fold order_prod_def)
apply (insert semT_LFP_fun_cpo[of "Pf"])
apply (simp)

apply (rule LFP_least)
apply (simp add: semT_hasLFP_cpo)

apply (simp add: semT_def semTfun_def semTf_def)
apply (simp add: traces_subst)
done

lemma cspT_greatest_cpo:
  "[| Pf = PNfun ;
       FPmode = CPOmode ;
       ALL p. (Pf p) << f =T f p |] ==> f p <=T $p"
by (simp add: ALL_cspT_greatest_cpo)

(*-------------------------------------------------------*
 |                                                       |
 |           Fixpoint unwind (CSP-Prover rule)           |
 |                                                       |
 *-------------------------------------------------------*)

lemma ALL_cspT_unwind_cpo:
   "[| Pf = PNfun ;
       FPmode = CPOmode | FPmode = MIXmode |]
     ==> ALL p. ($p =T Pf p)"
apply (simp add: cspT_semantics)
apply (simp add: traces_iff)
apply (simp add: MT_def)
apply (simp add: semTfix_def)
apply (simp add: fun_eq_iff[THEN sym])
apply (simp add: traces_semTfun)
apply (simp add: LFP_fp semT_hasLFP_cpo)
apply (force)
done

(*  csp law  *)

lemma cspT_unwind_cpo:
   "[| Pf = PNfun ;
       FPmode = CPOmode | FPmode = MIXmode |]
     ==> $p =T Pf p"
by (simp add: ALL_cspT_unwind_cpo)

(*-------------------------------------------------------*
 |                                                       |
 |    fixed point inducntion (CSP-Prover intro rule)     |
 |                                                       |
 *-------------------------------------------------------*)

(*** right ***)

lemma cspT_fp_induct_cpo_ref_right_ALL:
   "[| Pf = PNfun ;
       FPmode = CPOmode | FPmode = MIXmode ;
       Q <=T f p;
       ALL p. f p <=T (Pf p)<<f |]
    ==> Q <=T $p"
apply (simp add: refT_semT)
apply (insert cpo_fixpoint_induction_rev
       [of "[[Pf]]Tfun" "(%p. [[f p]]T)"])
apply (simp add: LFP_fp semT_hasLFP_cpo)
apply (simp add: fold_order_prod_def)
apply (simp add: semT_subst_semTfun)

apply (simp add: continuous_semTfun)
apply (simp add: order_prod_def)
apply (drule_tac x="p" in spec)+

apply (simp add: semT_LFP_cpo)
done

(*  csp law  *)

lemma cspT_fp_induct_cpo_ref_right:
   "[| Pf = PNfun ;
       FPmode = CPOmode | FPmode = MIXmode ;
       Q <=T f p;
       !! p. f p <=T (Pf p)<<f |]
    ==> Q <=T $p"
by (simp add: cspT_fp_induct_cpo_ref_right_ALL)

lemmas cspT_fp_induct_cpo_right 
     = cspT_fp_induct_cpo_ref_right

(*=======================================================*
 |                                                       |
 |                    LFP <--> UFP                       |
 |                                                       |
 |                       MIXmode                         |
 |                                                       |
 *=======================================================*)

lemma semT_guarded_LFP_UFP:
  "[| Pf = PNfun ; guardedfun Pf |]
   ==> LFP [[Pf]]Tfun = UFP [[Pf]]Tfun"
by (simp add: semT_hasUFP_cms hasUFP_LFP_UFP)

(*----------- refinement -----------*)

(*** left ***)

lemma cspT_fp_induct_mix_ref_left_ALL:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = MIXmode ;
       f p <=T Q ;
       ALL p. (Pf p)<<f <=T f p |]
    ==> $p <=T Q"
apply (simp add: refT_semT)
apply (insert cms_fixpoint_induction_ref
       [of "[[Pf]]Tfun" "(%p. [[f p]]T)" "UFP [[Pf]]Tfun"])
apply (simp add: semT_guarded_LFP_UFP[THEN sym])
apply (simp add: LFP_fp semT_hasLFP_cpo)

apply (simp add: fold_order_prod_def)
apply (simp add: semT_subst_semTfun)
apply (simp add: mono_semTfun)

apply (simp add: contra_alpha_to_contst contraction_alpha_semTfun)
apply (simp add: to_distance_rs)
apply (simp add: order_prod_def)
apply (drule_tac x="p" in spec)+
apply (simp add: semT_LFP_cpo)
done

(*  csp law  *)

lemma cspT_fp_induct_mix_ref_left:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = MIXmode ;
       f p <=T Q ;
       !! p. (Pf p)<<f <=T f p |]
    ==> $p <=T Q"
by (simp add: cspT_fp_induct_mix_ref_left_ALL)

(*----------- equality -----------*)

(*** left ***)

lemma cspT_fp_induct_mix_eq_left_ALL:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = MIXmode ;
       f p =T Q ;
       ALL p. (Pf p)<<f =T f p |]
    ==> $p =T Q"
apply (simp add: eqT_semT)
apply (simp add: fun_eq_iff[THEN sym])
apply (simp add: semT_subst_semTfun)
apply (insert semT_LFP_fun_cpo[of Pf])
apply (simp add: semT_guarded_LFP_UFP)
apply (subgoal_tac "(%p. [[$p]]T) = (%p. [[f p]]T)")
apply (simp add: fun_eq_iff)

apply (rule hasUFP_unique_solution[of "[[Pf]]Tfun"])
apply (simp_all add: semT_hasUFP_cms)
apply (simp add: UFP_fp semT_hasUFP_cms)
done

(*  csp law  *)

lemma cspT_fp_induct_mix_eq_left:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = MIXmode ;
       f p =T Q;
       !! p. (Pf p)<<f =T f p |]
    ==> $p =T Q"
by (simp add: cspT_fp_induct_mix_eq_left_ALL)

lemma cspT_fp_induct_mix_eq_right:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = MIXmode ;
       Q =T f p;
       !! p. f p =T (Pf p)<<f |]
    ==> Q =T $p"
apply (rule cspT_sym)
apply (rule cspT_fp_induct_mix_eq_left[of Pf f p Q])
apply (simp_all)
apply (rule cspT_sym)
apply (simp)
apply (rule cspT_sym)
apply (simp)
done

lemmas cspT_fp_induct_mix_left 
     = cspT_fp_induct_mix_ref_left cspT_fp_induct_mix_eq_left

lemmas cspT_fp_induct_mix_right 
     = cspT_fp_induct_cpo_ref_right cspT_fp_induct_mix_eq_right

(*=======================================================*
 |                                                       |
 |            mixing CPOmode and CMSmode                 |
 |                                                       |
 *=======================================================*)

lemma cspT_unwind:
   "[| Pf = PNfun ;
       FPmode = CPOmode
     | FPmode = CMSmode & guardedfun Pf
     | FPmode = MIXmode |]
     ==> $p =T Pf p"
apply (erule disjE)
apply (simp add: cspT_unwind_cpo)
apply (erule disjE)
apply (simp add: cspT_unwind_cms)
apply (simp add: cspT_unwind_cpo)
done

lemma cspT_fp_induct_ref_right:
   "[| Pf = PNfun ;
       FPmode = CPOmode
     | FPmode = CMSmode & guardedfun Pf
     | FPmode = MIXmode ;
       Q <=T f p;
       !! p. f p <=T (Pf p)<<f |]
    ==> Q <=T $p"
apply (erule disjE)
apply (simp add: cspT_fp_induct_cpo_right)
apply (erule disjE)
apply (simp add: cspT_fp_induct_cms_right)
apply (simp add: cspT_fp_induct_cpo_right)
done

lemma cspT_fp_induct_ref_left:
   "[| Pf = PNfun ;
       FPmode = CMSmode 
     | FPmode = MIXmode ;
       guardedfun Pf ;
       f p <=T Q ;
       !! p. (Pf p)<<f <=T f p |]
    ==> $p <=T Q"
apply (erule disjE)
apply (simp add: cspT_fp_induct_cms_left)
apply (simp add: cspT_fp_induct_mix_left)
done

lemma cspT_fp_induct_eq_left:
   "[| Pf = PNfun ;
       FPmode = CMSmode 
     | FPmode = MIXmode ;
       guardedfun Pf ;
       f p =T Q ;
       !! p. (Pf p)<<f =T f p |]
    ==> $p =T Q"
apply (erule disjE)
apply (simp add: cspT_fp_induct_cms_left)
apply (simp add: cspT_fp_induct_mix_left)
done

lemma cspT_fp_induct_eq_right:
   "[| Pf = PNfun ;
       FPmode = CMSmode 
     | FPmode = MIXmode ;
       guardedfun Pf ;
       Q =T f p;
       !! p. f p =T (Pf p)<<f |]
    ==> Q =T $p"
apply (erule disjE)
apply (simp add: cspT_fp_induct_cms_right)
apply (simp add: cspT_fp_induct_mix_right)
done

(*** cpo and cms ***)

lemmas cspT_fp_induct_right = cspT_fp_induct_ref_right cspT_fp_induct_eq_right
lemmas cspT_fp_induct_left = cspT_fp_induct_ref_left cspT_fp_induct_eq_left

(****************** to add them again ******************)
(* 2013
declare Union_image_eq [simp]
declare Inter_image_eq [simp]
*)
(* 2017
declare Sup_image_eq [simp]
declare Inf_image_eq [simp]
*)
end
