           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               February 2005               |
            |                   June 2005 (modified)    |
            |              September 2005 (modified)    |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_law_fp
imports CSP_T.CSP_T_law_fp CSP_F_law_ufp
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

lemma semF_hasLFP_cpo: 
 "Pf = PNfun ==> [[Pf]]Ffun hasLFP"
apply (rule Tarski_thm_EX)
apply (rule continuous_semFfun)
done

lemma semF_LFP_cpo:
  "[| Pf = PNfun ;
      FPmode = CPOmode | FPmode = MIXmode |]
  ==> [[$p]]F = LFP ([[Pf]]Ffun) p"
apply (simp add: semF_def)
apply (simp add: semFf_Proc_name)
apply (simp add: MF_def)
apply (simp add: semFfix_def)
apply (force)
done

lemma semF_LFP_fun_cpo:
  "[| Pf = PNfun ;
      FPmode = CPOmode | FPmode = MIXmode |]
  ==> (%p. [[$p]]F) = LFP ([[Pf]]Ffun)"
apply (simp (no_asm) add: fun_eq_iff)
apply (simp add: semF_LFP_cpo)
done

(*---------*
 |    MF   |
 *---------*)

lemma MF_fixed_point_cpo:
      "[| (Pf::'p=>('p,'a) proc) = PNfun; FPmode = CPOmode | FPmode = MIXmode |]
        ==> [[Pf]]Ffun (MF::'p => 'a domF) = (MF::'p => 'a domF)"
apply (simp add: MF_def)
apply (simp add: semFfix_def)
apply (erule disjE)
apply (simp_all)
apply (rule LFP_fp)
apply (simp add: semF_hasLFP_cpo)
apply (rule LFP_fp)
apply (simp add: semF_hasLFP_cpo)
done

(*-------------*
 |  greatest   |
 *-------------*)

lemma ALL_cspF_greatest_cpo:
  "[| Pf = PNfun ;
       FPmode = CPOmode ;
       ALL p. (Pf p) << f =F f p |] ==> ALL p. f p <=F $p"
apply (simp add: eqF_def refF_def)
apply (fold semF_def)
apply (simp add: fun_eq_iff[THEN sym])
apply (fold order_prod_def)
apply (insert semF_LFP_fun_cpo[of "Pf"])
apply (simp)

apply (rule LFP_least)
apply (simp add: semF_hasLFP_cpo)

apply (simp add: semF_subst)
apply (simp add: semFfun_def)
done

lemma cspF_greatest_cpo:
  "[| Pf = PNfun ;
       FPmode = CPOmode ;
       ALL p. (Pf p) << f =F f p |] ==> f p <=F $p"
by (simp add: ALL_cspF_greatest_cpo)

(*-------------------------------------------------------*
 |                                                       |
 |           Fixpoint unwind (CSP-Prover rule)           |
 |                                                       |
 *-------------------------------------------------------*)

lemma ALL_cspF_unwind_cpo:
   "[| Pf = PNfun ;
       FPmode = CPOmode | FPmode = MIXmode |]
     ==> ALL p. ($p =F Pf p)"
apply (simp add: eqF_def)
apply (simp add: semFf_Proc_name)
apply (simp add: MF_def)
apply (simp add: semFfix_def)
apply (simp add: fun_eq_iff[THEN sym])
apply (simp add: semFf_semFfun)
apply (simp add: LFP_fp semF_hasLFP_cpo)
apply (force)
done

(*  csp law  *)

lemma cspF_unwind_cpo:
   "[| Pf = PNfun ;
       FPmode = CPOmode | FPmode = MIXmode |]
     ==> $p =F Pf p"
by (simp add: ALL_cspF_unwind_cpo)

(*-------------------------------------------------------*
 |                                                       |
 |    fixed point inducntion (CSP-Prover intro rule)     |
 |                                                       |
 *-------------------------------------------------------*)

(*** right ***)

lemma cspF_fp_induct_cpo_ref_right_ALL:
   "[| Pf = PNfun ;
       FPmode = CPOmode | FPmode = MIXmode ;
       Q <=F f p;
       ALL p. f p <=F (Pf p)<<f |]
    ==> Q <=F $p"
apply (simp add: refF_semF)
apply (insert cpo_fixpoint_induction_rev
       [of "[[Pf]]Ffun" "(%p. [[f p]]F)"])
apply (simp add: LFP_fp semF_hasLFP_cpo)
apply (simp add: fold_order_prod_def)
apply (simp add: semF_subst_semFfun)

apply (simp add: continuous_semFfun)
apply (simp add: order_prod_def)
apply (drule_tac x="p" in spec)+

apply (simp add: semF_LFP_cpo)
done

(*  csp law  *)

lemma cspF_fp_induct_cpo_ref_right:
   "[| Pf = PNfun ;
       FPmode = CPOmode | FPmode = MIXmode ;
       Q <=F f p;
       !! p. f p <=F (Pf p)<<f |]
    ==> Q <=F $p"
by (simp add: cspF_fp_induct_cpo_ref_right_ALL)

lemmas cspF_fp_induct_cpo_right 
     = cspF_fp_induct_cpo_ref_right

(*=======================================================*
 |                                                       |
 |                    LFP <--> UFP                       |
 |                                                       |
 |                       MIXmode                         |
 |                                                       |
 *=======================================================*)

lemma semF_guarded_LFP_UFP:
  "[| Pf = PNfun ; guardedfun Pf |]
   ==> LFP ([[Pf]]Ffun) = UFP ([[Pf]]Ffun)"
by (simp add: semF_hasUFP_cms hasUFP_LFP_UFP)

(*----------- refinement -----------*)

(*** left ***)

lemma cspF_fp_induct_mix_ref_left_ALL:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = MIXmode ;
       f p <=F Q ;
       ALL p. (Pf p)<<f <=F f p |]
    ==> $p <=F Q"
apply (simp add: refF_semF)
apply (insert cms_fixpoint_induction_ref
       [of "[[Pf]]Ffun" "(%p. [[f p]]F)" "UFP ([[Pf]]Ffun)"])
apply (simp add: semF_guarded_LFP_UFP[THEN sym])
apply (simp add: LFP_fp semF_hasLFP_cpo)

apply (simp add: fold_order_prod_def)
apply (simp add: semF_subst_semFfun)
apply (simp add: mono_semFfun)
apply (simp add: contra_alpha_to_contst contraction_alpha_semFfun)
apply (simp add: to_distance_rs)
apply (simp add: order_prod_def)
apply (drule_tac x="p" in spec)+
apply (simp add: semF_LFP_cpo)
done

(*  csp law  *)

lemma cspF_fp_induct_mix_ref_left:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = MIXmode ;
       f p <=F Q ;
       !! p. (Pf p)<<f <=F f p |]
    ==> $p <=F Q"
by (simp add: cspF_fp_induct_mix_ref_left_ALL)

(*----------- equality -----------*)

(*** left ***)

lemma cspF_fp_induct_mix_eq_left_ALL:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = MIXmode ;
       f p =F Q ;
       ALL p. (Pf p)<<f =F f p |]
    ==> $p =F Q"
apply (simp add: eqF_semF)
apply (simp add: fun_eq_iff[THEN sym])
apply (simp add: semF_subst_semFfun)
apply (insert semF_LFP_fun_cpo[of Pf])
apply (simp add: semF_guarded_LFP_UFP)
apply (subgoal_tac "(%p. [[$p]]F) = (%p. [[f p]]F)")
apply (simp add: fun_eq_iff)

apply (rule hasUFP_unique_solution[of "[[Pf]]Ffun"])
apply (simp_all add: semF_hasUFP_cms)
apply (simp add: UFP_fp semF_hasUFP_cms)
done

(*  csp law  *)

lemma cspF_fp_induct_mix_eq_left:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = MIXmode ;
       f p =F Q ;
       !! p. (Pf p)<<f =F f p |]
    ==> $p =F Q"
by (simp add: cspF_fp_induct_mix_eq_left_ALL)

lemma cspF_fp_induct_mix_eq_right:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = MIXmode ;
       Q =F f p;
       !! p. f p =F (Pf p)<<f |]
    ==> Q =F $p"
apply (rule cspF_sym)
apply (rule cspF_fp_induct_mix_eq_left[of Pf f p Q])
apply (simp_all)
apply (rule cspF_sym)
apply (simp)
apply (rule cspF_sym)
apply (simp)
done

lemmas cspF_fp_induct_mix_left 
     = cspF_fp_induct_mix_ref_left cspF_fp_induct_mix_eq_left

lemmas cspF_fp_induct_mix_right 
     = cspF_fp_induct_cpo_ref_right cspF_fp_induct_mix_eq_right

(*=======================================================*
 |                                                       |
 |            mixing CPOmode and CMSmode                 |
 |                                                       |
 *=======================================================*)

lemma cspF_unwind:
   "[| Pf = PNfun ;
       FPmode = CPOmode
     | FPmode = CMSmode & guardedfun Pf
     | FPmode = MIXmode |]
     ==> $p =F Pf p"
apply (erule disjE)
apply (simp add: cspF_unwind_cpo)
apply (erule disjE)
apply (simp add: cspF_unwind_cms)
apply (simp add: cspF_unwind_cpo)
done

lemma cspF_fp_induct_ref_right:
   "[| Pf = PNfun ;
       FPmode = CPOmode
     | FPmode = CMSmode & guardedfun Pf
     | FPmode = MIXmode ;
       Q <=F f p;
       !! p. f p <=F (Pf p)<<f |]
    ==> Q <=F $p"
apply (erule disjE)
apply (simp add: cspF_fp_induct_cpo_right)
apply (erule disjE)
apply (simp add: cspF_fp_induct_cms_right)
apply (simp add: cspF_fp_induct_cpo_right)
done

lemma cspF_fp_induct_ref_left:
   "[| Pf = PNfun ;
       FPmode = CMSmode 
     | FPmode = MIXmode ;
       guardedfun Pf ;
       f p <=F Q ;
       !! p. (Pf p)<<f <=F f p |]
    ==> $p <=F Q"
apply (erule disjE)
apply (simp add: cspF_fp_induct_cms_left)
apply (simp add: cspF_fp_induct_mix_left)
done

lemma cspF_fp_induct_eq_left:
   "[| Pf = PNfun ;
       FPmode = CMSmode 
     | FPmode = MIXmode ;
       guardedfun Pf ;
       f p =F Q ;
       !! p. (Pf p)<<f =F f p |]
    ==> $p =F Q"
apply (erule disjE)
apply (simp add: cspF_fp_induct_cms_left)
apply (simp add: cspF_fp_induct_mix_left)
done

lemma cspF_fp_induct_eq_right:
   "[| Pf = PNfun ;
       FPmode = CMSmode 
     | FPmode = MIXmode ;
       guardedfun Pf ;
       Q =F f p;
       !! p. f p =F (Pf p)<<f |]
    ==> Q =F $p"
apply (erule disjE)
apply (simp add: cspF_fp_induct_cms_right)
apply (simp add: cspF_fp_induct_mix_right)
done

(*** cpo and cms ***)

lemmas cspF_fp_induct_right = cspF_fp_induct_ref_right cspF_fp_induct_eq_right
lemmas cspF_fp_induct_left = cspF_fp_induct_ref_left cspF_fp_induct_eq_left

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
