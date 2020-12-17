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

theory CSP_T_law_ufp
imports CSP_T_continuous CSP_T_contraction CSP_T_mono CSP_T_law_decompo
begin

(*****************************************************************

         1. cms fixed point theory in CSP-Prover
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
 |                        CMS                            |
 |                                                       |
 *=======================================================*)

(*-------------*
 |  existency  |
 *-------------*)

lemma semT_hasUFP_cms: 
 "[| Pf = PNfun ; guardedfun (Pf) |]
  ==> [[Pf]]Tfun hasUFP"
apply (rule Banach_thm_EX)
apply (rule contraction_semTfun)
apply (simp)
done

lemma semT_UFP_cms:
  "[| Pf = PNfun ;
      guardedfun (Pf) ;
      FPmode = CMSmode |]
  ==> [[$p]]T = UFP [[Pf]]Tfun p"
apply (simp add: semT_def semTf_def)
apply (simp add: traces_iff)
apply (simp add: MT_def)
apply (simp add: semTfix_def)
done

lemma semT_UFP_fun_cms:
  "[| Pf = PNfun ;
      guardedfun (Pf) ;
      FPmode = CMSmode |]
  ==> (%p. [[$p]]T) = UFP [[Pf]]Tfun"
apply (simp (no_asm) add: fun_eq_iff)
apply (simp add: semT_UFP_cms)
done

(*---------*
 |    MT   |
 *---------*)

lemma MT_fixed_point_cms:
      "[| (Pf::'p=>('p,'a) proc) = PNfun; guardedfun Pf ; FPmode = CMSmode|]
        ==> [[Pf]]Tfun (MT::'p => 'a domT) = (MT::'p => 'a domT)"
apply (simp add: MT_def)
apply (simp add: semTfix_def)
apply (rule UFP_fp)
apply (simp add: semT_hasUFP_cms)
done

(*---------*
 |  unique |
 *---------*)

lemma ALL_cspT_unique_cms:
  "[| Pf = PNfun ; guardedfun Pf ;
       FPmode = CMSmode ;
       ALL p. (Pf p) << f =T f p |] ==> ALL p. f p =T $p"
apply (simp add: cspT_semantics)
apply (simp add: fun_eq_iff[THEN sym])
apply (rule hasUFP_unique_solution[of "[[PNfun]]Tfun"])
apply (simp add: semT_hasUFP_cms)

apply (simp add: traces_subst)
apply (simp add: semTfun_def semTf_def)

apply (fold semTf_def semT_def)
apply (simp add: semT_UFP_fun_cms)
apply (simp add: UFP_fp semT_hasUFP_cms)
done

lemma cspT_unique_cms:
  "[| Pf = PNfun ; guardedfun Pf ;
       FPmode = CMSmode ;
       ALL p. (Pf p) << f =T f p |] ==> f p =T $p"
by (simp add: ALL_cspT_unique_cms)

(*-------------------------------------------------------*
 |                                                       |
 |           Fixpoint unwind (CSP-Prover rule)           |
 |                                                       |
 *-------------------------------------------------------*)

lemma ALL_cspT_unwind_cms:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = CMSmode |]
     ==> ALL p. ($p =T Pf p)"
apply (simp add: cspT_semantics)
apply (simp add: traces_iff)
apply (simp add: MT_def)
apply (simp add: semTfix_def)
apply (simp add: fun_eq_iff[THEN sym])
apply (simp add: traces_semTfun)
apply (simp add: UFP_fp semT_hasUFP_cms)
done

(*  csp law  *)

lemma cspT_unwind_cms:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = CMSmode |]
     ==> $p =T Pf p"
by (simp add: ALL_cspT_unwind_cms)

(*-------------------------------------------------------*
 |                                                       |
 |    fixed point inducntion (CSP-Prover intro rule)     |
 |                                                       |
 *-------------------------------------------------------*)

(*----------- refinement -----------*)

(*** left ***)

lemma cspT_fp_induct_cms_ref_left_ALL:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = CMSmode ;
       f p <=T Q ;
       ALL p. (Pf p)<<f <=T f p |]
    ==> $p <=T Q"
apply (simp add: refT_semT)
apply (insert cms_fixpoint_induction_ref
       [of "[[Pf]]Tfun" "(%p. [[f p]]T)" "UFP [[Pf]]Tfun"])
apply (simp add: UFP_fp semT_hasUFP_cms)
apply (simp add: fold_order_prod_def)
apply (simp add: semT_subst_semTfun)
apply (simp add: mono_semTfun)

apply (simp add: contra_alpha_to_contst contraction_alpha_semTfun)
apply (simp add: to_distance_rs)
apply (simp add: order_prod_def)
apply (drule_tac x="p" in spec)+
apply (simp add: semT_UFP_cms)
done

(*  csp law  *)

lemma cspT_fp_induct_cms_ref_left:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = CMSmode ; 
       f p <=T Q;
       !! p. (Pf p)<<f <=T f p |]
    ==> $p <=T Q"
by (simp add: cspT_fp_induct_cms_ref_left_ALL)

(*** right ***)

lemma cspT_fp_induct_cms_ref_right_ALL:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = CMSmode ;
       Q <=T f p;
       ALL p. f p <=T (Pf p)<<f |]
    ==> Q <=T $p"
apply (simp add: refT_semT)
apply (insert cms_fixpoint_induction_rev
       [of "[[Pf]]Tfun" "(%p. [[f p]]T)" "UFP [[Pf]]Tfun"])
apply (simp add: UFP_fp semT_hasUFP_cms)
apply (simp add: fold_order_prod_def)
apply (simp add: semT_subst_semTfun)
apply (simp add: mono_semTfun)

apply (simp add: contra_alpha_to_contst contraction_alpha_semTfun)
apply (simp add: to_distance_rs)
apply (simp add: order_prod_def)
apply (drule_tac x="p" in spec)+

apply (simp add: semT_UFP_cms)
done

(*  csp law  *)

lemma cspT_fp_induct_cms_ref_right:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = CMSmode ;
       Q <=T f p;
       !! p. f p <=T (Pf p)<<f |]
    ==> Q <=T $p"
by (simp add: cspT_fp_induct_cms_ref_right_ALL)

(*----------- equality -----------*)

(*** left ***)

lemma cspT_fp_induct_cms_eq_left_ALL:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = CMSmode ;
       f p =T Q ;
       ALL p. (Pf p)<<f =T f p |]
    ==> $p =T Q"
apply (simp add: eqT_semT)
apply (simp add: fun_eq_iff[THEN sym])
apply (simp add: semT_subst_semTfun)
apply (insert semT_UFP_fun_cms[of Pf])
apply (simp)
apply (subgoal_tac "(%p. [[$p]]T) = (%p. [[f p]]T)")
apply (simp add: fun_eq_iff)

apply (rule hasUFP_unique_solution[of "[[Pf]]Tfun"])
apply (simp_all add: semT_hasUFP_cms)
apply (simp add: UFP_fp semT_hasUFP_cms)
done

(*  csp law  *)

lemma cspT_fp_induct_cms_eq_left:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = CMSmode ;
       f p =T Q ;
       !! p. (Pf p)<<f =T f p |]
    ==> $p =T Q"
by (simp add: cspT_fp_induct_cms_eq_left_ALL)

lemma cspT_fp_induct_cms_eq_right:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = CMSmode ;
       Q =T f p;
       !! p. f p =T (Pf p)<<f |]
    ==> Q =T $p"
apply (rule cspT_sym)
apply (rule cspT_fp_induct_cms_eq_left[of Pf f p Q])
apply (simp_all)
apply (rule cspT_sym)
apply (simp)
apply (rule cspT_sym)
apply (simp)
done

lemmas cspT_fp_induct_cms_left 
     = cspT_fp_induct_cms_ref_left cspT_fp_induct_cms_eq_left

lemmas cspT_fp_induct_cms_right 
     = cspT_fp_induct_cms_ref_right cspT_fp_induct_cms_eq_right

(****************** to add them again ******************)
(*
declare Union_image_eq [simp]
declare Inter_image_eq [simp]
*)
(* 2017
declare Sup_image_eq [simp]
declare Inf_image_eq [simp]
*)
end
