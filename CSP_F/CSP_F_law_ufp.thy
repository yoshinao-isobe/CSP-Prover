           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               February 2005               |
            |                   June 2005  (modified)   |
            |                 August 2005  (modified)   |
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

theory CSP_F_law_ufp
imports CSP_F_continuous CSP_F_contraction CSP_F_mono
        CSP_F_law_decompo CSP_T.CSP_T_law_ufp
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

lemma semF_hasUFP_cms: 
 "[| Pf = PNfun ; guardedfun (Pf) |]
  ==> [[Pf]]Ffun hasUFP"
apply (rule Banach_thm_EX)
apply (rule contraction_semFfun)
apply (simp)
done

lemma semF_UFP_cms:
  "[| Pf = PNfun ;
      guardedfun (Pf) ;
      FPmode = CMSmode |]
  ==> [[$p]]F = UFP ([[Pf]]Ffun) p"
apply (simp add: semF_def)
apply (simp add: semFf_Proc_name)
apply (simp add: MF_def)
apply (simp add: semFfix_def)
done

lemma semF_UFP_fun_cms:
  "[| Pf = PNfun ;
      guardedfun (Pf) ;
      FPmode = CMSmode |]
  ==> (%p. [[$p]]F) = UFP ([[Pf]]Ffun)"
apply (simp (no_asm) add: fun_eq_iff)
apply (simp add: semF_UFP_cms)
done

(*---------*
 |    MF   |
 *---------*)

lemma MF_fixed_point_cms:
      "[| (Pf::'p=>('p,'a) proc) = PNfun; guardedfun Pf ; FPmode = CMSmode|]
        ==> [[Pf]]Ffun (MF::'p => 'a domF) = (MF::'p => 'a domF)"
apply (simp add: MF_def)
apply (simp add: semFfix_def)
apply (rule UFP_fp)
apply (simp add: semF_hasUFP_cms)
done

(*---------*
 |  unique |
 *---------*)

lemma ALL_cspF_unique_cms:
  "[| Pf = PNfun ; guardedfun Pf ;
       FPmode = CMSmode ;
       ALL p. (Pf p) << f =F f p |] ==> ALL p. f p =F $p"
apply (simp add: eqF_def)
apply (simp add: fun_eq_iff[THEN sym])
apply (rule hasUFP_unique_solution[of "[[PNfun]]Ffun"])
apply (simp add: semF_hasUFP_cms)
apply (fold semF_def)

apply (simp add: semF_subst)
apply (simp add: semFfun_def)

apply (simp add: semF_UFP_fun_cms)
apply (simp add: UFP_fp semF_hasUFP_cms)
done

lemma cspF_unique_cms:
  "[| Pf = PNfun ; guardedfun Pf ;
       FPmode = CMSmode ;
       ALL p. (Pf p) << f =F f p |] ==> f p =F $p"
by (simp add: ALL_cspF_unique_cms)

(*-------------------------------------------------------*
 |                                                       |
 |           Fixpoint unwind (CSP-Prover rule)           |
 |                                                       |
 *-------------------------------------------------------*)

lemma ALL_cspF_unwind_cms:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = CMSmode |]
     ==> ALL p. ($p =F Pf p)"
apply (simp add: eqF_def)
apply (simp add: semFf_Proc_name)
apply (simp add: MF_def)
apply (simp add: semFfix_def)
apply (simp add: fun_eq_iff[THEN sym])
apply (simp add: semFf_semFfun)
apply (simp add: UFP_fp semF_hasUFP_cms)
done

(*  csp law  *)

lemma cspF_unwind_cms:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = CMSmode |]
     ==> $p =F Pf p"
by (simp add: ALL_cspF_unwind_cms)

(*-------------------------------------------------------*
 |                                                       |
 |    fixed point inducntion (CSP-Prover intro rule)     |
 |                                                       |
 *-------------------------------------------------------*)

(*----------- refinement -----------*)

(*** left ***)

lemma cspF_fp_induct_cms_ref_left_ALL:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = CMSmode ;
       f p <=F Q ;
       ALL p. (Pf p)<<f <=F f p |]
    ==> $p <=F Q"
apply (simp add: refF_semF)
apply (insert cms_fixpoint_induction_ref
       [of "[[Pf]]Ffun" "(%p. [[f p]]F)" "UFP ([[Pf]]Ffun)"])
apply (simp add: UFP_fp semF_hasUFP_cms)
apply (simp add: fold_order_prod_def)
apply (simp add: semF_subst_semFfun)
apply (simp add: mono_semFfun)

apply (simp add: contra_alpha_to_contst contraction_alpha_semFfun)
apply (simp add: to_distance_rs)
apply (simp add: order_prod_def)
apply (drule_tac x="p" in spec)+

apply (simp add: semF_UFP_cms)
done

(*  csp law  *)

lemma cspF_fp_induct_cms_ref_left:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = CMSmode ;
       f p <=F Q ;
       !! p. (Pf p)<<f <=F f p |]
    ==> $p <=F Q"
by (simp add: cspF_fp_induct_cms_ref_left_ALL)

(*** right ***)

lemma cspF_fp_induct_cms_ref_right_ALL:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = CMSmode ;
       Q <=F f p;
       ALL p. f p <=F (Pf p)<<f |]
    ==> Q <=F $p"
apply (simp add: refF_semF)
apply (insert cms_fixpoint_induction_rev
       [of "[[Pf]]Ffun" "(%p. [[f p]]F)" "UFP ([[Pf]]Ffun)"])
apply (simp add: UFP_fp semF_hasUFP_cms)
apply (simp add: fold_order_prod_def)
apply (simp add: semF_subst_semFfun)
apply (simp add: mono_semFfun)

apply (simp add: contra_alpha_to_contst contraction_alpha_semFfun)
apply (simp add: to_distance_rs)
apply (simp add: order_prod_def)
apply (drule_tac x="p" in spec)+

apply (simp add: semF_UFP_cms)
done

(*  csp law  *)

lemma cspF_fp_induct_cms_ref_right:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = CMSmode ;
       Q <=F f p;
       !! p. f p <=F (Pf p)<<f |]
    ==> Q <=F $p"
by (simp add: cspF_fp_induct_cms_ref_right_ALL)

(*----------- equality -----------*)

(*** left ***)

lemma cspF_fp_induct_cms_eq_left_ALL:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = CMSmode ;
       f p =F Q ;
       ALL p. (Pf p)<<f =F f p |]
    ==> $p =F Q"
apply (simp add: eqF_semF)
apply (simp add: fun_eq_iff[THEN sym])
apply (simp add: semF_subst_semFfun)
apply (insert semF_UFP_fun_cms[of Pf])
apply (simp)
apply (subgoal_tac "(%p. [[$p]]F) = (%p. [[f p]]F)")
apply (simp add: fun_eq_iff)

apply (rule hasUFP_unique_solution[of "[[Pf]]Ffun"])
apply (simp_all add: semF_hasUFP_cms)
apply (simp add: UFP_fp semF_hasUFP_cms)
done

(*  csp law  *)

lemma cspF_fp_induct_cms_eq_left:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = CMSmode ;
       f p =F Q;
       !! p. (Pf p)<<f =F f p |]
    ==> $p =F Q"
by (simp add: cspF_fp_induct_cms_eq_left_ALL)

lemma cspF_fp_induct_cms_eq_right:
   "[| Pf = PNfun ;
       guardedfun Pf ;
       FPmode = CMSmode ;
       Q =F f p;
       !! p. f p =F (Pf p)<<f |]
    ==> Q =F $p"
apply (rule cspF_sym)
apply (rule cspF_fp_induct_cms_eq_left[of Pf f p Q])
apply (simp_all)
apply (rule cspF_sym)
apply (simp)
apply (rule cspF_sym)
apply (simp)
done

lemmas cspF_fp_induct_cms_left 
     = cspF_fp_induct_cms_ref_left cspF_fp_induct_cms_eq_left

lemmas cspF_fp_induct_cms_right 
     = cspF_fp_induct_cms_ref_right cspF_fp_induct_cms_eq_right

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
