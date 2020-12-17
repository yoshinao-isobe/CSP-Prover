           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |               February 2005  (modified)   |
            |                   June 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2008         |
            |                   June 2008  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_Main
imports CSP_F_tactic CSP_F_surj CSP_T_Main
        CSP_F_T_domain CSP_F_MF_MT
begin

(*--------------------------------------------*
 |                                            |
 |    decomposition considering refinement    |
 |                                            |
 *--------------------------------------------*)

lemmas cspF_mono_ref = cspF_free_mono
   cspF_Act_prefix_mono cspF_Ext_pre_choice_mono 
   cspF_IF_mono cspF_decompo_subset

lemmas cspF_decompo_ref = cspF_mono_ref cspF_cong

(*-------------------------------------------------------*
 |                                                       |
 |  The folloing def have already added in CSP_T         |
 |                                                       |
 |   Procfun_def                                         |
 |   ProcX_def                                           |
 |   gSKIPX_def                                          |
 |   gProcX_def                                          |
 |   nohideX_def                                         |
 |                                                       |
 *-------------------------------------------------------*)

(*----------------------------------------------------------------------*
 |                                                                      |
 |  To unfold (resp. fold) syntactic-sugar for Ext_ and Int_pre_choices |
 |  choices, use "unfold csp_prefix_ss_def"                             |
 |                                                                      |
 *----------------------------------------------------------------------*)

(*------------------------------------*
 |                                    |
 |    laws automatically applied      |
 |                                    |
 *------------------------------------*)

(* intro! intro? are automatically applied by "rule".     *)
(* intro! is automatically applied by "rules" and "auto". *)

(* CSP_F_law_basic *)

declare cspF_commut                                  [simp]

(* CSP_F_law_ref *)

declare cspF_Int_choice_right                        [intro!]
declare cspF_Rep_int_choice_right                    [intro!]

(* CSP_F_law_SKIP *)

declare cspF_SKIP_DIV_resolve                        [simp]
lemmas  cspF_SKIP_DIV_resolve_sym                    [simp]
      = cspF_SKIP_DIV_resolve[THEN cspF_sym]

(* CSP_F_law_decompo *)

declare cspF_rm_head                                 [intro!]
declare cspF_decompo                                 [simp]

(* CSP_F_law_dist *)

declare cspF_all_dist                                [simp]
lemmas  cspF_all_dist_sym                            [simp]
      = cspF_all_dist[THEN cspF_sym]

(*
declare cspF_unwind                                  [simp]
lemmas  cspF_unwind_sym                              [simp]
      = cspF_unwind[THEN cspF_sym]
*)

(* CSP_F_law_step *)

(*
declare cspF_step                                    [simp]
lemmas  cspF_step_sym                                [simp]
      = cspF_step[THEN cspF_sym]
*)

declare cspF_step_rw                                 [simp]
lemmas  cspF_step_rw_sym                             [simp]
      = cspF_step_rw[THEN cspF_sym]

(* CSP_F_law_etc *)

declare cspF_choice_IF                               [simp]

(* CSP_F_DIV_top *)

declare cspF_DIV_top                                 [simp]

(* Alpha_Parallel *)

declare cspF_decompo_Alpha_parallel                  [simp]



(* ------------------------------------------------------------------- *

      The lemma "cspF_Rep_int_simp" is not automatically applied by
      tactics. If you want to simplify indexes in replicated internal
      choice, then the following command will be useful.

         apply (cspF_simp cspF_Rep_int_simp)

 * ------------------------------------------------------------------- *)

lemmas cspF_Rep_int_simp = 
          cspF_choice_delay
          cspF_Rep_int_choice_sepa
          cspF_Rep_int_choice_f_map


(* -------------------------------------------------- *
        The following lemma is added to "simp"
        This is applied for simplifying compostions
        of functions in internal choices.
        (See the bottom of CSP_F_law_basic.thy)
 * -------------------------------------------------- *)

lemma compo_inj_is_inj: "[| inj f ; inj g |] ==> inj (f o g)"
by (auto simp add: inj_on_def)


(* -------------------------------------------------- *
           convenient lemmas for event-sets
 * -------------------------------------------------- *)

(*
declare simp_event_set [simp]
*)

end
