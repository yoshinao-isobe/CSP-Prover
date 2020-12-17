           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |               February 2005  (modified)   |
            |                   June 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_Main
imports CSP_T_tactic CSP_T_surj
begin

(*--------------------------------------------*
 |                                            |
 |    decomposition considering refinement    |
 |                                            |
 *--------------------------------------------*)

lemmas cspT_mono_ref = cspT_free_mono
   cspT_Act_prefix_mono cspT_Ext_pre_choice_mono 
   cspT_IF_mono cspT_decompo_subset

lemmas cspT_decompo_ref = cspT_mono_ref cspT_cong

(*-------------------------------------------------------*
 |                                                       |
 |      adding ... to automatically check Procfun        |
 |                                                       |
 *-------------------------------------------------------*)


(*-------------------------------------------------------------*
 |                                                             |
 |  Users may be sometimes required to apply "Int_prefix_def"  |
 |  for unfoling "! x:X -> P". Do you like the following ?     |
 |                                                             |
 |  declare Int_pre_choice_def                     [simp]      |
 |                                                             |
 |  Users may be sometimes required to apply "Send_prefix_def" |
 |  for unfoling "a ! x: -> P". Do you like the following ?    |
 |                                                             |
 |  declare Send_prefix_def                        [simp]      |
 |                                                             |
 |  Users may be sometimes required to apply "Rec_prefix_def"  |
 |  for unfoling "a ? x:X -> P". Do you like the following ?   |
 |                                                             |
 |  declare Rec_prefix_def                         [simp]      |
 |                                                             |
 *-------------------------------------------------------------*)

(*                           NO                                *)

(*----------------------------------------------------------------------*
 |                                                                      |
 |  To unfold (resp. fold) syntactic-sugar for Ext_ and Int_pre_choices |
 |  choices, use "unfold csp_prefix_ss_def"                             |
 |                                                                      |
 *----------------------------------------------------------------------*)

(*---------------------------------------------------------------------*
 | Nondet_send_prefix_def : non-deterministic sending                  |
 | Rep_int_choice_fun_def : Replicated internal choice with a function |
 *---------------------------------------------------------------------*)

(*   "inj_on_def" is needed for resolving (inv f) in R_Prefix_def *)
(*  declare inj_on_def                                 [simp]     *)

(*------------------------------------*
 |                                    |
 |    laws automatically applied      |
 |                                    |
 *------------------------------------*)

(* intro! intro? are automatically applied by "rule".     *)
(* intro! is automatically applied by "rules" and "auto". *)

(* CSP_T_law_basic *)

declare cspT_commut                                  [simp]

(* CSP_T_law_ref *)

declare cspT_Int_choice_right                        [intro!]
declare cspT_Rep_int_choice_right                    [intro!]

(* CSP_T_law_SKIP *)

declare cspT_SKIP_DIV_resolve                        [simp]
lemmas  cspT_SKIP_DIV_resolve_sym                    [simp]
      = cspT_SKIP_DIV_resolve[THEN cspT_sym]

(* CSP_T_law_decompo *)

declare cspT_rm_head                                 [intro!]
declare cspT_decompo                                 [simp]

(* CSP_T_law_dist *)

declare cspT_all_dist                                [simp]
lemmas  cspT_all_dist_sym                            [simp]
      = cspT_all_dist[THEN cspT_sym]

(*
declare cspT_unwind                                  [simp]
lemmas  cspT_unwind_sym                              [simp]
      = cspT_unwind[THEN cspT_sym]
*)

(* CSP_T_law_step *)
(*
declare cspT_step                                    [simp]
lemmas  cspT_step_sym                                [simp]
      = cspT_step[THEN cspT_sym]
*)

declare cspT_step_rw                                 [simp]
lemmas  cspT_step_rw_sym                             [simp]
      = cspT_step_rw[THEN cspT_sym]


(* CSP_T_law_etc *)

declare cspT_choice_IF                               [simp]

(* top *)

declare cspT_top                                     [simp]
declare cspT_Ent_choice_left_ref                     [simp]

declare cspT_decompo_Alpha_parallel                  [simp]


(*-------------------[test of CSP_T]------------------------*

datatype Event = eva | evb

datatype PNSpec = AB
datatype PNImpl = A

consts 
  PNfunSpec :: "PNSpec => (PNSpec, Event) proc"
  PNfunImpl :: "PNImpl => (PNImpl, Event) proc"

primrec
  "PNfunSpec   AB = eva -> $AB |~| evb -> $AB"

primrec
  "PNfunImpl   A = eva -> $A"

defs (overloaded)
Set_PNfunSpec_def : "PNfun == PNfunSpec"
Set_PNfunImpl_def : "PNfun == PNfunImpl"
FPmode_def        : "FPmode == CMSmode"

declare Set_PNfunSpec_def [simp]
declare Set_PNfunImpl_def [simp]
declare FPmode_def        [simp]

lemma example_test_01: "PNfun AB = eva -> $AB |~| evb -> $AB"
by (simp)

lemma example_test_02: "PNfun A = eva -> $A"
by (simp)

consts 
  Spec_Impl :: "PNSpec => (PNImpl, Event) proc"

primrec
  "Spec_Impl  AB = $A"

consts 
  Spec :: "(PNSpec, Event) proc"
  Impl :: "(PNImpl, Event) proc"

defs
  Spec_def : "Spec == $AB"
  Impl_def : "Impl == $A"

lemma guardedfun_ex[simp]: 
  "guardedfun PNfunSpec"
  "guardedfun PNfunImpl"
by (simp add: guardedfun_def, rule allI, induct_tac p, simp)+

lemma example_test_fp: "Spec <=T Impl"
apply (simp add: Spec_def Impl_def)
apply (rule cspT_fp_induct_left[of _ "Spec_Impl"])
apply (simp_all)
apply (simp)

apply (induct_tac p)
apply (simp)

apply (rule cspT_rw_right)
apply (rule cspT_unwind)
apply (simp_all)
apply (simp)

apply (rule cspT_Int_choice_left1)
apply (simp)
done

-- you have to note that you cannot prove "$AB <=T $A"
-- because $AB has a wider type "(PNSpec,'s) proc" than
-- "(PNSpec,Event) proc".

 *-------------------[test of CSP_T]------------------------*)

end
