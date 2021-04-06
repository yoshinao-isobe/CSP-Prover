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
            |        CSP-Prover on Isabelle2008         |
            |                   June 2008  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2012         |
            |               November 2012  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |	    
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_tactic
imports CSP_T_law CSP_T_law_etc
begin

(*****************************************************************

         1. tactic
         2.
         3. 
         4. 

 *****************************************************************)

(*================================================*
 |                                                |
 |                  Tacticals                     |
 |                                                |
 *================================================*)

lemmas cspT_all_dist = cspT_dist cspT_Dist cspT_Ext_dist

                       cspT_Seq_compo_hide_dist
                       cspT_Interleave_hide_dist
                       cspT_Seq_compo_renaming_dist
                       cspT_Interleave_renaming_dist

                       cspT_dist_Alpha_Parallel
                       cspT_Dist_Alpha_Parallel

lemmas cspT_choice_IF = cspT_choice_rule cspT_IF cspT_Interleave_unit 
lemmas cspT_pre_step  = cspT_Alpha_Parallel_step

lemmas cspT_Act_prefix_step_sym = cspT_Act_prefix_step[THEN cspT_sym]


ML \<open>
    val CSPT_reflex                    = @{thms cspT_reflex} ;
    val CSPT_rw_flag_left              = @{thms cspT_rw_flag_left} ;
    val CSPT_rw_flag_right             = @{thms cspT_rw_flag_right} ;

    val CSPT_tr_flag_left              = @{thms cspT_tr_flag_left} ;
    val CSPT_tr_flag_right             = @{thms cspT_tr_flag_right} ;

    val CSPT_light_step                = @{thms cspT_light_step_rw} ;
    val CSPT_SKIP_DIV_resolve          = @{thms cspT_SKIP_DIV_resolve} ;

    val CSPT_unwind                    = @{thms cspT_unwind} ;

    val CSPT_SKIP_DIV_sort             = @{thms cspT_SKIP_DIV_sort};
    val CSPT_Ext_Int                   = @{thms cspT_Ext_Int} ;        (* only T *)

    val CSPT_rw_flag_leftE             = @{thms cspT_rw_flag_leftE} ;  (* E *)
    val CSPT_rw_flag_rightE            = @{thms cspT_rw_flag_rightE} ; (* E *)

    val CSPT_Act_prefix_step_sym       = @{thms cspT_Act_prefix_step_sym} ;


\<close>

ML \<open>
 val CSPT_free_decompo_flag     = @{thms cspT_free_decompo_flag} ;
 val CSPT_decompo               = @{thms cspT_decompo_ss} ;

 val CSPT_all_dist              = @{thms cspT_all_dist} ;
 val CSPT_choice_IF             = @{thms cspT_choice_IF} ;
 val CSPT_step                  = @{thms cspT_step_rw} ;

 val CSPT_choice_delay               = @{thms cspT_choice_delay} ;          (* new *)
 val CSPT_Rep_int_choice_sepa        = @{thms cspT_Rep_int_choice_sepa} ;   (* new *)
 val CSPT_Rep_int_choice_f_map       = @{thms cspT_Rep_int_choice_f_map} ;  (* new *)

 val CSPT_first_prefix_ss            = @{thms cspT_first_prefix_ss} ;
 val CSPT_prefix_Renaming_in_step    = @{thms cspT_prefix_Renaming_in_step} ;
 val CSPT_prefix_Renaming_notin_step = @{thms cspT_prefix_Renaming_notin_step} ;
 val CSPT_Renaming_fun_step          = @{thms cspT_Renaming_step} ;

(* the name is changed in Isabelle 2017
 val Split_if                        = @{thm split_if} ;
*)
 val If_split                        = @{thm if_split} ;

 val CSPT_pre_step                   = @{thms cspT_pre_step} ;             (* new *)

\<close>

(* ===================================================== *
 |                                                       |
 |                                                       |
 |          Templates (written by equations)             |
 |                                                       |
 |                                                       |
 * ===================================================== *)

(*--------------------------------------*
 |  one_step or deep, (no_asm) or asm   |
 *--------------------------------------*)

(* simptac :: context -> int -> tactic *)
 
ML \<open>
fun templateT_main_tac simptac decompo f ctxt thms =
 CHANGED (
  EVERY
   [REPEAT (
     FIRST 
      [(CHANGED (simptac (ctxt |> Splitter.del_split If_split) 1)),                             
                 (* <-- simptac *)
                 (* no if_split *)
                
          (f ctxt thms),
          (EVERY [ resolve_tac ctxt CSPT_rw_flag_left 1 , 
                   resolve_tac ctxt decompo 1 ]),            (* <-- decompo *)

       (EVERY [ TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1), 
                TRY (resolve_tac ctxt OFF_Not_Rewrite_Flag 1), 
                resolve_tac ctxt CSPT_reflex 1 ])
(*
       (resolve_tac OFF_All_Flag_True 1)
*)

   ]) ,

(* (f ctxt thms),
             (simpset_of ctxt addsimps OFF_All_Flag_True
                               delsimps if_split)))]) 
*)
(*              (simpset_of (ctxt addsimps OFF_All_Flag_True
               |> Splitter.add_split @{thm if_split}))))]) *) 

  (ALLGOALS (asm_full_simp_tac 
               (((ctxt addsimps OFF_All_Flag_True)
               |> Splitter.del_split If_split))))])

(*                             )))])   *)

\<close>

ML \<open>
fun templateT_left_tac simptac decompo f ctxt thms =
 CHANGED (
  EVERY
   [resolve_tac ctxt CSPT_rw_flag_left 1,
    templateT_main_tac simptac decompo f ctxt thms ])
\<close>

ML \<open>
fun templateT_right_tac simptac decompo f ctxt thms =
 CHANGED (
  EVERY
   [resolve_tac ctxt CSPT_rw_flag_right 1,
    templateT_main_tac simptac decompo f ctxt thms ])
\<close>


ML \<open>
fun templateT_both_tac simptac decompo f ctxt thms =
 CHANGED (
  EVERY
   [TRY (templateT_left_tac simptac decompo f ctxt thms),
    TRY (templateT_right_tac simptac decompo f ctxt thms)])
\<close>

(*

 simptac:
  full_simp_tac     (no_asm)
  asm_full_simp_tac (asm)

 decompo:
  CSPT_decompo            (any deep)
  CSPT_free_decompo_flag  (one step)

*)

(* ===================================================== *
 |                                                       |
 |                                                       |
 |          Templates (written by refinements)           |
 |                                                       |
 |                                                       |
 * ===================================================== *)

(*--------------------------*
 |  trans, (no_asm) or asm  |
 *--------------------------*)

ML \<open>
fun templateT_refine_main_tac simptac tr f ctxt thms =
 CHANGED (
  EVERY
   [REPEAT (
     FIRST 
      [(CHANGED (simptac                             (* <-- simptac *)
(*                (simpset_of ctxt |> fold Splitter.del_split Split_if) 1)),  *)
(*                (simpset_of (ctxt |> Splitter.del_split Split_if)))), *)  
                  (ctxt |> Splitter.del_split If_split) 1)),  
                (* no if_split *)

       (f ctxt thms),

       (EVERY [ resolve_tac ctxt tr 1 ,                         (* <-- transitivity *)
                resolve_tac ctxt CSPT_free_decompo_flag 1 ]),   (* <-- one step *)

       (EVERY [ TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1), 
                TRY (resolve_tac ctxt OFF_Not_Rewrite_Flag 1), 
                resolve_tac ctxt CSPT_reflex 1 ]),

       (resolve_tac ctxt OFF_All_Flag_True 1)]) ,

    (ALLGOALS (asm_full_simp_tac 
               (((ctxt addsimps OFF_All_Flag_True)
               |> Splitter.del_split If_split))))])
(*               
    (ALLGOALS (asm_full_simp_tac 
              (simpset_of ctxt addsimps OFF_All_Flag_True
                              |> fold Splitter.del_split If_split)))])
*)
\<close>

ML \<open>
fun templateT_refine_left_tac simptac f ctxt thms =
 CHANGED (
  EVERY
   [resolve_tac ctxt CSPT_tr_flag_left 1,
    templateT_refine_main_tac simptac CSPT_tr_flag_left f ctxt thms ])
\<close>

ML \<open>
fun templateT_refine_right_tac simptac f ctxt thms =
 CHANGED (
  EVERY
   [resolve_tac ctxt CSPT_tr_flag_right 1,
    templateT_refine_main_tac simptac CSPT_tr_flag_right f ctxt thms ])
\<close>

(*

 simptac:
  full_simp_tac     (no_asm)
  asm_full_simp_tac (asm)

*)



(* ===================================================== *
                       Cores 
 * ===================================================== *)

(* ----- simp ----- *)

ML \<open>
fun cspT_simp_core ctxt thms =
       (EVERY [ (* TRY (resolve_tac OFF_Not_Decompo_Flag 1),  *)
                FIRST [ resolve_tac ctxt CSPT_choice_IF 1,
                        resolve_tac ctxt thms 1 ]])
\<close>

(* ----- renaming ----- *)

ML \<open>
fun cspT_ren_core ctxt thms =
       (EVERY [ (* TRY (resolve_tac OFF_Not_Decompo_Flag 1),  *)
                FIRST [ resolve_tac ctxt CSPT_choice_IF 1,
                        resolve_tac ctxt thms 1,
                        resolve_tac ctxt CSPT_all_dist 1,
                        resolve_tac ctxt CSPT_prefix_Renaming_in_step 1,
                        resolve_tac ctxt CSPT_prefix_Renaming_notin_step 1,
                        resolve_tac ctxt CSPT_Renaming_fun_step 1 ]])
\<close>

(* ----- hsf ----- *)

ML \<open>
fun cspT_hsf_core ctxt thms =

       (EVERY [ (* TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1),  *)
                FIRST [ resolve_tac ctxt CSPT_choice_IF 1,
                        resolve_tac ctxt thms 1,
                        resolve_tac ctxt CSPT_all_dist 1,
                        resolve_tac ctxt CSPT_prefix_Renaming_in_step 1,
                        resolve_tac ctxt CSPT_prefix_Renaming_notin_step 1,
                        resolve_tac ctxt CSPT_Renaming_fun_step 1,
                        resolve_tac ctxt CSPT_first_prefix_ss 1,
                        resolve_tac ctxt CSPT_pre_step 1,
                        resolve_tac ctxt CSPT_SKIP_DIV_sort 1,
                        resolve_tac ctxt CSPT_SKIP_DIV_resolve 1,
                        resolve_tac ctxt CSPT_step 1
(*
                        resolve_tac ctxt CSPT_choice_delay 1,        
                        resolve_tac ctxt CSPT_Rep_int_choice_sepa 1, 
                        resolve_tac ctxt CSPT_Rep_int_choice_f_map 1,
                        resolve_tac ctxt CSPT_unwind 1 
*)
                        ]])
\<close>

(* ----- auto ----- *)

ML \<open>
fun cspT_auto_core ctxt thms =

       (EVERY [ (* TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1),  *)
                FIRST [ resolve_tac ctxt CSPT_choice_IF 1,
                        resolve_tac ctxt thms 1,
                        resolve_tac ctxt CSPT_all_dist 1,
                        resolve_tac ctxt CSPT_prefix_Renaming_in_step 1,
                        resolve_tac ctxt CSPT_prefix_Renaming_notin_step 1,
                        resolve_tac ctxt CSPT_Renaming_fun_step 1,
                        resolve_tac ctxt CSPT_first_prefix_ss 1,
                        resolve_tac ctxt CSPT_pre_step 1,
                        resolve_tac ctxt CSPT_SKIP_DIV_sort 1,
                        resolve_tac ctxt CSPT_SKIP_DIV_resolve 1,
                        resolve_tac ctxt CSPT_step 1,
                        resolve_tac ctxt CSPT_choice_delay 1,         (* new *)
                        resolve_tac ctxt CSPT_Rep_int_choice_sepa 1,  (* new *)
                        resolve_tac ctxt CSPT_Rep_int_choice_f_map 1, (* new *)
                        resolve_tac ctxt CSPT_unwind 1 ]])
\<close>

(* ----- unwinding ----- *)

ML \<open>
fun cspT_unwind_core ctxt thms =

       (EVERY [ (* TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1),  *)
                FIRST [ resolve_tac ctxt CSPT_choice_IF 1,
                        resolve_tac ctxt thms 1,
                        resolve_tac ctxt CSPT_unwind 1 ]])
\<close>

(* ----- dist ----- *)

ML \<open>
fun cspT_dist_core ctxt thms =

       (EVERY [ (* TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1), *)
                FIRST [ resolve_tac ctxt CSPT_choice_IF 1,
                        resolve_tac ctxt thms 1,
                        resolve_tac ctxt CSPT_all_dist 1]])
\<close>

(* ----- step ----- *)

ML \<open>
fun cspT_step_core ctxt thms =

       (EVERY [ (* TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1), *)
                FIRST [ resolve_tac ctxt CSPT_choice_IF 1,
                        resolve_tac ctxt thms 1,
                        resolve_tac ctxt CSPT_prefix_Renaming_in_step 1,
                        resolve_tac ctxt CSPT_prefix_Renaming_notin_step 1,
                        resolve_tac ctxt CSPT_Renaming_fun_step 1,
                        resolve_tac ctxt CSPT_first_prefix_ss 1,
                        resolve_tac ctxt CSPT_pre_step 1,
                        resolve_tac ctxt CSPT_SKIP_DIV_sort 1,
                        resolve_tac ctxt CSPT_SKIP_DIV_resolve 1,
                        resolve_tac ctxt CSPT_step 1 ]])

\<close>

(* ----- light_step ----- *)

ML \<open>
fun cspT_light_step_core ctxt thms =

       (EVERY [ (* TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1), *)
                FIRST [ resolve_tac ctxt CSPT_choice_IF 1,
                        resolve_tac ctxt thms 1,
                        resolve_tac ctxt CSPT_first_prefix_ss 1,
                        resolve_tac ctxt CSPT_light_step 1 ]])

\<close>


(* ----- prefix ----- *)

ML \<open>
fun cspT_prefix_core ctxt thms =

       (EVERY [ (* TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1), *)
                FIRST [ resolve_tac ctxt CSPT_choice_IF 1,
                        resolve_tac ctxt thms 1,
                        resolve_tac ctxt CSPT_Act_prefix_step_sym 1]])
\<close>

(* ----- choice ----- *)

ML \<open>
fun cspT_choice_core ctxt thms =

       (EVERY [ (* TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1), *)
                FIRST [ resolve_tac ctxt CSPT_choice_IF 1,
                        resolve_tac ctxt thms 1,
                        resolve_tac ctxt CSPT_Ext_Int 1]])
\<close>


(*

 simptac:
  full_simp_tac     (no_asm)
  asm_full_simp_tac (asm)

 decompo:
  CSPT_decompo            (any deep)
  CSPT_free_decompo_flag  (one step)

*)


(* ===================================================== *
                   Methods (instances)
 * ===================================================== *)

(*=================================================*
 |                                                 |
 |                     asm                         |
 |                                                 |
 *=================================================*)

(*------------------------*
 |  simp (one step, asm)  |
 *------------------------*)

method_setup cspT_asm_left =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_left_tac 
                    asm_full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_simp_core ctxt thms)) \<close>
  "simplify left process with using assumption"

method_setup cspT_asm_right =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_right_tac 
                    asm_full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_simp_core ctxt thms)) \<close>
  "simplify right process with using assumption"

method_setup cspT_asm =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_both_tac 
                    asm_full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_simp_core ctxt thms)) \<close>
  "simplify both processes with using assumption"

(*------------------------*
 |    simp (deep, asm)    |
 *------------------------*)

method_setup cspT_asm_deep_left =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_left_tac 
                    asm_full_simp_tac
                    CSPT_decompo
                    cspT_simp_core ctxt thms)) \<close>
  "deeply simplify left process with using assumption"

method_setup cspT_asm_deep_right =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_right_tac 
                    asm_full_simp_tac
                    CSPT_decompo
                    cspT_simp_core ctxt thms)) \<close>
  "deeply simplify right process with using assumption"

method_setup cspT_asm_deep =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_both_tac 
                    asm_full_simp_tac
                    CSPT_decompo
                    cspT_simp_core ctxt thms)) \<close>
  "deeply simplify both processes with using assumption"

(*=================================================*
 |                                                 |
 |                     simp                        |
 |                                                 |
 *=================================================*)

(*---------------------------------*
 |   simp (one step, no asm use)   |
 *---------------------------------*)

method_setup cspT_simp_left =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_left_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_simp_core ctxt thms)) \<close>
  "simplify left process without using assumptions"

method_setup cspT_simp_right =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_right_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_simp_core ctxt thms)) \<close>
  "simplify right process without using assumptions"

method_setup cspT_simp =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_both_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_simp_core ctxt thms)) \<close>
  "simplify both processes without using assumptions"

(*-----------------------------*
 |   simp (deep, no asm use)   |
 *-----------------------------*)

method_setup cspT_simp_deep_left =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_left_tac 
                    full_simp_tac
                    CSPT_decompo
                    cspT_simp_core ctxt thms)) \<close>
  "deeply simplify left process without using assumptions"

method_setup cspT_simp_deep_right =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_right_tac 
                    full_simp_tac
                    CSPT_decompo
                    cspT_simp_core ctxt thms)) \<close>
  "deeply simplify right process without using assumptions"

method_setup cspT_simp_deep =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_both_tac 
                    full_simp_tac
                    CSPT_decompo
                    cspT_simp_core ctxt thms)) \<close>
  "deeply simplify both processes without using assumptions"

(*=================================================*
 |                                                 |
 |                    renaming                     |
 |                                                 |
 *=================================================*)

(*---------------------------------*
 | renaming (one step, no asm use) |
 *---------------------------------*)

method_setup cspT_ren_left =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_left_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_ren_core ctxt thms)) \<close>
  "rename left process without using assumptions"

method_setup cspT_ren_right =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_right_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_ren_core ctxt thms)) \<close>
  "rename right process without using assumptions"

method_setup cspT_ren =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_both_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_ren_core ctxt thms)) \<close>
  "rename both processes without using assumptions"

(*---------------------------------*
 |   renaming (deep, no asm use)   |
 *---------------------------------*)

method_setup cspT_ren_deep_left =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_left_tac 
                    full_simp_tac
                    CSPT_decompo
                    cspT_ren_core ctxt thms)) \<close>
  "deeply rename left process without using assumptions"

method_setup cspT_ren_deep_right =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_right_tac 
                    full_simp_tac
                    CSPT_decompo
                    cspT_ren_core ctxt thms)) \<close>
  "deeply rename right process without using assumptions"

method_setup cspT_ren_deep =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_both_tac 
                    full_simp_tac
                    CSPT_decompo
                    cspT_ren_core ctxt thms)) \<close>
  "deeply rename both processes without using assumptions"


(*=================================================*
 |                                                 |
 |              Head Sequential Form               |
 |                                                 |
 *=================================================*)

(*----------------------------*
 | hsf (one step, no asm use) |
 *----------------------------*)

method_setup cspT_hsf_left =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_left_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_hsf_core ctxt thms)) \<close>
  "sequentialize left process without using assumptions"

method_setup cspT_hsf_right =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_right_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_hsf_core ctxt thms)) \<close>
  "sequentialize right process without using assumptions"

method_setup cspT_hsf =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_both_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_hsf_core ctxt thms)) \<close>
  "sequentialize both processes without using assumptions"


(*=================================================*
 |                                                 |
 |                      auto                       |
 |                                                 |
 *=================================================*)

(*-----------------------------*
 | auto (one step, no asm use) |
 *-----------------------------*)

method_setup cspT_auto_left =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_left_tac 
                    asm_full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_auto_core ctxt thms)) \<close>
  "apply all possible laws to left process with using assumptions"

method_setup cspT_auto_right =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_right_tac 
                    asm_full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_auto_core ctxt thms)) \<close>
  "apply all possible laws to right process with using assumptions"

method_setup cspT_auto =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_both_tac 
                    asm_full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_auto_core ctxt thms)) \<close>
  "apply all possible laws to both processes with using assumptions"


(*=================================================*
 |                                                 |
 |                    Unwinding                    |
 |                                                 |
 *=================================================*)

(*-------------------------------*
 | unwind (one step, no asm use) |
 *-------------------------------*)

method_setup cspT_unwind_left =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_left_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_unwind_core ctxt thms)) \<close>
  "unwind left process without using assumptions"

method_setup cspT_unwind_right =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_right_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_unwind_core ctxt thms)) \<close>
  "unwind right process without using assumptions"

method_setup cspT_unwind =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_both_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_unwind_core ctxt thms)) \<close>
  "unwind both processes without using assumptions"

(*=================================================*
 |                                                 |
 |                   Refinement                    |
 |                                                 |
 *=================================================*)

(*--------------------------*
 | refine (one step, asm)   |
 *--------------------------*)

method_setup cspT_refine_asm_left =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_refine_left_tac 
                    asm_full_simp_tac
                    cspT_simp_core ctxt thms)) \<close>
  "refine left process"

method_setup cspT_refine_asm_right =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_refine_right_tac 
                    asm_full_simp_tac
                    cspT_simp_core ctxt thms)) \<close>
  "refine right process"

(*-------------------------------*
 | refine (one step, no asm use) |
 *-------------------------------*)

method_setup cspT_refine_left =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_refine_left_tac
                    full_simp_tac
                    cspT_simp_core ctxt thms)) \<close>
  "refine left process without using assumptions"

method_setup cspT_refine_right =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_refine_right_tac 
                    full_simp_tac
                    cspT_simp_core ctxt thms)) \<close>
  "refine right process without using assumptions"

(*=================================================*
 |                                                 |
 |                   dist (aux)                    |
 |                                                 |
 *=================================================*)

(*---------------------------*
 | dist (one step, no asm)   |
 *---------------------------*)

method_setup cspT_dist_left =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_left_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_dist_core ctxt thms)) \<close>
  "distribution in left process"

method_setup cspT_dist_right =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_right_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_dist_core ctxt thms)) \<close>
  "distribution in right process"

method_setup cspT_dist =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_both_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_dist_core ctxt thms)) \<close>
  "distribution both processes"


(*=================================================*
 |                                                 |
 |                    step (aux)                   |
 |                                                 |
 *=================================================*)

(*---------------------------*
 | step (one step, no asm)   |
 *---------------------------*)

method_setup cspT_step_left =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_left_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_step_core ctxt thms)) \<close>
  "apply step-laws to left process"

method_setup cspT_step_right =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_right_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_step_core ctxt thms)) \<close>
  "apply step-laws to right process"

method_setup cspT_step =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_both_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_step_core ctxt thms)) \<close>
   "apply step-laws to both processes"

(*=================================================*
 |                                                 |
 |                 light step (aux)                |
 |                                                 |
 *=================================================*)

(*---------------------------------*
 | light step (one step, no asm)   |
 *---------------------------------*)

method_setup cspT_light_step_left =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_left_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_light_step_core ctxt thms)) \<close>
  "unfold prefix in left process"

method_setup cspT_light_step_right =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_right_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_light_step_core ctxt thms)) \<close>
  "unfold prefix in right process"

method_setup cspT_light_step =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_both_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_light_step_core ctxt thms)) \<close>
   "unfold prefix in both processes"

(*=================================================*
 |                                                 |
 |                  prefix (aux)                   |
 |                                                 |
 *=================================================*)

(*-----------------------------*
 | prefix (one step, no asm)   |
 *-----------------------------*)

method_setup cspT_prefix_left =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_left_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_prefix_core ctxt thms)) \<close>
  "fold prefix in left process"

method_setup cspT_prefix_right =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_right_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_prefix_core ctxt thms)) \<close>
  "fold prefix in right process"

method_setup cspT_prefix =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_both_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_prefix_core ctxt thms)) \<close>
  "fold prefix in both processes"

(*-----------------------------*
 | choice (one step, no asm)   |
 *-----------------------------*)

method_setup cspT_choice_left =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_left_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_choice_core ctxt thms)) \<close>
  "replace external choice by internal choice in left process"

method_setup cspT_choice_right =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_right_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_choice_core ctxt thms)) \<close>
  "replace external choice by internal choice in right process"

method_setup cspT_choice =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_both_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_choice_core ctxt thms)) \<close>
  "replace external choice by internal choice in both processes"

(*=======================================================*
 |                                                       |
 |         rewriting processes in assumptions            |
 |              (do not work well yet)                   |
 |                                                       |
 *-------------------------------------------------------*
 |                                                       |
 |          Templates (written by equations)             |
 |                                                       |
 *=======================================================*)

ML \<open>
fun templateT_leftE_tac simptac decompo f ctxt thms =
 CHANGED (
  EVERY
   [resolve_tac ctxt CSPT_rw_flag_leftE 1,
    templateT_main_tac simptac decompo f ctxt thms ])
\<close>

ML \<open>
fun templateT_rightE_tac simptac decompo f ctxt thms =
 CHANGED (
  EVERY
   [resolve_tac ctxt CSPT_rw_flag_rightE 1,
    templateT_main_tac simptac decompo f ctxt thms ])
\<close>

ML \<open>
fun templateT_bothE_tac simptac decompo f ctxt thms =
 CHANGED (
  EVERY
   [TRY (templateT_leftE_tac simptac decompo f ctxt thms),
    TRY (templateT_rightE_tac simptac decompo f ctxt thms)])
\<close>

(*
 simptac:
  full_simp_tac     (no_asm)
  asm_full_simp_tac (asm)

 decompo:
  CSPT_decompo            (any deep)
  CSPT_free_decompo_flag  (one step)
*)

(* ===================================================== *
                   Methods (instances)
 * ===================================================== *)

(*=================================================*
 |                                                 |
 |                      asm                        |
 |                                                 |
 *=================================================*)

(*------------------------*
 |  simp (one step, asm)  |
 *------------------------*)

method_setup cspT_asm_leftE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_leftE_tac 
                    asm_full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_simp_core ctxt thms)) \<close>
  "simplify leftE process with using assumption"

method_setup cspT_asm_rightE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_rightE_tac 
                    asm_full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_simp_core ctxt thms)) \<close>
  "simplify rightE process with using assumption"

method_setup cspT_asmE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_bothE_tac 
                    asm_full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_simp_core ctxt thms)) \<close>
  "simplify bothE processes with using assumption"

(*------------------------*
 |    simp (deep, asm)    |
 *------------------------*)

method_setup cspT_asm_deep_leftE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_leftE_tac 
                    asm_full_simp_tac
                    CSPT_decompo
                    cspT_simp_core ctxt thms)) \<close>
  "deeply simplify leftE process with using assumption"

method_setup cspT_asm_deep_rightE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_rightE_tac 
                    asm_full_simp_tac
                    CSPT_decompo
                    cspT_simp_core ctxt thms)) \<close>
  "deeply simplify rightE process with using assumption"

method_setup cspT_asm_deepE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_bothE_tac 
                    asm_full_simp_tac
                    CSPT_decompo
                    cspT_simp_core ctxt thms)) \<close>
  "deeply simplify bothE processes with using assumption"

(*=================================================*
 |                                                 |
 |                     simp                        |
 |                                                 |
 *=================================================*)

(*---------------------------------*
 |   simp (one step, no asm use)   |
 *---------------------------------*)

method_setup cspT_simp_leftE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_leftE_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_simp_core ctxt thms)) \<close>
  "simplify leftE process without using assumptions"

method_setup cspT_simp_rightE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_rightE_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_simp_core ctxt thms)) \<close>
  "simplify rightE process without using assumptions"

method_setup cspT_simpE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_bothE_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_simp_core ctxt thms)) \<close>
  "simplify bothE processes without using assumptions"

(*-----------------------------*
 |   simp (deep, no asm use)   |
 *-----------------------------*)

method_setup cspT_simp_deep_leftE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_leftE_tac 
                    full_simp_tac
                    CSPT_decompo
                    cspT_simp_core ctxt thms)) \<close>
  "deeply simplify leftE process without using assumptions"

method_setup cspT_simp_deep_rightE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_rightE_tac 
                    full_simp_tac
                    CSPT_decompo
                    cspT_simp_core ctxt thms)) \<close>
  "deeply simplify rightE process without using assumptions"

method_setup cspT_simp_deepE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_bothE_tac 
                    full_simp_tac
                    CSPT_decompo
                    cspT_simp_core ctxt thms)) \<close>
  "deeply simplify bothE processes without using assumptions"

(*=================================================*
 |                                                 |
 |                    renaming                     |
 |                                                 |
 *=================================================*)

(*---------------------------------*
 | renaming (one step, no asm use) |
 *---------------------------------*)

method_setup cspT_ren_leftE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_leftE_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_ren_core ctxt thms)) \<close>
  "rename leftE process without using assumptions"

method_setup cspT_ren_rightE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_rightE_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_ren_core ctxt thms)) \<close>
  "rename rightE process without using assumptions"

method_setup cspT_renE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_bothE_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_ren_core ctxt thms)) \<close>
  "rename bothE processes without using assumptions"

(*---------------------------------*
 |   renaming (deep, no asm use)   |
 *---------------------------------*)

method_setup cspT_ren_deep_leftE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_leftE_tac 
                    full_simp_tac
                    CSPT_decompo
                    cspT_ren_core ctxt thms)) \<close>
  "deeply rename leftE process without using assumptions"

method_setup cspT_ren_deep_rightE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_rightE_tac 
                    full_simp_tac
                    CSPT_decompo
                    cspT_ren_core ctxt thms)) \<close>
  "deeply rename rightE process without using assumptions"

method_setup cspT_ren_deepE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_bothE_tac 
                    full_simp_tac
                    CSPT_decompo
                    cspT_ren_core ctxt thms)) \<close>
  "deeply rename bothE processes without using assumptions"


(*=================================================*
 |                                                 |
 |              Head Sequential Form               |
 |                                                 |
 *=================================================*)

(*----------------------------*
 | hsf (one step, no asm use) |
 *----------------------------*)

method_setup cspT_hsf_leftE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_leftE_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_hsf_core ctxt thms)) \<close>
  "sequentialize leftE process without using assumptions"


method_setup cspT_hsf_rightE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_rightE_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_hsf_core ctxt thms)) \<close>
  "sequentialize rightE process without using assumptions"

method_setup cspT_hsfE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_bothE_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_hsf_core ctxt thms)) \<close>
  "sequentialize bothE processes without using assumptions"

(*=================================================*
 |                                                 |
 |                       auto                      |
 |                                                 |
 *=================================================*)

(*---------------------------*
 | auto (one step, asm use)  |
 *---------------------------*)

method_setup cspT_auto_leftE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_leftE_tac 
                    asm_full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_auto_core ctxt thms)) \<close>
  "apply all possible laws to leftE process with using assumption"

method_setup cspT_auto_rightE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_rightE_tac 
                    asm_full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_auto_core ctxt thms)) \<close>
  "apply all possible laws to rightE process with using assumption"

method_setup cspT_autoE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_bothE_tac 
                    asm_full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_auto_core ctxt thms)) \<close>
  "apply all possible laws to bothE processes with using assumption"

(*=================================================*
 |                                                 |
 |                    Unwinding                    |
 |                                                 |
 *=================================================*)

(*-------------------------------*
 | unwind (one step, no asm use) |
 *-------------------------------*)

method_setup cspT_unwind_leftE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_leftE_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_unwind_core ctxt thms)) \<close>
  "unwind leftE process without using assumptions"

method_setup cspT_unwind_rightE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_rightE_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_unwind_core ctxt thms)) \<close>
  "unwind rightE process without using assumptions"

method_setup cspT_unwindE =
  \<open> Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateT_bothE_tac 
                    full_simp_tac
                    CSPT_free_decompo_flag
                    cspT_unwind_core ctxt thms)) \<close>
  "unwind bothE processes without using assumptions"


(* test *)

(*
consts
  NewProc :: "('p,'a) proc"

defs
  NewProc_def : "NewProc == STOP"

lemma NewProc_STOP: "NewProc =T STOP"
by (simp add: NewProc_def)

lemma "(IF True THEN NewProc ELSE SKIP) =T P"
apply (cspT_simp)+
apply (cspT_simp NewProc_STOP)
oops

lemma "a -> (IF True THEN NewProc ELSE SKIP) =T P"
apply (cspT_simp_deep)+
apply (cspT_simp_deep NewProc_STOP)
oops

lemma "a -> (IF True THEN NewProc ELSE (SKIP::('p,'a) proc)) 
    =T a -> (STOP::('p,'a) proc)"
by (cspT_simp_deep NewProc_STOP)+

lemma "((0::nat) -> 0 -> STOP)[[0<-->(Suc 0)]] =T P"
apply (cspT_ren)+
apply (cspT_ren_deep)+
oops
*)


end
