           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |               February 2005  (modified)   |
            |                   June 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2008         |
            |                   June 2008  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2012         |
            |               November 2012  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |	    
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_tactic
imports CSP_F_law CSP_F_law_etc
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

lemmas cspF_all_dist = cspF_dist cspF_Dist cspF_Ext_dist

                       cspF_Seq_compo_hide_dist
                       cspF_Interleave_hide_dist
                       cspF_Seq_compo_renaming_dist
                       cspF_Interleave_renaming_dist

                       cspF_dist_Alpha_Parallel
                       cspF_Dist_Alpha_Parallel

lemmas cspF_choice_IF = cspF_choice_rule cspF_IF cspF_Interleave_unit 
lemmas cspF_pre_step  = cspF_Alpha_Parallel_step



lemmas cspF_Act_prefix_step_sym = cspF_Act_prefix_step[THEN cspF_sym]


ML {*
    val CSPF_reflex                    = @{thms cspF_reflex} ;
    val CSPF_rw_flag_left              = @{thms cspF_rw_flag_left} ;
    val CSPF_rw_flag_right             = @{thms cspF_rw_flag_right} ;

    val CSPF_tr_flag_left              = @{thms cspF_tr_flag_left} ;
    val CSPF_tr_flag_right             = @{thms cspF_tr_flag_right} ;

    val CSPF_light_step                = @{thms cspF_light_step_rw} ;
    val CSPF_SKIP_DIV_resolve          = @{thms cspF_SKIP_DIV_resolve} ;

    val CSPF_unwind                    = @{thms cspF_unwind} ;

    val CSPF_SKIP_DIV_sort             = @{thms cspF_SKIP_DIV_sort};

    val CSPF_rw_flag_leftE             = @{thms cspF_rw_flag_leftE} ;  (* E *)
    val CSPF_rw_flag_rightE            = @{thms cspF_rw_flag_rightE} ; (* E *)

    val CSPF_Act_prefix_step_sym       = @{thms cspF_Act_prefix_step_sym} ;
*}

ML {*
 val CSPF_free_decompo_flag     = @{thms cspF_free_decompo_flag} ;
 val CSPF_decompo               = @{thms cspF_decompo_ss} ;

 val CSPF_all_dist              = @{thms cspF_all_dist} ;
 val CSPF_choice_IF             = @{thms cspF_choice_IF} ;
 val CSPF_step                  = @{thms cspF_step_rw} ;

 val CSPF_choice_delay               = @{thms cspF_choice_delay} ;          (* new *)
 val CSPF_Rep_int_choice_sepa        = @{thms cspF_Rep_int_choice_sepa} ;   (* new *)
 val CSPF_Rep_int_choice_f_map       = @{thms cspF_Rep_int_choice_f_map} ;  (* new *)

 val CSPF_first_prefix_ss            = @{thms cspF_first_prefix_ss} ;
 val CSPF_prefix_Renaming_in_step    = @{thms cspF_prefix_Renaming_in_step} ;
 val CSPF_prefix_Renaming_notin_step = @{thms cspF_prefix_Renaming_notin_step} ;
 val CSPF_Renaming_fun_step          = @{thms cspF_Renaming_step} ;

(* the name is changed in Isabelle 2017
 val Split_if                        = @{thm split_if} ;
*)
 val If_split                        = @{thm if_split} ;

 val CSPF_pre_step                   = @{thms cspF_pre_step} ;             (* new *)

*}

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



ML {*
fun templateF_main_tac simptac decompo f ctxt thms =
 CHANGED (
  EVERY
   [REPEAT (
     FIRST 
      [(CHANGED (simptac                             (* <-- simptac *)
                (ctxt |> Splitter.del_split If_split) 1)),  
                (* no if_split *)

       (f ctxt thms),

       (EVERY [ resolve_tac ctxt CSPF_rw_flag_left 1 , 
                resolve_tac ctxt decompo 1 ]),            (* <-- decompo *)

       (EVERY [ TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1), 
                TRY (resolve_tac ctxt OFF_Not_Rewrite_Flag 1), 
                resolve_tac ctxt CSPF_reflex 1 ])

(*
       (resolve_tac ctxt OFF_All_Flag_True 1)

*)
      ]) ,
    (ALLGOALS (asm_full_simp_tac 
               (((ctxt addsimps OFF_All_Flag_True)
               |> Splitter.del_split If_split))))])

*}

ML {*
fun templateF_left_tac simptac decompo f ctxt thms =
 CHANGED (
  EVERY
   [resolve_tac ctxt CSPF_rw_flag_left 1,
    templateF_main_tac simptac decompo f ctxt thms ])
*}

ML {*
fun templateF_right_tac simptac decompo f ctxt thms =
 CHANGED (
  EVERY
   [resolve_tac ctxt CSPF_rw_flag_right 1,
    templateF_main_tac simptac decompo f ctxt thms ])
*}


ML {*
fun templateF_both_tac simptac decompo f ctxt thms =
 CHANGED (
  EVERY
   [TRY (templateF_left_tac simptac decompo f ctxt thms),
    TRY (templateF_right_tac simptac decompo f ctxt thms)])
*}

(*

 simptac:
  full_simp_tac     (no_asm)
  asm_full_simp_tac (asm)

 decompo:
  CSPF_decompo            (any deep)
  CSPF_free_decompo_flag  (one step)

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

ML {*
fun templateF_refine_main_tac simptac tr f ctxt thms =
 CHANGED (
  EVERY
   [REPEAT (
     FIRST 
      [(CHANGED (simptac                             (* <-- simptac *)
                (ctxt |> Splitter.del_split If_split) 1)),  
                (* no split_if *)

       (f ctxt thms),

       (EVERY [ resolve_tac ctxt tr 1 ,                         (* <-- transitivity *)
                resolve_tac ctxt CSPF_free_decompo_flag 1 ]),   (* <-- one step *)

       (EVERY [ TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1), 
                TRY (resolve_tac ctxt OFF_Not_Rewrite_Flag 1), 
                resolve_tac ctxt CSPF_reflex 1 ])
(*
       (resolve_tac ctxt OFF_All_Flag_True 1)
*)
       ]) ,
    (ALLGOALS (asm_full_simp_tac 
               (((ctxt addsimps OFF_All_Flag_True)
               |> Splitter.del_split If_split))))])
               
*}

ML {*
fun templateF_refine_left_tac simptac f ctxt thms =
 CHANGED (
  EVERY
   [resolve_tac ctxt CSPF_tr_flag_left 1,
    templateF_refine_main_tac simptac CSPF_tr_flag_left f ctxt thms ])
*}

ML {*
fun templateF_refine_right_tac simptac f ctxt thms =
 CHANGED (
  EVERY
   [resolve_tac ctxt CSPF_tr_flag_right 1,
    templateF_refine_main_tac simptac CSPF_tr_flag_right f ctxt thms ])
*}

(*

 simptac:
  full_simp_tac     (no_asm)
  asm_full_simp_tac (asm)

*)



(* ===================================================== *
                       Cores 
 * ===================================================== *)

(* ----- simp ----- *)

ML {*
fun cspF_simp_core ctxt thms =
       (EVERY [ (* TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1), *)   
                FIRST [ resolve_tac ctxt CSPF_choice_IF 1,
                        resolve_tac ctxt thms 1 ]])
*}

(* ----- renaming ----- *)

ML {*
fun cspF_ren_core ctxt thms =
       (EVERY [ (* TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1),  *)
                FIRST [ resolve_tac ctxt CSPF_choice_IF 1,
                        resolve_tac ctxt thms 1,
                        resolve_tac ctxt CSPF_all_dist 1,
                        resolve_tac ctxt CSPF_prefix_Renaming_in_step 1,
                        resolve_tac ctxt CSPF_prefix_Renaming_notin_step 1,
                        resolve_tac ctxt CSPF_Renaming_fun_step 1 ]])
*}

(* ----- hsf ----- *)

ML {*
fun cspF_hsf_core ctxt thms =

       (EVERY [ (* TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1), *)
                FIRST [ resolve_tac ctxt CSPF_choice_IF 1,
                        resolve_tac ctxt thms 1,
                        resolve_tac ctxt CSPF_all_dist 1,
                        resolve_tac ctxt CSPF_prefix_Renaming_in_step 1,
                        resolve_tac ctxt CSPF_prefix_Renaming_notin_step 1,
                        resolve_tac ctxt CSPF_Renaming_fun_step 1,
                        resolve_tac ctxt CSPF_first_prefix_ss 1,
                        resolve_tac ctxt CSPF_pre_step 1,
                        resolve_tac ctxt CSPF_SKIP_DIV_sort 1,
                        resolve_tac ctxt CSPF_SKIP_DIV_resolve 1,
                        resolve_tac ctxt CSPF_step 1
(*
                        resolve_tac ctxt CSPF_choice_delay 1,        
                        resolve_tac ctxt CSPF_Rep_int_choice_sepa 1, 
                        resolve_tac ctxt CSPF_Rep_int_choice_f_map 1,
                        resolve_tac ctxt CSPF_unwind 1 
*)
                    ]])
*}

(* ----- auto ----- *)

ML {*
fun cspF_auto_core ctxt thms =

       (EVERY [ (* TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1), *)
                FIRST [ resolve_tac ctxt CSPF_choice_IF 1,
                        resolve_tac ctxt thms 1,
                        resolve_tac ctxt CSPF_all_dist 1,
                        resolve_tac ctxt CSPF_prefix_Renaming_in_step 1,
                        resolve_tac ctxt CSPF_prefix_Renaming_notin_step 1,
                        resolve_tac ctxt CSPF_Renaming_fun_step 1,
                        resolve_tac ctxt CSPF_first_prefix_ss 1,
                        resolve_tac ctxt CSPF_pre_step 1,
                        resolve_tac ctxt CSPF_SKIP_DIV_sort 1,
                        resolve_tac ctxt CSPF_SKIP_DIV_resolve 1,
                        resolve_tac ctxt CSPF_step 1,
                        resolve_tac ctxt CSPF_choice_delay 1,        
                        resolve_tac ctxt CSPF_Rep_int_choice_sepa 1, 
                        resolve_tac ctxt CSPF_Rep_int_choice_f_map 1,
                        resolve_tac ctxt CSPF_unwind 1 ]])
*}

(* ----- unwinding ----- *)

ML {*
fun cspF_unwind_core ctxt thms =

       (EVERY [ (* TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1), *)
                FIRST [ resolve_tac ctxt CSPF_choice_IF 1,
                        resolve_tac ctxt thms 1,
                        resolve_tac ctxt CSPF_unwind 1 ]])
*}

(* ----- dist ----- *)

ML {*
fun cspF_dist_core ctxt thms =

       (EVERY [ (* TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1), *)
                FIRST [ resolve_tac ctxt CSPF_choice_IF 1,
                        resolve_tac ctxt thms 1,
                        resolve_tac ctxt CSPF_all_dist 1]])
*}

(* ----- step ----- *)

ML {*
fun cspF_step_core ctxt thms =

       (EVERY [ (* TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1), *)
                FIRST [ resolve_tac ctxt CSPF_choice_IF 1,
                        resolve_tac ctxt thms 1,
                        resolve_tac ctxt CSPF_prefix_Renaming_in_step 1,
                        resolve_tac ctxt CSPF_prefix_Renaming_notin_step 1,
                        resolve_tac ctxt CSPF_Renaming_fun_step 1,
                        resolve_tac ctxt CSPF_first_prefix_ss 1,
                        resolve_tac ctxt CSPF_pre_step 1,
                        resolve_tac ctxt CSPF_SKIP_DIV_sort 1,
                        resolve_tac ctxt CSPF_SKIP_DIV_resolve 1,
                        resolve_tac ctxt CSPF_step 1 ]])

*}

(* ----- light_step ----- *)

ML {*
fun cspF_light_step_core ctxt thms =

       (EVERY [ (* TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1), *)
                FIRST [ resolve_tac ctxt CSPF_choice_IF 1,
                        resolve_tac ctxt thms 1,
                        resolve_tac ctxt CSPF_first_prefix_ss 1,
                        resolve_tac ctxt CSPF_light_step 1 ]])

*}


(* ----- prefix ----- *)

ML {*
fun cspF_prefix_core ctxt thms =

       (EVERY [ (* TRY (resolve_tac ctxt OFF_Not_Decompo_Flag 1), *)
                FIRST [ resolve_tac ctxt CSPF_choice_IF 1,
                        resolve_tac ctxt thms 1,
                        resolve_tac ctxt CSPF_Act_prefix_step_sym 1]])
*}

(*

 simptac:
  full_simp_tac     (no_asm)
  asm_full_simp_tac (asm)

 decompo:
  CSPF_decompo            (any deep)
  CSPF_free_decompo_flag  (one step)

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
 |  asm (one step, asm)   |
 *------------------------*)

method_setup cspF_asm_left =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_left_tac 
                    asm_full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_simp_core ctxt thms)) *}
  "simplify left process with using assumption"

method_setup cspF_asm_right =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_right_tac 
                    asm_full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_simp_core ctxt thms)) *}
  "simplify right process with using assumption"

method_setup cspF_asm =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_both_tac 
                    asm_full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_simp_core ctxt thms)) *}
  "simplify both processes with using assumption"

(*------------------------*
 |    simp (deep, asm)    |
 *------------------------*)

method_setup cspF_asm_deep_left =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_left_tac 
                    asm_full_simp_tac
                    CSPF_decompo
                    cspF_simp_core ctxt thms)) *}
  "deeply simplify left process with using assumption"

method_setup cspF_asm_deep_right =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_right_tac 
                    asm_full_simp_tac
                    CSPF_decompo
                    cspF_simp_core ctxt thms)) *}
  "deeply simplify right process with using assumption"

method_setup cspF_asm_deep =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_both_tac 
                    asm_full_simp_tac
                    CSPF_decompo
                    cspF_simp_core ctxt thms)) *}
  "deeply simplify both processes with using assumption"

(*=================================================*
 |                                                 |
 |                     simp                        |
 |                                                 |
 *=================================================*)

(*---------------------------------*
 |   simp (one step, no asm use)   |
 *---------------------------------*)

method_setup cspF_simp_left =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_left_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_simp_core ctxt thms)) *}
  "simplify left process without using assumptions"

method_setup cspF_simp_right =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_right_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_simp_core ctxt thms)) *}
  "simplify right process without using assumptions"

method_setup cspF_simp =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_both_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_simp_core ctxt thms)) *}
  "simplify both processes without using assumptions"

(*-----------------------------*
 |   simp (deep, no asm use)   |
 *-----------------------------*)

method_setup cspF_simp_deep_left =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_left_tac 
                    full_simp_tac
                    CSPF_decompo
                    cspF_simp_core ctxt thms)) *}
  "deeply simplify left process without using assumptions"

method_setup cspF_simp_deep_right =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_right_tac 
                    full_simp_tac
                    CSPF_decompo
                    cspF_simp_core ctxt thms)) *}
  "deeply simplify right process without using assumptions"

method_setup cspF_simp_deep =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_both_tac 
                    full_simp_tac
                    CSPF_decompo
                    cspF_simp_core ctxt thms)) *}
  "deeply simplify both processes without using assumptions"

(*=================================================*
 |                                                 |
 |                    renaming                     |
 |                                                 |
 *=================================================*)



(*---------------------------------*
 | renaming (one step, no asm use) |
 *---------------------------------*)

method_setup cspF_ren_left =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_left_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_ren_core ctxt thms)) *}
  "rename left process without using assumptions"

method_setup cspF_ren_right =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_right_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_ren_core ctxt thms)) *}
  "rename right process without using assumptions"

method_setup cspF_ren =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_both_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_ren_core ctxt thms)) *}
  "rename both processes without using assumptions"

(*---------------------------------*
 |   renaming (deep, no asm use)   |
 *---------------------------------*)

method_setup cspF_ren_deep_left =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_left_tac 
                    full_simp_tac
                    CSPF_decompo
                    cspF_ren_core ctxt thms)) *}
  "deeply rename left process without using assumptions"

method_setup cspF_ren_deep_right =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_right_tac 
                    full_simp_tac
                    CSPF_decompo
                    cspF_ren_core ctxt thms)) *}
  "deeply rename right process without using assumptions"

method_setup cspF_ren_deep =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_both_tac 
                    full_simp_tac
                    CSPF_decompo
                    cspF_ren_core ctxt thms)) *}
  "deeply rename both processes without using assumptions"

(*=================================================*
 |                                                 |
 |              Head Sequential Form               |
 |                                                 |
 *=================================================*)

(*----------------------------*
 | hsf (one step, no asm use) |
 *----------------------------*)

method_setup cspF_hsf_left =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_left_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_hsf_core ctxt thms)) *}
  "sequentialize left process without using assumptions"

method_setup cspF_hsf_right =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_right_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_hsf_core ctxt thms)) *}
  "sequentialize right process without using assumptions"

method_setup cspF_hsf =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_both_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_hsf_core ctxt thms)) *}
  "sequentialize both processes without using assumptions"


(*=================================================*
 |                                                 |
 |                       auto                      |
 |                                                 |
 *=================================================*)

(*--------------------------*
 | auto (one step, asm use) |
 *--------------------------*)

method_setup cspF_auto_left =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_left_tac 
                    asm_full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_auto_core ctxt thms)) *}
  "apply all possible laws to left process with using assumptions"

method_setup cspF_auto_right =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_right_tac 
                    asm_full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_auto_core ctxt thms)) *}
  "apply all possible laws to right process with using assumptions"

method_setup cspF_auto =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_both_tac 
                    asm_full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_auto_core ctxt thms)) *}
  "apply all possible laws to both processes with using assumptions"


(*=================================================*
 |                                                 |
 |                    Unwinding                    |
 |                                                 |
 *=================================================*)

(*-------------------------------*
 | unwind (one step, no asm use) |
 *-------------------------------*)

method_setup cspF_unwind_left =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_left_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_unwind_core ctxt thms)) *}
  "unwind left process without using assumptions"

method_setup cspF_unwind_right =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_right_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_unwind_core ctxt thms)) *}
  "unwind right process without using assumptions"

method_setup cspF_unwind =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_both_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_unwind_core ctxt thms)) *}
  "unwind both processes without using assumptions"


(*=================================================*
 |                                                 |
 |                   Refinement                    |
 |                                                 |
 *=================================================*)

(*--------------------------*
 | refine (one step, asm)   |
 *--------------------------*)

method_setup cspF_refine_asm_left =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_refine_left_tac 
                    asm_full_simp_tac
                    cspF_simp_core ctxt thms)) *}
  "refine left process"

method_setup cspF_refine_asm_right =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_refine_right_tac 
                    asm_full_simp_tac
                    cspF_simp_core ctxt thms)) *}
  "refine right process"

(*-------------------------------*
 | refine (one step, no asm use) |
 *-------------------------------*)

method_setup cspF_refine_left =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_refine_left_tac
                    full_simp_tac
                    cspF_simp_core ctxt thms)) *}
  "refine left process without using assumptions"

method_setup cspF_refine_right =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_refine_right_tac 
                    full_simp_tac
                    cspF_simp_core ctxt thms)) *}
  "refine right process without using assumptions"



(*=================================================*
 |                                                 |
 |                   dist (aux)                    |
 |                                                 |
 *=================================================*)

(*---------------------------*
 | dist (one step, no asm)   |
 *---------------------------*)

method_setup cspF_dist_left =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_left_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_dist_core ctxt thms)) *}
  "distribution in left process"

method_setup cspF_dist_right =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_right_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_dist_core ctxt thms)) *}
  "distribution in right process"

method_setup cspF_dist =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_both_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_dist_core ctxt thms)) *}
  "distribution both processes"


(*=================================================*
 |                                                 |
 |                    step (aux)                   |
 |                                                 |
 *=================================================*)

(*---------------------------*
 | step (one step, no asm)   |
 *---------------------------*)

method_setup cspF_step_left =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_left_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_step_core ctxt thms)) *}
  "apply step-laws to left process"

method_setup cspF_step_right =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_right_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_step_core ctxt thms)) *}
  "apply step-laws to right process"

method_setup cspF_step =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_both_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_step_core ctxt thms)) *}
   "apply step-laws to both processes"

(*=================================================*
 |                                                 |
 |                 light step (aux)                |
 |                                                 |
 *=================================================*)

(*---------------------------------*
 | light step (one step, no asm)   |
 *---------------------------------*)

method_setup cspF_light_step_left =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_left_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_light_step_core ctxt thms)) *}
  "unfold prefix in left process"

method_setup cspF_light_step_right =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_right_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_light_step_core ctxt thms)) *}
  "unfold prefix in right process"

method_setup cspF_light_step =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_both_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_light_step_core ctxt thms)) *}
   "unfold prefix in both processes"

(*=================================================*
 |                                                 |
 |                  prefix (aux)                   |
 |                                                 |
 *=================================================*)

(*-----------------------------*
 | prefix (one step, no asm)   |
 *-----------------------------*)

method_setup cspF_prefix_left =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_left_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_prefix_core ctxt thms)) *}
  "fold prefix in left process"

method_setup cspF_prefix_right =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_right_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_prefix_core ctxt thms)) *}
  "fold prefix in right process"

method_setup cspF_prefix =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_both_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_prefix_core ctxt thms)) *}
  "fold prefix in both processes"

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

ML {*
fun templateF_leftE_tac simptac decompo f ctxt thms =
 CHANGED (
  EVERY
   [resolve_tac ctxt CSPF_rw_flag_leftE 1,
    templateF_main_tac simptac decompo f ctxt thms ])
*}

ML {*
fun templateF_rightE_tac simptac decompo f ctxt thms =
 CHANGED (
  EVERY
   [resolve_tac ctxt CSPF_rw_flag_rightE 1,
    templateF_main_tac simptac decompo f ctxt thms ])
*}

ML {*
fun templateF_bothE_tac simptac decompo f ctxt thms =
 CHANGED (
  EVERY
   [TRY (templateF_leftE_tac simptac decompo f ctxt thms),
    TRY (templateF_rightE_tac simptac decompo f ctxt thms)])
*}

(*
 simptac:
  full_simp_tac     (no_asm)
  asm_full_simp_tac (asm)

 decompo:
  CSPF_decompo            (any deep)
  CSPF_free_decompo_flag  (one step)
*)

(* ===================================================== *
                   Methods (instances)
 * ===================================================== *)

(*=================================================*
 |                                                 |
 |             simp with assumption                |
 |                                                 |
 *=================================================*)

(*-----------------------*
 |  asm (one step, asm)  |
 *-----------------------*)

method_setup cspF_asm_leftE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_leftE_tac 
                    asm_full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_simp_core ctxt thms)) *}
  "simplify leftE process"

method_setup cspF_asm_rightE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_rightE_tac 
                    asm_full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_simp_core ctxt thms)) *}
  "simplify rightE process"

method_setup cspF_asmE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_bothE_tac 
                    asm_full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_simp_core ctxt thms)) *}
  "simplify bothE processes"

(*------------------------*
 |    simp (deep, asm)    |
 *------------------------*)

method_setup cspF_asm_deep_leftE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_leftE_tac 
                    asm_full_simp_tac
                    CSPF_decompo
                    cspF_simp_core ctxt thms)) *}
  "deeply simplify leftE process"

method_setup cspF_asm_deep_rightE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_rightE_tac 
                    asm_full_simp_tac
                    CSPF_decompo
                    cspF_simp_core ctxt thms)) *}
  "deeply simplify rightE process"

method_setup cspF_asm_deepE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_bothE_tac 
                    asm_full_simp_tac
                    CSPF_decompo
                    cspF_simp_core ctxt thms)) *}
  "deeply simplify bothE processes"


(*=================================================*
 |                                                 |
 |                     simp                        |
 |                                                 |
 *=================================================*)

(*---------------------------------*
 |   simp (one step, no asm use)   |
 *---------------------------------*)

method_setup cspF_simp_leftE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_leftE_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_simp_core ctxt thms)) *}
  "simplify leftE process without using assumptions"

method_setup cspF_simp_rightE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_rightE_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_simp_core ctxt thms)) *}
  "simplify rightE process without using assumptions"

method_setup cspF_simpE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_bothE_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_simp_core ctxt thms)) *}
  "simplify bothE processes without using assumptions"

(*-----------------------------*
 |   simp (deep, no asm use)   |
 *-----------------------------*)

method_setup cspF_simp_deep_leftE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_leftE_tac 
                    full_simp_tac
                    CSPF_decompo
                    cspF_simp_core ctxt thms)) *}
  "deeply simplify leftE process without using assumptions"

method_setup cspF_simp_deep_rightE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_rightE_tac 
                    full_simp_tac
                    CSPF_decompo
                    cspF_simp_core ctxt thms)) *}
  "deeply simplify rightE process without using assumptions"

method_setup cspF_simp_deepE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_bothE_tac 
                    full_simp_tac
                    CSPF_decompo
                    cspF_simp_core ctxt thms)) *}
  "deeply simplify bothE processes without using assumptions"

(*=================================================*
 |                                                 |
 |                    renaming                     |
 |                                                 |
 *=================================================*)

(*---------------------------------*
 | renaming (one step, no asm use) |
 *---------------------------------*)

method_setup cspF_ren_leftE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_leftE_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_ren_core ctxt thms)) *}
  "rename leftE process without using assumptions"

method_setup cspF_ren_rightE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_rightE_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_ren_core ctxt thms)) *}
  "rename rightE process without using assumptions"

method_setup cspF_renE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_bothE_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_ren_core ctxt thms)) *}
  "rename bothE processes without using assumptions"

(*---------------------------------*
 |   renaming (deep, no asm use)   |
 *---------------------------------*)

method_setup cspF_ren_deep_leftE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_leftE_tac 
                    full_simp_tac
                    CSPF_decompo
                    cspF_ren_core ctxt thms)) *}
  "deeply rename leftE process without using assumptions"

method_setup cspF_ren_deep_rightE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_rightE_tac 
                    full_simp_tac
                    CSPF_decompo
                    cspF_ren_core ctxt thms)) *}
  "deeply rename rightE process without using assumptions"

method_setup cspF_ren_deepE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_bothE_tac 
                    full_simp_tac
                    CSPF_decompo
                    cspF_ren_core ctxt thms)) *}
  "deeply rename bothE processes without using assumptions"


(*=================================================*
 |                                                 |
 |              Head Sequential Form               |
 |                                                 |
 *=================================================*)

(*----------------------------*
 | hsf (one step, no asm use) |
 *----------------------------*)

method_setup cspF_hsf_leftE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_leftE_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_hsf_core ctxt thms)) *}
  "sequentialize leftE process without using assumptions"

method_setup cspF_hsf_rightE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_rightE_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_hsf_core ctxt thms)) *}
  "sequentialize rightE process without using assumptions"

method_setup cspF_hsfE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_bothE_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_hsf_core ctxt thms)) *}
  "sequentialize bothE processes without using assumptions"


(*=================================================*
 |                                                 |
 |                     auto                        |
 |                                                 |
 *=================================================*)

(*----------------------------*
 | auto (one step, no asm use) |
 *----------------------------*)

method_setup cspF_auto_leftE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_leftE_tac 
                    asm_full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_auto_core ctxt thms)) *}
  "apply all possible laws to left process with using assumption"


method_setup cspF_auto_rightE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_rightE_tac 
                    asm_full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_auto_core ctxt thms)) *}
  "apply all possible laws to right process with using assumption"

method_setup cspF_autoE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_bothE_tac 
                    asm_full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_auto_core ctxt thms)) *}
  "apply all possible laws to both process with using assumption"



(*=================================================*
 |                                                 |
 |                    Unwinding                    |
 |                                                 |
 *=================================================*)

(*-------------------------------*
 | unwind (one step, no asm use) |
 *-------------------------------*)

method_setup cspF_unwind_leftE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_leftE_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_unwind_core ctxt thms)) *}
  "unwind leftE process without using assumptions"

method_setup cspF_unwind_rightE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_rightE_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_unwind_core ctxt thms)) *}
  "unwind rightE process without using assumptions"

method_setup cspF_unwindE =
  {* Attrib.thms >> (fn thms => fn ctxt => 
     SIMPLE_METHOD (templateF_bothE_tac 
                    full_simp_tac
                    CSPF_free_decompo_flag
                    cspF_unwind_core ctxt thms)) *}
  "unwind bothE processes without using assumptions"





(* test *)

(*
definition
  NewProc :: "('p,'a) proc"
  where
  NewProc_def : "NewProc == STOP"

lemma NewProc_STOP: "NewProc =F STOP"
by (simp add: NewProc_def)

lemma "(IF True THEN NewProc ELSE SKIP) =F P"
apply (cspF_simp)+
apply (cspF_simp NewProc_STOP)
oops

lemma "a -> (IF True THEN NewProc ELSE SKIP) =F P"
apply (cspF_simp_deep)+
apply (cspF_simp_deep NewProc_STOP)
oops

lemma "a -> (IF True THEN NewProc ELSE (SKIP::('p,'a) proc)) 
    =F a -> (STOP::('p,'a) proc)"
by (cspF_simp_deep NewProc_STOP)+

lemma "((0::nat) -> 0 -> STOP)[[0<-->(Suc 0)]] =F P"
apply (cspF_ren)+
apply (cspF_ren_deep)+
oops

lemma "? x:{a} -> P =F Q"
apply (cspF_prefix)
oops

*)


end
