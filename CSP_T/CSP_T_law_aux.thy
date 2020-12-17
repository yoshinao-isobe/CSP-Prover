           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                  April 2006               |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_law_aux
imports CSP_T_law
begin

(*---------------------------------------------------------------*
 |                                                               |
 |           convenient laws, especially for tactics             |
 |                                                               |
 *---------------------------------------------------------------*)

(*****************************************************************
                            Internal                 
 *****************************************************************)

(*------------------*
 |     singleton    |
 *------------------*)

(*** ! :{a} ***)

lemma cspT_Rep_int_choice_sum1_singleton:
  "!! : type1 {c} .. Pf =T[M,M] Pf (type1 c)"
by (rule cspT_Rep_int_choice_const, auto)

lemma cspT_Rep_int_choice_sum2_singleton:
  "!! : type2 {c} .. Pf =T[M,M] Pf (type2 c)"
by (rule cspT_Rep_int_choice_const, auto)

lemma cspT_Rep_int_choice_nat_singleton:
  "!nat :{n} .. Pf =T[M,M] Pf n"
by (rule cspT_Rep_int_choice_const, auto)

lemma cspT_Rep_int_choice_set_singleton:
  "!set :{X} .. Pf =T[M,M] Pf X"
by (rule cspT_Rep_int_choice_const, auto)

lemma cspT_Rep_int_choice_com_singleton:
  "! :{a} .. Pf =T[M,M] Pf a"
by (rule cspT_Rep_int_choice_const, auto)

lemma cspT_Rep_int_choice_f_singleton:
  "inj f ==> !<f> :{x} .. Pf =T[M,M] Pf x"
by (rule cspT_Rep_int_choice_const, auto)

lemmas cspT_Rep_int_choice_singleton =
       cspT_Rep_int_choice_sum1_singleton
       cspT_Rep_int_choice_sum2_singleton
       cspT_Rep_int_choice_nat_singleton
       cspT_Rep_int_choice_set_singleton
       cspT_Rep_int_choice_com_singleton
       cspT_Rep_int_choice_f_singleton

lemma cspT_Rep_int_choice_const_sum_rule:
  "!! c:C .. P =T[M,M] IF (sumset C={}) THEN DIV ELSE P"
apply (case_tac "sumset C={}")
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (rule cspT_Rep_int_choice_empty)
apply (simp)
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (rule cspT_Rep_int_choice_const)
apply (simp_all)
done

lemma cspT_Rep_int_choice_const_nat_rule:
  "!nat n:N .. P =T[M,M] IF (N={}) THEN DIV ELSE P"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Rep_int_choice_const_sum_rule)
by (simp)

lemma cspT_Rep_int_choice_const_set_rule:
  "!set X:Xs .. P =T[M,M] IF (Xs={}) THEN DIV ELSE P"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Rep_int_choice_const_sum_rule)
by (simp)

lemma cspT_Rep_int_choice_const_com_rule:
  "! x:X .. P =T[M,M] IF (X={}) THEN DIV ELSE P"
apply (simp add: Rep_int_choice_com_def)
apply (rule cspT_rw_left)
apply (rule cspT_Rep_int_choice_const_set_rule)
by (simp)

lemma cspT_Rep_int_choice_const_f_rule:
  "!<f> x:X .. P =T[M,M] IF (X={}) THEN DIV ELSE P"
apply (simp add: Rep_int_choice_f_def)
apply (rule cspT_rw_left)
apply (rule cspT_Rep_int_choice_const_com_rule)
by (simp)

lemmas cspT_Rep_int_choice_const_rule =
       cspT_Rep_int_choice_const_sum_rule
       cspT_Rep_int_choice_const_nat_rule
       cspT_Rep_int_choice_const_set_rule
       cspT_Rep_int_choice_const_com_rule
       cspT_Rep_int_choice_const_f_rule

lemmas cspT_Int_choice_rule = cspT_Rep_int_choice_empty
                              cspT_Rep_int_choice_singleton 
                              cspT_Int_choice_idem
                              cspT_Rep_int_choice_const_rule

(*****************************************************************
                          External
 *****************************************************************)

(* to make produced process be concrete *)

lemma cspT_Ext_pre_choice_empty_DIV:
   "? :{} -> Pf =T[M1,M2] ? a:{} -> DIV"
apply (rule cspT_rw_left)
apply (rule cspT_STOP_step[THEN cspT_sym])
apply (rule cspT_STOP_step)
done

lemma cspT_Ext_choice_unit_l_hsf: 
  "? :{} -> Qf [+] P =T[M,M] P"
apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (rule cspT_step[THEN cspT_sym])
apply (rule cspT_reflex)
apply (simp add: cspT_unit)
done

lemma cspT_Ext_choice_unit_r_hsf: 
  "P [+] ? :{} -> Qf =T[M,M] P"
apply (rule cspT_rw_left)
apply (rule cspT_commut)
apply (simp add: cspT_Ext_choice_unit_l_hsf)
done

lemmas cspT_Ext_choice_rule = cspT_Ext_pre_choice_empty_DIV
                              cspT_Ext_choice_unit_l
                              cspT_Ext_choice_unit_l_hsf
                              cspT_Ext_choice_unit_r
                              cspT_Ext_choice_unit_r_hsf
                              cspT_Ext_choice_idem

(*-----------------------------*
 |      simp rule for cspT     |
 *-----------------------------*)

lemmas cspT_choice_rule  = cspT_Int_choice_rule cspT_Ext_choice_rule

(*****************************************************************
                          Timeout
 *****************************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

(*** <= Timeout ***)

lemma cspT_Timeout_right:
  "[| P <=T[M1,M2] Q1 ; P <=T[M1,M2] Q2 |] ==> P <=T[M1,M2] Q1 [> Q2"
apply (rule cspT_rw_right)
apply (rule cspT_dist)
apply (rule cspT_Int_choice_right)
apply (rule cspT_Ext_choice_right, simp_all)
apply (rule cspT_rw_right)
apply (rule cspT_Ext_choice_unit_l, simp_all)
done

(*** STOP [> P  =  P ***)

lemma cspT_STOP_Timeout:
  "STOP [> P =T[M,M] P"
apply (rule cspT_rw_left)
apply (rule cspT_dist)
apply (rule cspT_rw_left)
apply (rule cspT_Int_choice_idem)
apply (rule cspT_unit)
done

(*================================================*
 |                                                |
 |               auxiliary step laws              |
 |                                                |
 *================================================*)

(* split + resolve *)

lemma cspT_Parallel_Timeout_split_resolve_SKIP_or_DIV:
  "[| P = SKIP | P = DIV ; Q = SKIP | Q = DIV |] ==>
    ((? :Y -> Pf) [+] P) |[X]| ((? :Z -> Qf) [+] Q) =T[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [+] Q))
                                        |~| (((? x:Y -> Pf x) [+] P) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [+] Q))
               ELSE (((? x:Y -> Pf x) [+] P) |[X]| Qf x))
     [> (((P |[X]| ((? :Z -> Qf) [+] Q)) |~|
         (((? :Y -> Pf) [+] P) |[X]| Q)))"
apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_Ext_choice_SKIP_or_DIV_resolve)
apply (simp)
apply (rule cspT_Ext_choice_SKIP_or_DIV_resolve)
apply (simp)

apply (rule cspT_rw_left)
apply (rule cspT_Parallel_Timeout_split)
apply (rule cspT_decompo)
apply (rule cspT_decompo)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_decompo)
apply (simp)
apply (simp)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_decompo)
apply (rule cspT_decompo)
apply (simp)
apply (simp)
apply (rule cspT_Ext_choice_SKIP_or_DIV_resolve[THEN cspT_sym])
apply (simp)

apply (rule cspT_decompo)
apply (simp)
apply (simp)
apply (rule cspT_Ext_choice_SKIP_or_DIV_resolve[THEN cspT_sym])
apply (simp)
apply (simp)

apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_decompo)
apply (simp)
apply (simp)
apply (rule cspT_Ext_choice_SKIP_or_DIV_resolve[THEN cspT_sym])
apply (simp)
apply (rule cspT_decompo)
apply (simp)
apply (simp)
apply (rule cspT_Ext_choice_SKIP_or_DIV_resolve[THEN cspT_sym])
apply (simp)
apply (simp)
apply (simp)

apply (rule cspT_decompo)
apply (rule cspT_decompo)
apply (simp)
apply (simp)
apply (rule cspT_Ext_choice_SKIP_or_DIV_resolve[THEN cspT_sym])
apply (simp)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_Ext_choice_SKIP_or_DIV_resolve[THEN cspT_sym])
apply (simp)
apply (simp)
done

lemma cspT_Parallel_Timeout_split_resolve_SKIP_SKIP:
  "((? :Y -> Pf) [+] SKIP) |[X]| ((? :Z -> Qf) [+] SKIP) =T[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [+] SKIP))
                                        |~| (((? x:Y -> Pf x) [+] SKIP) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [+] SKIP))
               ELSE (((? x:Y -> Pf x) [+] SKIP) |[X]| Qf x))
     [> (((SKIP |[X]| ((? :Z -> Qf) [+] SKIP)) |~|
         (((? :Y -> Pf) [+] SKIP) |[X]| SKIP)))"
by (simp add: cspT_Parallel_Timeout_split_resolve_SKIP_or_DIV)

lemma cspT_Parallel_Timeout_split_resolve_DIV_DIV:
  "((? :Y -> Pf) [+] DIV) |[X]| ((? :Z -> Qf) [+] DIV) =T[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [+] DIV))
                                        |~| (((? x:Y -> Pf x) [+] DIV) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [+] DIV))
               ELSE (((? x:Y -> Pf x) [+] DIV) |[X]| Qf x))
     [> (((DIV |[X]| ((? :Z -> Qf) [+] DIV)) |~|
         (((? :Y -> Pf) [+] DIV) |[X]| DIV)))"
by (simp add: cspT_Parallel_Timeout_split_resolve_SKIP_or_DIV)

lemma cspT_Parallel_Timeout_split_resolve_SKIP_DIV:
  "((? :Y -> Pf) [+] SKIP) |[X]| ((? :Z -> Qf) [+] DIV) =T[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [+] DIV))
                                        |~| (((? x:Y -> Pf x) [+] SKIP) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [+] DIV))
               ELSE (((? x:Y -> Pf x) [+] SKIP) |[X]| Qf x))
     [> (((SKIP |[X]| ((? :Z -> Qf) [+] DIV)) |~|
         (((? :Y -> Pf) [+] SKIP) |[X]| DIV)))"
by (simp add: cspT_Parallel_Timeout_split_resolve_SKIP_or_DIV)

lemma cspT_Parallel_Timeout_split_resolve_DIV_SKIP:
  "((? :Y -> Pf) [+] DIV) |[X]| ((? :Z -> Qf) [+] SKIP) =T[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [+] SKIP))
                                        |~| (((? x:Y -> Pf x) [+] DIV) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [+] SKIP))
               ELSE (((? x:Y -> Pf x) [+] DIV) |[X]| Qf x))
     [> (((DIV |[X]| ((? :Z -> Qf) [+] SKIP)) |~|
         (((? :Y -> Pf) [+] DIV) |[X]| SKIP)))"
by (simp add: cspT_Parallel_Timeout_split_resolve_SKIP_or_DIV)

lemmas cspT_Parallel_Timeout_split_resolve =
       cspT_Parallel_Timeout_split_resolve_SKIP_SKIP
       cspT_Parallel_Timeout_split_resolve_DIV_DIV
       cspT_Parallel_Timeout_split_resolve_SKIP_DIV
       cspT_Parallel_Timeout_split_resolve_DIV_SKIP

(* input + resolve *)

lemma cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV_l:
  "P = SKIP | P = DIV ==>
   ((? :Y -> Pf) [+] P) |[X]| (? :Z -> Qf) =T[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| (? x:Z -> Qf x))
                                        |~| (((? x:Y -> Pf x) [+] P) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| (? x:Z -> Qf x))
               ELSE (((? x:Y -> Pf x) [+] P) |[X]| Qf x))
     [> (((P |[X]| (? :Z -> Qf))))"
apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_Ext_choice_SKIP_or_DIV_resolve)
apply (simp)
apply (rule cspT_reflex)

apply (rule cspT_rw_left)
apply (rule cspT_Parallel_Timeout_input)
apply (rule cspT_decompo)
apply (rule cspT_decompo)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_decompo)
apply (simp)
apply (simp)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_decompo)
apply (simp)

apply (rule cspT_decompo)
apply (simp)
apply (simp)
apply (rule cspT_Ext_choice_SKIP_or_DIV_resolve[THEN cspT_sym])
apply (simp)
apply (simp)

apply (rule cspT_decompo)
apply (simp)
apply (simp)
apply (rule cspT_decompo)
apply (simp)
apply (simp)
apply (rule cspT_Ext_choice_SKIP_or_DIV_resolve[THEN cspT_sym])
apply (simp)
apply (simp)
apply (simp)

apply (simp)
done

lemma cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV_r:
  "Q = SKIP | Q = DIV ==>
   (? :Y -> Pf) |[X]| ((? :Z -> Qf) [+] Q) =T[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [+] Q))
                                        |~| ((? x:Y -> Pf x) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [+] Q))
               ELSE ((? x:Y -> Pf x) |[X]| Qf x))
     [> ((((? :Y -> Pf) |[X]| Q)))"
apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_reflex)
apply (rule cspT_Ext_choice_SKIP_or_DIV_resolve)
apply (simp)

apply (rule cspT_rw_left)
apply (rule cspT_Parallel_Timeout_input)
apply (rule cspT_decompo)
apply (rule cspT_decompo)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_decompo)
apply (simp)
apply (simp)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_decompo)
apply (rule cspT_decompo)
apply (simp)
apply (simp)
apply (rule cspT_Ext_choice_SKIP_or_DIV_resolve[THEN cspT_sym])
apply (simp)
apply (simp)

apply (rule cspT_decompo)
apply (simp)
apply (simp)
apply (rule cspT_decompo)
apply (simp)
apply (simp)
apply (rule cspT_Ext_choice_SKIP_or_DIV_resolve[THEN cspT_sym])
apply (simp)
apply (simp)
apply (simp)

apply (simp)
done

lemmas cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV =
       cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV_l
       cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV_r

lemma cspT_Parallel_Timeout_input_resolve_SKIP_l:
  "((? :Y -> Pf) [+] SKIP) |[X]| (? :Z -> Qf) =T[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| (? x:Z -> Qf x))
                                        |~| (((? x:Y -> Pf x) [+] SKIP) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| (? x:Z -> Qf x))
               ELSE (((? x:Y -> Pf x) [+] SKIP) |[X]| Qf x))
     [> (((SKIP |[X]| (? :Z -> Qf))))"
by (simp add: cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV)

lemma cspT_Parallel_Timeout_input_resolve_DIV_l:
  "((? :Y -> Pf) [+] DIV) |[X]| (? :Z -> Qf) =T[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| (? x:Z -> Qf x))
                                        |~| (((? x:Y -> Pf x) [+] DIV) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| (? x:Z -> Qf x))
               ELSE (((? x:Y -> Pf x) [+] DIV) |[X]| Qf x))
     [> (((DIV |[X]| (? :Z -> Qf))))"
by (simp add: cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV)

lemma cspT_Parallel_Timeout_input_resolve_SKIP_r:
  "(? :Y -> Pf) |[X]| ((? :Z -> Qf) [+] SKIP) =T[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [+] SKIP))
                                        |~| ((? x:Y -> Pf x) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [+] SKIP))
               ELSE ((? x:Y -> Pf x) |[X]| Qf x))
     [> ((((? :Y -> Pf) |[X]| SKIP)))"
by (simp add: cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV)

lemma cspT_Parallel_Timeout_input_resolve_DIV_r:
  "(? :Y -> Pf) |[X]| ((? :Z -> Qf) [+] DIV) =T[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [+] DIV))
                                        |~| ((? x:Y -> Pf x) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [+] DIV))
               ELSE ((? x:Y -> Pf x) |[X]| Qf x))
     [> ((((? :Y -> Pf) |[X]| DIV)))"
by (simp add: cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV)

lemmas cspT_Parallel_Timeout_input_resolve =
       cspT_Parallel_Timeout_input_resolve_SKIP_l
       cspT_Parallel_Timeout_input_resolve_SKIP_r
       cspT_Parallel_Timeout_input_resolve_DIV_l
       cspT_Parallel_Timeout_input_resolve_DIV_r

(**************** ;; + resolve ****************)

lemma cspT_SKIP_Seq_compo_step_resolve:
  "((? :X -> Pf) [+] SKIP) ;; Q =T[M,M] (? x:X -> (Pf x ;; Q)) [> Q"
apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (rule cspT_Ext_choice_SKIP_or_DIV_resolve)
apply (simp)
apply (rule cspT_reflex)
apply (rule cspT_SKIP_Seq_compo_step)
done

lemma cspT_DIV_Seq_compo_step_resolve:
  "((? :X -> Pf) [+] DIV) ;; Q =T[M,M] (? x:X -> (Pf x ;; Q)) [+] DIV"
apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (rule cspT_Ext_choice_SKIP_or_DIV_resolve)
apply (simp)
apply (rule cspT_reflex)

apply (rule cspT_rw_left)
apply (rule cspT_DIV_Seq_compo_step)
apply (rule cspT_Ext_choice_SKIP_DIV_resolve[THEN cspT_sym])
done

lemmas cspT_SKIP_DIV_Seq_compo_step_resolve =
       cspT_SKIP_Seq_compo_step_resolve
       cspT_DIV_Seq_compo_step_resolve

(****** for sequentilising processes with SKIP or DIV ******)

lemmas cspT_SKIP_DIV_resolve =
       cspT_SKIP_DIV
       cspT_Parallel_Timeout_split_resolve
       cspT_Parallel_Timeout_input_resolve
       cspT_SKIP_DIV_Seq_compo_step_resolve

lemmas cspT_SKIP_or_DIV_resolve =
       cspT_Parallel_Timeout_split_resolve_SKIP_or_DIV
       cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV


(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)


(*********************************************************
                       P |[X,Y]| Q
 *********************************************************)

lemma cspT_Alpha_Parallel_step: 
  "(? :A -> Pf) |[X,Y]| (? :B -> Qf) =T[M,M]
      ? x:((A Int (X - Y)) Un (B Int (Y - X)) Un (A Int B Int X Int Y))
         -> IF (x : X & x : Y) THEN (Pf x |[X,Y]| Qf x)
            ELSE IF (x : X) THEN (Pf x |[X,Y]| ? x:B -> Qf x)
            ELSE (? x:A -> Pf x |[X,Y]| Qf x)"
apply (simp add: Alpha_parallel_def)

apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_SKIP)
apply (rule cspT_SKIP)

apply (rule cspT_rw_left)
apply (rule cspT_step)
apply (simp)
apply (rule cspT_decompo)
apply (force)

apply (simp)
apply (elim disjE)

 apply (simp)
 apply (rule cspT_rw_left, rule cspT_IF)+
 apply (rule cspT_rw_right, rule cspT_IF)+
 apply (rule cspT_decompo)
 apply (simp)+
 apply (rule cspT_rw_right)
 apply (rule cspT_SKIP)
 apply (simp)

 apply (simp)
 apply (rule cspT_rw_left, rule cspT_IF)+
 apply (rule cspT_rw_right, rule cspT_IF)+
 apply (rule cspT_decompo)
 apply (simp)
 apply (rule cspT_rw_right)
 apply (rule cspT_SKIP)
 apply (simp)
 apply (simp)

 apply (simp)
 apply (rule cspT_rw_left, rule cspT_IF)+
 apply (rule cspT_rw_right, rule cspT_IF)+
 apply (simp)
done


(*==============================================================*
 |                                                              |
 |       Associativity and Commutativity for SKIP and DIV       |
 |                    (for sequentialising)                     |
 |                                                              |
 *==============================================================*)

lemma cspT_Ext_pre_choice_SKIP_commut:
  "SKIP [+] (? :X -> Pf) =T[M,M] (? :X -> Pf) [+] SKIP"
by (rule cspT_commut)

lemma cspT_Ext_pre_choice_DIV_commut:
  "DIV [+] (? :X -> Pf) =T[M,M] (? :X -> Pf) [+] DIV"
by (rule cspT_commut)

lemma cspT_Ext_pre_choice_SKIP_assoc:
  "((? :X -> Pf) [+] SKIP) [+] (? :Y -> Qf)
   =T[M,M] ((? :X -> Pf) [+] (? :Y -> Qf)) [+] SKIP"
apply (rule cspT_rw_left)
apply (rule cspT_assoc[THEN cspT_sym])
apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (rule cspT_reflex)
apply (rule cspT_commut)
apply (rule cspT_assoc)
done

lemma cspT_Ext_pre_choice_DIV_assoc:
  "((? :X -> Pf) [+] DIV) [+] (? :Y -> Qf)
   =T[M,M] ((? :X -> Pf) [+] (? :Y -> Qf)) [+] DIV"
apply (rule cspT_rw_left)
apply (rule cspT_assoc[THEN cspT_sym])
apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (rule cspT_reflex)
apply (rule cspT_commut)
apply (rule cspT_assoc)
done

lemma cspT_Ext_choice_idem_assoc:
  "(P [+] Q) [+] Q =T[M,M] (P [+] Q)"
apply (rule cspT_rw_left)
apply (rule cspT_assoc[THEN cspT_sym])
apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (rule cspT_reflex)
apply (rule cspT_idem)
apply (rule cspT_reflex)
done

lemma cspT_Ext_choice_SKIP_DIV_assoc:
  "(P [+] SKIP) [+] DIV =T[M,M] (P [+] SKIP)"
apply (rule cspT_rw_left)
apply (rule cspT_assoc[THEN cspT_sym])
apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (rule cspT_reflex)
apply (rule cspT_SKIP_DIV)
apply (rule cspT_reflex)
done

lemma cspT_Ext_choice_DIV_SKIP_assoc:
  "(P [+] DIV) [+] SKIP =T[M,M] (P [+] SKIP)"
apply (rule cspT_rw_left)
apply (rule cspT_assoc[THEN cspT_sym])
apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (rule cspT_reflex)
apply (rule cspT_SKIP_DIV)
apply (rule cspT_reflex)
done

lemmas cspT_SKIP_DIV_sort =
       cspT_Ext_choice_assoc
       cspT_Ext_pre_choice_SKIP_commut
       cspT_Ext_pre_choice_DIV_commut
       cspT_Ext_pre_choice_SKIP_assoc
       cspT_Ext_pre_choice_DIV_assoc
       cspT_Ext_choice_idem_assoc
       cspT_Ext_choice_SKIP_DIV_assoc
       cspT_Ext_choice_DIV_SKIP_assoc

(*==============================================================*
 |                                                              |
 |    decompostion control by the flag "Not_Decompo_Flag"       |
 |                                                              |
 *==============================================================*)

(*------------------------------------------------*
 |              trans with Flag                   |
 *------------------------------------------------*)

(*** rewrite (eq) ***)

lemma cspT_rw_flag_left_eq:
  "[| R1 =T[M1,M1] R2 ; Not_Decompo_Flag & R2 =T[M1,M3] R3 |] ==> R1 =T[M1,M3] R3"
by (simp add: eqT_def Not_Decompo_Flag_def)

lemma cspT_rw_flag_left_ref:
  "[| R1 =T[M1,M1] R2 ; Not_Decompo_Flag & R2 <=T[M1,M3] R3 |] ==> R1 <=T[M1,M3] R3"
by (simp add: refT_def eqT_def Not_Decompo_Flag_def)

lemmas cspT_rw_flag_left = cspT_rw_flag_left_eq cspT_rw_flag_left_ref

lemma cspT_rw_flag_right_eq:
  "[| R3 =T[M3,M3] R2 ; Not_Decompo_Flag & R1 =T[M1,M3] R2 |] ==> R1 =T[M1,M3] R3"
by (simp add: eqT_def Not_Decompo_Flag_def)

lemma cspT_rw_flag_right_ref:
  "[| R3 =T[M3,M3] R2 ; Not_Decompo_Flag & R1 <=T[M1,M3] R2 |] ==> R1 <=T[M1,M3] R3"
by (simp add: refT_def eqT_def Not_Decompo_Flag_def)

lemmas cspT_rw_flag_right = cspT_rw_flag_right_eq cspT_rw_flag_right_ref

(*------------------------------------------------*
 |              trans with Flag (ref)             |
 *------------------------------------------------*)

(*** rewrite (ref) ***)

lemma cspT_tr_flag_left_eq:
   "[| P1 =T[M1,M1] P2 ; Not_Decompo_Flag & P2 =T[M1,M3] P3 |] ==> P1 =T[M1,M3] P3"
by (simp add: eqT_def)

lemma cspT_tr_flag_left_ref:
   "[| P1 <=T[M1,M1] P2 ; Not_Decompo_Flag & P2 <=T[M1,M3] P3 |] ==> P1 <=T[M1,M3] P3"
by (simp add: refT_def eqT_def Not_Decompo_Flag_def)

lemmas cspT_tr_flag_left = cspT_tr_flag_left_eq cspT_tr_flag_left_ref

lemma cspT_tr_flag_right_eq:
   "[| P2 =T[M3,M3] P3 ; Not_Decompo_Flag & P1 =T[M1,M3] P2 |] ==> P1 =T[M1,M3] P3"
by (simp add: eqT_def)

lemma cspT_tr_flag_right_ref:
  "[| P2 <=T[M3,M3] P3 ; Not_Decompo_Flag & P1 <=T[M1,M3] P2 |] ==> P1 <=T[M1,M3] P3"
by (simp add: refT_def eqT_def Not_Decompo_Flag_def)

lemmas cspT_tr_flag_right = cspT_tr_flag_right_eq cspT_tr_flag_right_ref



(*------------------------------------------------*
 |           trans with Flag (erule)              |
 *------------------------------------------------*)

(*** rewrite (eq) ***)

lemma cspT_rw_flag_left_eqE:
  "[| P1 =T[M1,M3] P3 ; P1 =T[M1,M1] P2 ; 
      [| Not_Decompo_Flag & P2 =T[M1,M3] P3 |] ==> R |] ==> R"
by (simp add: eqT_def Not_Decompo_Flag_def)

lemma cspT_rw_flag_left_refE:
  "[| P1 <=T[M1,M3] P3 ; P1 =T[M1,M1] P2 ; 
      [| Not_Decompo_Flag & P2 <=T[M1,M3] P3 |] ==> R |] ==> R"
apply (simp add: Not_Decompo_Flag_def)
apply (subgoal_tac "P2 <=T[M1,M3] P3")
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_sym)
apply (simp)
apply (simp)
done

lemmas cspT_rw_flag_leftE = 
   cspT_rw_flag_left_eqE    cspT_rw_flag_left_refE

(* right *)

lemma cspT_rw_flag_right_eqE:
  "[| P1 =T[M1,M3] P3 ; P3 =T[M3,M3] P2 ;
      [| Not_Decompo_Flag & P1 =T[M1,M3] P2 |] ==> R |] ==> R"
by (simp add: eqT_def Not_Decompo_Flag_def)

lemma cspT_rw_flag_right_refE:
  "[| P1 <=T[M1,M3] P3 ; P3 =T[M3,M3] P2 ;
      [| Not_Decompo_Flag & P1 <=T[M1,M3] P2 |] ==> R |] ==> R"
apply (simp add: Not_Decompo_Flag_def)
apply (subgoal_tac "P1 <=T[M1,M3] P2")
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_sym)
apply (simp)
apply (simp)
done

lemmas cspT_rw_flag_rightE = 
   cspT_rw_flag_right_eqE    cspT_rw_flag_right_refE




(*==============================================================*
 |  decompostion of Sequential composition with a flag          |
 |  It is often useful that the second process is not expanded. |
 |                   (until CSP-Prover 4)                       |
 *==============================================================*)

(*
lemma cspT_Seq_compo_mono_flag:
  "[| P1 <=T[M1,M2] Q1 ; 
      Not_Decompo_Flag & P2 <=T[M1,M2] Q2 |]
           ==> P1 ;; P2 <=T[M1,M2] Q1 ;; Q2"
by (simp add: cspT_Seq_compo_mono)

lemma cspT_Seq_compo_cong_flag:
  "[| P1 =T[M1,M2] Q1 ; 
      Not_Decompo_Flag & P2 =T[M1,M2] Q2 |]
           ==> P1 ;; P2 =T[M1,M2] Q1 ;; Q2"
by (simp add: cspT_Seq_compo_cong)

lemmas cspT_free_mono_flag =
       cspT_Ext_choice_mono cspT_Int_choice_mono cspT_Parallel_mono
       cspT_Hiding_mono cspT_Renaming_mono cspT_Seq_compo_mono_flag
       cspT_Depth_rest_mono

lemmas cspT_free_cong_flag =
       cspT_Ext_choice_cong cspT_Int_choice_cong cspT_Parallel_cong
       cspT_Hiding_cong cspT_Renaming_cong cspT_Seq_compo_cong_flag
       cspT_Depth_rest_cong

lemmas cspT_free_decompo_flag = cspT_free_mono_flag cspT_free_cong_flag
*)

(*===============================================================*
 |  decompostion of Sequential composition with a flag           |
 |  It is often useful that the second process is not rewritten. |
 |                    (since CSP-Prover 5)                       |
 *===============================================================*)

lemma cspT_Seq_compo_mono_flag:
  "[| P1 <=T[M1,M2] Q1 ; 
      Not_Rewrite_Flag & P2 <=T[M1,M2] Q2 |]
           ==> P1 ;; P2 <=T[M1,M2] Q1 ;; Q2"
by (simp add: cspT_Seq_compo_mono)

lemma cspT_Seq_compo_cong_flag:
  "[| P1 =T[M1,M2] Q1 ; 
      Not_Rewrite_Flag & P2 =T[M1,M2] Q2 |]
           ==> P1 ;; P2 =T[M1,M2] Q1 ;; Q2"
by (simp add: cspT_Seq_compo_cong)

lemmas cspT_free_mono_flag =
       cspT_Ext_choice_mono cspT_Int_choice_mono cspT_Parallel_mono
       cspT_Hiding_mono cspT_Renaming_mono cspT_Seq_compo_mono_flag
       cspT_Depth_rest_mono
       cspT_Rep_int_choice_mono_UNIV

       cspT_Alpha_parallel_mono


lemmas cspT_free_cong_flag =
       cspT_Ext_choice_cong cspT_Int_choice_cong cspT_Parallel_cong
       cspT_Hiding_cong cspT_Renaming_cong cspT_Seq_compo_cong_flag
       cspT_Depth_rest_cong
       cspT_Rep_int_choice_cong_UNIV

       cspT_Alpha_parallel_cong

lemmas cspT_free_decompo_flag = cspT_free_mono_flag cspT_free_cong_flag

end
