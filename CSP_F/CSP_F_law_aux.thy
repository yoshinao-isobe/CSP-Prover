           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                  April 2006               |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_law_aux
imports CSP_F_law
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

lemma cspF_Rep_int_choice_sum1_singleton:
  "!! : type1 {c} .. Pf =F[M,M] Pf (type1 c)"
by (rule cspF_Rep_int_choice_const, auto)

lemma cspF_Rep_int_choice_sum2_singleton:
  "!! : type2 {c} .. Pf =F[M,M] Pf (type2 c)"
by (rule cspF_Rep_int_choice_const, auto)

lemma cspF_Rep_int_choice_nat_singleton:
  "!nat :{n} .. Pf =F[M,M] Pf n"
by (rule cspF_Rep_int_choice_const, auto)

lemma cspF_Rep_int_choice_set_singleton:
  "!set :{X} .. Pf =F[M,M] Pf X"
by (rule cspF_Rep_int_choice_const, auto)

lemma cspF_Rep_int_choice_com_singleton:
  "! :{a} .. Pf =F[M,M] Pf a"
by (rule cspF_Rep_int_choice_const, auto)

lemma cspF_Rep_int_choice_f_singleton:
  "inj f ==> !<f> :{x} .. Pf =F[M,M] Pf x"
by (rule cspF_Rep_int_choice_const, auto)

lemmas cspF_Rep_int_choice_singleton =
       cspF_Rep_int_choice_sum1_singleton
       cspF_Rep_int_choice_sum2_singleton
       cspF_Rep_int_choice_nat_singleton
       cspF_Rep_int_choice_set_singleton
       cspF_Rep_int_choice_com_singleton
       cspF_Rep_int_choice_f_singleton

lemma cspF_Rep_int_choice_const_sum_rule:
  "!! c:C .. P =F[M,M] IF (sumset C={}) THEN DIV ELSE P"
apply (case_tac "sumset C={}")
apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (rule cspF_Rep_int_choice_empty)
apply (simp)
apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (rule cspF_Rep_int_choice_const)
apply (simp_all)
done

lemma cspF_Rep_int_choice_const_nat_rule:
  "!nat n:N .. P =F[M,M] IF (N={}) THEN DIV ELSE P"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspF_rw_left)
apply (rule cspF_Rep_int_choice_const_sum_rule)
by (simp)

lemma cspF_Rep_int_choice_const_set_rule:
  "!set X:Xs .. P =F[M,M] IF (Xs={}) THEN DIV ELSE P"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspF_rw_left)
apply (rule cspF_Rep_int_choice_const_sum_rule)
by (simp)

lemma cspF_Rep_int_choice_const_com_rule:
  "! x:X .. P =F[M,M] IF (X={}) THEN DIV ELSE P"
apply (simp add: Rep_int_choice_com_def)
apply (rule cspF_rw_left)
apply (rule cspF_Rep_int_choice_const_set_rule)
by (simp)

lemma cspF_Rep_int_choice_const_f_rule:
  "!<f> x:X .. P =F[M,M] IF (X={}) THEN DIV ELSE P"
apply (simp add: Rep_int_choice_f_def)
apply (rule cspF_rw_left)
apply (rule cspF_Rep_int_choice_const_com_rule)
by (simp)

lemmas cspF_Rep_int_choice_const_rule =
       cspF_Rep_int_choice_const_sum_rule
       cspF_Rep_int_choice_const_nat_rule
       cspF_Rep_int_choice_const_set_rule
       cspF_Rep_int_choice_const_com_rule
       cspF_Rep_int_choice_const_f_rule

lemmas cspF_Int_choice_rule = cspF_Rep_int_choice_empty
                              cspF_Rep_int_choice_singleton 
                              cspF_Int_choice_idem
                              cspF_Rep_int_choice_const_rule

(*****************************************************************
                          External
 *****************************************************************)

(* to make produced process be concrete *)

lemma cspF_Ext_pre_choice_empty_DIV:
   "? :{} -> Pf =F[M1,M2] ? a:{} -> DIV"
apply (rule cspF_rw_left)
apply (rule cspF_STOP_step[THEN cspF_sym])
apply (rule cspF_STOP_step)
done

lemma cspF_Ext_choice_unit_l_hsf: 
  "? :{} -> Qf [+] P =F[M,M] P"
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_step[THEN cspF_sym])
apply (rule cspF_reflex)
apply (simp add: cspF_unit)
done

lemma cspF_Ext_choice_unit_r_hsf: 
  "P [+] ? :{} -> Qf =F[M,M] P"
apply (rule cspF_rw_left)
apply (rule cspF_commut)
apply (simp add: cspF_Ext_choice_unit_l_hsf)
done

lemmas cspF_Ext_choice_rule = cspF_Ext_pre_choice_empty_DIV
                              cspF_Ext_choice_unit_l
                              cspF_Ext_choice_unit_l_hsf
                              cspF_Ext_choice_unit_r
                              cspF_Ext_choice_unit_r_hsf
                              cspF_Ext_choice_idem

(*-----------------------------*
 |      simp rule for cspF     |
 *-----------------------------*)

lemmas cspF_choice_rule  = cspF_Int_choice_rule cspF_Ext_choice_rule

(*****************************************************************
                          Timeout
 *****************************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

(*** <= Timeout ***)

lemma cspF_Timeout_right:
  "[| P <=F[M1,M2] Q1 ; P <=F[M1,M2] Q2 |] ==> P <=F[M1,M2] Q1 [> Q2"
apply (rule cspF_rw_right)
apply (rule cspF_dist)
apply (rule cspF_Int_choice_right)
apply (rule cspF_Ext_choice_right, simp_all)
apply (rule cspF_rw_right)
apply (rule cspF_Ext_choice_unit_l, simp_all)
done

(*** STOP [> P  =  P ***)

lemma cspF_STOP_Timeout:
  "STOP [> P =F[M,M] P"
apply (rule cspF_rw_left)
apply (rule cspF_dist)
apply (rule cspF_rw_left)
apply (rule cspF_Int_choice_idem)
apply (rule cspF_unit)
done

(*================================================*
 |                                                |
 |               auxiliary step laws              |
 |                                                |
 *================================================*)

(* split + resolve *)

lemma cspF_Parallel_Timeout_split_resolve_SKIP_or_DIV:
  "[| P = SKIP | P = DIV ; Q = SKIP | Q = DIV |] ==>
    ((? :Y -> Pf) [+] P) |[X]| ((? :Z -> Qf) [+] Q) =F[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [+] Q))
                                        |~| (((? x:Y -> Pf x) [+] P) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [+] Q))
               ELSE (((? x:Y -> Pf x) [+] P) |[X]| Qf x))
     [> (((P |[X]| ((? :Z -> Qf) [+] Q)) |~|
         (((? :Y -> Pf) [+] P) |[X]| Q)))"
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_Ext_choice_SKIP_or_DIV_resolve)
apply (simp)
apply (rule cspF_Ext_choice_SKIP_or_DIV_resolve)
apply (simp)

apply (rule cspF_rw_left)
apply (rule cspF_Parallel_Timeout_split)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_decompo)
apply (simp)
apply (simp)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (simp)
apply (simp)
apply (rule cspF_Ext_choice_SKIP_or_DIV_resolve[THEN cspF_sym])
apply (simp)

apply (rule cspF_decompo)
apply (simp)
apply (simp)
apply (rule cspF_Ext_choice_SKIP_or_DIV_resolve[THEN cspF_sym])
apply (simp)
apply (simp)

apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_decompo)
apply (simp)
apply (simp)
apply (rule cspF_Ext_choice_SKIP_or_DIV_resolve[THEN cspF_sym])
apply (simp)
apply (rule cspF_decompo)
apply (simp)
apply (simp)
apply (rule cspF_Ext_choice_SKIP_or_DIV_resolve[THEN cspF_sym])
apply (simp)
apply (simp)
apply (simp)

apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (simp)
apply (simp)
apply (rule cspF_Ext_choice_SKIP_or_DIV_resolve[THEN cspF_sym])
apply (simp)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_Ext_choice_SKIP_or_DIV_resolve[THEN cspF_sym])
apply (simp)
apply (simp)
done

lemma cspF_Parallel_Timeout_split_resolve_SKIP_SKIP:
  "((? :Y -> Pf) [+] SKIP) |[X]| ((? :Z -> Qf) [+] SKIP) =F[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [+] SKIP))
                                        |~| (((? x:Y -> Pf x) [+] SKIP) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [+] SKIP))
               ELSE (((? x:Y -> Pf x) [+] SKIP) |[X]| Qf x))
     [> (((SKIP |[X]| ((? :Z -> Qf) [+] SKIP)) |~|
         (((? :Y -> Pf) [+] SKIP) |[X]| SKIP)))"
by (simp add: cspF_Parallel_Timeout_split_resolve_SKIP_or_DIV)

lemma cspF_Parallel_Timeout_split_resolve_DIV_DIV:
  "((? :Y -> Pf) [+] DIV) |[X]| ((? :Z -> Qf) [+] DIV) =F[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [+] DIV))
                                        |~| (((? x:Y -> Pf x) [+] DIV) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [+] DIV))
               ELSE (((? x:Y -> Pf x) [+] DIV) |[X]| Qf x))
     [> (((DIV |[X]| ((? :Z -> Qf) [+] DIV)) |~|
         (((? :Y -> Pf) [+] DIV) |[X]| DIV)))"
by (simp add: cspF_Parallel_Timeout_split_resolve_SKIP_or_DIV)

lemma cspF_Parallel_Timeout_split_resolve_SKIP_DIV:
  "((? :Y -> Pf) [+] SKIP) |[X]| ((? :Z -> Qf) [+] DIV) =F[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [+] DIV))
                                        |~| (((? x:Y -> Pf x) [+] SKIP) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [+] DIV))
               ELSE (((? x:Y -> Pf x) [+] SKIP) |[X]| Qf x))
     [> (((SKIP |[X]| ((? :Z -> Qf) [+] DIV)) |~|
         (((? :Y -> Pf) [+] SKIP) |[X]| DIV)))"
by (simp add: cspF_Parallel_Timeout_split_resolve_SKIP_or_DIV)

lemma cspF_Parallel_Timeout_split_resolve_DIV_SKIP:
  "((? :Y -> Pf) [+] DIV) |[X]| ((? :Z -> Qf) [+] SKIP) =F[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [+] SKIP))
                                        |~| (((? x:Y -> Pf x) [+] DIV) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [+] SKIP))
               ELSE (((? x:Y -> Pf x) [+] DIV) |[X]| Qf x))
     [> (((DIV |[X]| ((? :Z -> Qf) [+] SKIP)) |~|
         (((? :Y -> Pf) [+] DIV) |[X]| SKIP)))"
by (simp add: cspF_Parallel_Timeout_split_resolve_SKIP_or_DIV)

lemmas cspF_Parallel_Timeout_split_resolve =
       cspF_Parallel_Timeout_split_resolve_SKIP_SKIP
       cspF_Parallel_Timeout_split_resolve_DIV_DIV
       cspF_Parallel_Timeout_split_resolve_SKIP_DIV
       cspF_Parallel_Timeout_split_resolve_DIV_SKIP

(* input + resolve *)

lemma cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV_l:
  "P = SKIP | P = DIV ==>
   ((? :Y -> Pf) [+] P) |[X]| (? :Z -> Qf) =F[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| (? x:Z -> Qf x))
                                        |~| (((? x:Y -> Pf x) [+] P) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| (? x:Z -> Qf x))
               ELSE (((? x:Y -> Pf x) [+] P) |[X]| Qf x))
     [> (((P |[X]| (? :Z -> Qf))))"
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_Ext_choice_SKIP_or_DIV_resolve)
apply (simp)
apply (rule cspF_reflex)

apply (rule cspF_rw_left)
apply (rule cspF_Parallel_Timeout_input)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_decompo)
apply (simp)
apply (simp)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_decompo)
apply (simp)

apply (rule cspF_decompo)
apply (simp)
apply (simp)
apply (rule cspF_Ext_choice_SKIP_or_DIV_resolve[THEN cspF_sym])
apply (simp)
apply (simp)

apply (rule cspF_decompo)
apply (simp)
apply (simp)
apply (rule cspF_decompo)
apply (simp)
apply (simp)
apply (rule cspF_Ext_choice_SKIP_or_DIV_resolve[THEN cspF_sym])
apply (simp)
apply (simp)
apply (simp)

apply (simp)
done

lemma cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV_r:
  "Q = SKIP | Q = DIV ==>
   (? :Y -> Pf) |[X]| ((? :Z -> Qf) [+] Q) =F[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [+] Q))
                                        |~| ((? x:Y -> Pf x) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [+] Q))
               ELSE ((? x:Y -> Pf x) |[X]| Qf x))
     [> ((((? :Y -> Pf) |[X]| Q)))"
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_reflex)
apply (rule cspF_Ext_choice_SKIP_or_DIV_resolve)
apply (simp)

apply (rule cspF_rw_left)
apply (rule cspF_Parallel_Timeout_input)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_decompo)
apply (simp)
apply (simp)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (simp)
apply (simp)
apply (rule cspF_Ext_choice_SKIP_or_DIV_resolve[THEN cspF_sym])
apply (simp)
apply (simp)

apply (rule cspF_decompo)
apply (simp)
apply (simp)
apply (rule cspF_decompo)
apply (simp)
apply (simp)
apply (rule cspF_Ext_choice_SKIP_or_DIV_resolve[THEN cspF_sym])
apply (simp)
apply (simp)
apply (simp)

apply (simp)
done

lemmas cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV =
       cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV_l
       cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV_r

lemma cspF_Parallel_Timeout_input_resolve_SKIP_l:
  "((? :Y -> Pf) [+] SKIP) |[X]| (? :Z -> Qf) =F[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| (? x:Z -> Qf x))
                                        |~| (((? x:Y -> Pf x) [+] SKIP) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| (? x:Z -> Qf x))
               ELSE (((? x:Y -> Pf x) [+] SKIP) |[X]| Qf x))
     [> (((SKIP |[X]| (? :Z -> Qf))))"
by (simp add: cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV)

lemma cspF_Parallel_Timeout_input_resolve_DIV_l:
  "((? :Y -> Pf) [+] DIV) |[X]| (? :Z -> Qf) =F[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| (? x:Z -> Qf x))
                                        |~| (((? x:Y -> Pf x) [+] DIV) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| (? x:Z -> Qf x))
               ELSE (((? x:Y -> Pf x) [+] DIV) |[X]| Qf x))
     [> (((DIV |[X]| (? :Z -> Qf))))"
by (simp add: cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV)

lemma cspF_Parallel_Timeout_input_resolve_SKIP_r:
  "(? :Y -> Pf) |[X]| ((? :Z -> Qf) [+] SKIP) =F[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [+] SKIP))
                                        |~| ((? x:Y -> Pf x) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [+] SKIP))
               ELSE ((? x:Y -> Pf x) |[X]| Qf x))
     [> ((((? :Y -> Pf) |[X]| SKIP)))"
by (simp add: cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV)

lemma cspF_Parallel_Timeout_input_resolve_DIV_r:
  "(? :Y -> Pf) |[X]| ((? :Z -> Qf) [+] DIV) =F[M,M]
     (? x:((X Int Y Int Z) Un (Y - X) Un (Z - X))
         -> IF (x : X) THEN (Pf x |[X]| Qf x)
               ELSE IF (x : Y & x : Z) THEN ((Pf x |[X]| ((? x:Z -> Qf x) [+] DIV))
                                        |~| ((? x:Y -> Pf x) |[X]| Qf x))
               ELSE IF (x : Y) THEN (Pf x |[X]| ((? x:Z -> Qf x) [+] DIV))
               ELSE ((? x:Y -> Pf x) |[X]| Qf x))
     [> ((((? :Y -> Pf) |[X]| DIV)))"
by (simp add: cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV)

lemmas cspF_Parallel_Timeout_input_resolve =
       cspF_Parallel_Timeout_input_resolve_SKIP_l
       cspF_Parallel_Timeout_input_resolve_SKIP_r
       cspF_Parallel_Timeout_input_resolve_DIV_l
       cspF_Parallel_Timeout_input_resolve_DIV_r

(**************** ;; + resolve ****************)

lemma cspF_SKIP_Seq_compo_step_resolve:
  "((? :X -> Pf) [+] SKIP) ;; Q =F[M,M] (? x:X -> (Pf x ;; Q)) [> Q"
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_Ext_choice_SKIP_or_DIV_resolve)
apply (simp)
apply (rule cspF_reflex)
apply (rule cspF_SKIP_Seq_compo_step)
done

lemma cspF_DIV_Seq_compo_step_resolve:
  "((? :X -> Pf) [+] DIV) ;; Q =F[M,M] (? x:X -> (Pf x ;; Q)) [+] DIV"
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_Ext_choice_SKIP_or_DIV_resolve)
apply (simp)
apply (rule cspF_reflex)

apply (rule cspF_rw_left)
apply (rule cspF_DIV_Seq_compo_step)
apply (rule cspF_Ext_choice_SKIP_DIV_resolve[THEN cspF_sym])
done

lemmas cspF_SKIP_DIV_Seq_compo_step_resolve =
       cspF_SKIP_Seq_compo_step_resolve
       cspF_DIV_Seq_compo_step_resolve

(****** for sequentilising processes with SKIP or DIV ******)

lemmas cspF_SKIP_DIV_resolve =
       cspF_SKIP_DIV
       cspF_Parallel_Timeout_split_resolve
       cspF_Parallel_Timeout_input_resolve
       cspF_SKIP_DIV_Seq_compo_step_resolve

lemmas cspF_SKIP_or_DIV_resolve =
       cspF_Parallel_Timeout_split_resolve_SKIP_or_DIV
       cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV

(*=========================================================*
 |                                                         |
 |   for convenience, especially for fully sequntialising  |
 |                                                         |
 *=========================================================*)

lemma cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_DIV_l:
  "Q = SKIP | Q = DIV | Q = STOP ==>
   (P [+] Q) |[X]| DIV =F[M,M] (P |[X]| DIV)"
apply (erule disjE)
apply (simp)
apply (rule cspF_SKIP_DIV)
apply (erule disjE)
apply (simp)
apply (rule cspF_SKIP_DIV)
apply (simp)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp_all)
apply (rule cspF_unit)
apply (rule cspF_reflex)
apply (rule cspF_reflex)
done

lemma cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_DIV_r:
  "Q = SKIP | Q = DIV | Q = STOP ==>
   DIV |[X]| (P [+] Q) =F[M,M] (DIV |[X]| P)"
apply (rule cspF_rw_left)
apply (rule cspF_commut)
apply (rule cspF_rw_right)
apply (rule cspF_commut)
apply (simp add: cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_DIV_l)
done

lemmas cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_DIV =
       cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_DIV_l
       cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_DIV_r

lemma cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP_l:
  "Q = SKIP | Q = DIV | Q = STOP ==>
   ((? :Y -> Pf) [+] Q) |[X]| SKIP =F[M,M] 
   (? x:(Y - X) -> (Pf x |[X]| SKIP)) [+] Q"
apply (erule disjE)
apply (simp)
apply (rule cspF_SKIP_DIV)
apply (erule disjE)
apply (simp)
apply (rule cspF_SKIP_DIV)

apply (simp)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp_all)
apply (rule cspF_unit)
apply (rule cspF_reflex)

apply (rule cspF_rw_right)
apply (rule cspF_unit)
apply (rule cspF_SKIP_DIV)
done

lemma cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP_r:
  "Q = SKIP | Q = DIV | Q = STOP ==>
   SKIP |[X]| ((? :Y -> Pf) [+] Q) =F[M,M] 
   (? x:(Y - X) -> (SKIP |[X]| Pf x)) [+] Q"
apply (rule cspF_rw_left)
apply (rule cspF_commut)
apply (rule cspF_rw_right)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_commut)
apply (rule cspF_reflex)
apply (simp add: cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP_l)
done

lemmas cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP =
       cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP_l
       cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP_r

lemmas cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice =
       cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_DIV
       cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP

(* renaming *)

lemma cspF_SKIP_or_DIV_or_STOP_Renaming_Id: 
   "P = SKIP | P = DIV | P = STOP ==> P [[r]] =F[M,M] P"
apply (erule disjE)
apply (simp add: cspF_SKIP_DIV)
apply (erule disjE)
apply (simp add: cspF_SKIP_DIV)

apply (simp)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_step)

apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_Ext_pre_choice_empty_DIV)

apply (rule cspF_rw_left)
apply (rule cspF_step)

apply (rule cspF_rw_right)
apply (rule cspF_step)

apply (rule cspF_decompo)
apply (auto)
done

(* restg *)

lemma cspF_STOP_Depth_rest:
   "STOP |. Suc n =F[M,M] STOP"
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_step)
apply (rule cspF_rw_left)
apply (rule cspF_step)
apply (rule cspF_rw_right)
apply (rule cspF_step)

apply (rule cspF_decompo)
apply (auto)
done

(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)

(*********************************************************
                       P |[X,Y]| Q (aux)
 *********************************************************)

lemma cspF_Alpha_Parallel_step: 
  "(? :A -> Pf) |[X,Y]| (? :B -> Qf) =F[M,M]
      ? x:((A Int (X - Y)) Un (B Int (Y - X)) Un (A Int B Int X Int Y))
         -> IF (x : X & x : Y) THEN (Pf x |[X,Y]| Qf x)
            ELSE IF (x : X) THEN (Pf x |[X,Y]| ? x:B -> Qf x)
            ELSE (? x:A -> Pf x |[X,Y]| Qf x)"
apply (simp add: Alpha_parallel_def)

apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_SKIP)
apply (rule cspF_SKIP)

apply (rule cspF_rw_left)
apply (rule cspF_step)
apply (simp)
apply (rule cspF_decompo)
apply (force)

apply (simp)
apply (elim disjE)

 apply (simp)
 apply (rule cspF_rw_left, rule cspF_IF)+
 apply (rule cspF_rw_right, rule cspF_IF)+
 apply (rule cspF_decompo)
 apply (simp)+
 apply (rule cspF_rw_right)
 apply (rule cspF_SKIP)
 apply (simp)

 apply (simp)
 apply (rule cspF_rw_left, rule cspF_IF)+
 apply (rule cspF_rw_right, rule cspF_IF)+
 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_rw_right)
 apply (rule cspF_SKIP)
 apply (simp)
 apply (simp)

 apply (simp)
 apply (rule cspF_rw_left, rule cspF_IF)+
 apply (rule cspF_rw_right, rule cspF_IF)+
 apply (simp)
done

(*==============================================================*
 |                                                              |
 |       Associativity and Commutativity for SKIP and DIV       |
 |                    (for sequentialising)                     |
 |                                                              |
 *==============================================================*)

lemma cspF_Ext_pre_choice_SKIP_commut:
  "SKIP [+] (? :X -> Pf) =F[M,M] (? :X -> Pf) [+] SKIP"
by (rule cspF_commut)

lemma cspF_Ext_pre_choice_DIV_commut:
  "DIV [+] (? :X -> Pf) =F[M,M] (? :X -> Pf) [+] DIV"
by (rule cspF_commut)

lemma cspF_Ext_pre_choice_SKIP_assoc:
  "((? :X -> Pf) [+] SKIP) [+] (? :Y -> Qf)
   =F[M,M] ((? :X -> Pf) [+] (? :Y -> Qf)) [+] SKIP"
apply (rule cspF_rw_left)
apply (rule cspF_assoc[THEN cspF_sym])
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_reflex)
apply (rule cspF_commut)
apply (rule cspF_assoc)
done

lemma cspF_Ext_pre_choice_DIV_assoc:
  "((? :X -> Pf) [+] DIV) [+] (? :Y -> Qf)
   =F[M,M] ((? :X -> Pf) [+] (? :Y -> Qf)) [+] DIV"
apply (rule cspF_rw_left)
apply (rule cspF_assoc[THEN cspF_sym])
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_reflex)
apply (rule cspF_commut)
apply (rule cspF_assoc)
done

lemma cspF_Ext_choice_idem_assoc:
  "(P [+] Q) [+] Q =F[M,M] (P [+] Q)"
apply (rule cspF_rw_left)
apply (rule cspF_assoc[THEN cspF_sym])
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_reflex)
apply (rule cspF_idem)
apply (rule cspF_reflex)
done

lemma cspF_Ext_choice_SKIP_DIV_assoc:
  "(P [+] SKIP) [+] DIV =F[M,M] (P [+] SKIP)"
apply (rule cspF_rw_left)
apply (rule cspF_assoc[THEN cspF_sym])
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_reflex)
apply (rule cspF_SKIP_DIV)
apply (rule cspF_reflex)
done

lemma cspF_Ext_choice_DIV_SKIP_assoc:
  "(P [+] DIV) [+] SKIP =F[M,M] (P [+] SKIP)"
apply (rule cspF_rw_left)
apply (rule cspF_assoc[THEN cspF_sym])
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_reflex)
apply (rule cspF_SKIP_DIV)
apply (rule cspF_reflex)
done

lemmas cspF_SKIP_DIV_sort =
       cspF_Ext_choice_assoc
       cspF_Ext_pre_choice_SKIP_commut
       cspF_Ext_pre_choice_DIV_commut
       cspF_Ext_pre_choice_SKIP_assoc
       cspF_Ext_pre_choice_DIV_assoc
       cspF_Ext_choice_idem_assoc
       cspF_Ext_choice_SKIP_DIV_assoc
       cspF_Ext_choice_DIV_SKIP_assoc

(*==============================================================*
 |                                                              |
 |    decompostion control by the flag "Not_Decompo_Flag"       |
 |                                                              |
 *==============================================================*)

(*------------------------------------------------*
 |              trans with Flag                   |
 *------------------------------------------------*)

(*** rewrite (eq) ***)

lemma cspF_rw_flag_left_eq:
  "[| R1 =F[M1,M1] R2 ; Not_Decompo_Flag & R2 =F[M1,M3] R3 |] ==> R1 =F[M1,M3] R3"
by (simp add: eqF_def Not_Decompo_Flag_def)

lemma cspF_rw_flag_left_ref:
  "[| R1 =F[M1,M1] R2 ; Not_Decompo_Flag & R2 <=F[M1,M3] R3 |] ==> R1 <=F[M1,M3] R3"
by (simp add: refF_def eqF_def Not_Decompo_Flag_def)

lemmas cspF_rw_flag_left = cspF_rw_flag_left_eq cspF_rw_flag_left_ref

lemma cspF_rw_flag_right_eq:
  "[| R3 =F[M3,M3] R2 ; Not_Decompo_Flag & R1 =F[M1,M3] R2 |] ==> R1 =F[M1,M3] R3"
by (simp add: eqF_def Not_Decompo_Flag_def)

lemma cspF_rw_flag_right_ref:
  "[| R3 =F[M3,M3] R2 ; Not_Decompo_Flag & R1 <=F[M1,M3] R2 |] ==> R1 <=F[M1,M3] R3"
by (simp add: refF_def eqF_def Not_Decompo_Flag_def)

lemmas cspF_rw_flag_right = cspF_rw_flag_right_eq cspF_rw_flag_right_ref

(*------------------------------------------------*
 |              trans with Flag (ref)             |
 *------------------------------------------------*)

lemma cspF_tr_flag_left_eq:
   "[| P1 =F[M1,M1] P2 ; Not_Decompo_Flag & P2 =F[M1,M3] P3 |] ==> P1 =F[M1,M3] P3"
by (simp add: eqF_def)

lemma cspF_tr_flag_left_ref:
   "[| P1 <=F[M1,M1] P2 ; Not_Decompo_Flag & P2 <=F[M1,M3] P3 |] ==> P1 <=F[M1,M3] P3"
by (simp add: refF_def eqF_def Not_Decompo_Flag_def)

lemmas cspF_tr_flag_left = cspF_tr_flag_left_eq cspF_tr_flag_left_ref

lemma cspF_tr_flag_right_eq:
   "[| P2 =F[M3,M3] P3 ; Not_Decompo_Flag & P1 =F[M1,M3] P2 |] ==> P1 =F[M1,M3] P3"
by (simp add: eqF_def)

lemma cspF_tr_flag_right_ref:
  "[| P2 <=F[M3,M3] P3 ; Not_Decompo_Flag & P1 <=F[M1,M3] P2 |] ==> P1 <=F[M1,M3] P3"
by (simp add: refF_def eqF_def Not_Decompo_Flag_def)

lemmas cspF_tr_flag_right = cspF_tr_flag_right_eq cspF_tr_flag_right_ref

(*------------------------------------------------*
 |           trans with Flag (erule)              |
 *------------------------------------------------*)

(*** rewrite (eq) ***)

lemma cspF_rw_flag_left_eqE:
  "[| P1 =F[M1,M3] P3 ; P1 =F[M1,M1] P2 ; 
      [| Not_Decompo_Flag & P2 =F[M1,M3] P3 |] ==> R |] ==> R"
by (simp add: eqF_def Not_Decompo_Flag_def)

lemma cspF_rw_flag_left_refE:
  "[| P1 <=F[M1,M3] P3 ; P1 =F[M1,M1] P2 ; 
      [| Not_Decompo_Flag & P2 <=F[M1,M3] P3 |] ==> R |] ==> R"
apply (simp add: Not_Decompo_Flag_def)
apply (subgoal_tac "P2 <=F[M1,M3] P3")
apply (simp)
apply (rule cspF_rw_left)
apply (rule cspF_sym)
apply (simp)
apply (simp)
done

lemmas cspF_rw_flag_leftE = 
   cspF_rw_flag_left_eqE    cspF_rw_flag_left_refE

(* right *)

lemma cspF_rw_flag_right_eqE:
  "[| P1 =F[M1,M3] P3 ; P3 =F[M3,M3] P2 ;
      [| Not_Decompo_Flag & P1 =F[M1,M3] P2 |] ==> R |] ==> R"
by (simp add: eqF_def Not_Decompo_Flag_def)

lemma cspF_rw_flag_right_refE:
  "[| P1 <=F[M1,M3] P3 ; P3 =F[M3,M3] P2 ;
      [| Not_Decompo_Flag & P1 <=F[M1,M3] P2 |] ==> R |] ==> R"
apply (simp add: Not_Decompo_Flag_def)
apply (subgoal_tac "P1 <=F[M1,M3] P2")
apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_sym)
apply (simp)
apply (simp)
done

lemmas cspF_rw_flag_rightE = 
   cspF_rw_flag_right_eqE    cspF_rw_flag_right_refE

(*==============================================================*
 |  decompostion of Sequential composition with a flag          |
 |  It is often useful that the second process is not expanded. |
 |                   (until CSP-Prover 4)                       |
 *==============================================================*)

(*
lemma cspF_Seq_compo_mono_flag:
  "[| P1 <=F[M1,M2] Q1 ; 
      Not_Decompo_Flag & P2 <=F[M1,M2] Q2 |]
           ==> P1 ;; P2 <=F[M1,M2] Q1 ;; Q2"
by (simp add: cspF_Seq_compo_mono)

lemma cspF_Seq_compo_cong_flag:
  "[| P1 =F[M1,M2] Q1 ; 
      Not_Decompo_Flag & P2 =F[M1,M2] Q2 |]
           ==> P1 ;; P2 =F[M1,M2] Q1 ;; Q2"
by (simp add: cspF_Seq_compo_cong)

lemmas cspF_free_mono_flag =
       cspF_Ext_choice_mono cspF_Int_choice_mono cspF_Parallel_mono
       cspF_Hiding_mono cspF_Renaming_mono cspF_Seq_compo_mono_flag
       cspF_Depth_rest_mono

lemmas cspF_free_cong_flag =
       cspF_Ext_choice_cong cspF_Int_choice_cong cspF_Parallel_cong
       cspF_Hiding_cong cspF_Renaming_cong cspF_Seq_compo_cong_flag
       cspF_Depth_rest_cong

lemmas cspF_free_decompo_flag = cspF_free_mono_flag cspF_free_cong_flag
*)

(*===============================================================*
 |  decompostion of Sequential composition with a flag           |
 |  It is often useful that the second process is not rewritten. |
 |                    (since CSP-Prover 5)                       |
 *===============================================================*)

lemma cspF_Seq_compo_mono_flag:
  "[| P1 <=F[M1,M2] Q1 ; 
      Not_Rewrite_Flag & P2 <=F[M1,M2] Q2 |]
           ==> P1 ;; P2 <=F[M1,M2] Q1 ;; Q2"
by (simp add: cspF_Seq_compo_mono)

lemma cspF_Seq_compo_cong_flag:
  "[| P1 =F[M1,M2] Q1 ; 
      Not_Rewrite_Flag & P2 =F[M1,M2] Q2 |]
           ==> P1 ;; P2 =F[M1,M2] Q1 ;; Q2"
by (simp add: cspF_Seq_compo_cong)

lemmas cspF_free_mono_flag =
       cspF_Ext_choice_mono cspF_Int_choice_mono cspF_Parallel_mono
       cspF_Hiding_mono cspF_Renaming_mono cspF_Seq_compo_mono_flag
       cspF_Depth_rest_mono
       cspF_Rep_int_choice_mono_UNIV

       cspF_Alpha_parallel_mono


lemmas cspF_free_cong_flag =
       cspF_Ext_choice_cong cspF_Int_choice_cong cspF_Parallel_cong
       cspF_Hiding_cong cspF_Renaming_cong cspF_Seq_compo_cong_flag
       cspF_Depth_rest_cong
       cspF_Rep_int_choice_cong_UNIV

       cspF_Alpha_parallel_cong

lemmas cspF_free_decompo_flag = cspF_free_mono_flag cspF_free_cong_flag


end
