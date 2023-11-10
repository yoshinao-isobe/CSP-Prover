           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |               December 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_law_decompo
imports CSP_T_traces
begin

(*------------------------------------------------*
 |                                                |
 |      laws for monotonicity and congruence      |
 |                                                |
 *------------------------------------------------*)

(*********************************************************
                        Act_prefix mono
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Act_prefix_mono:
  "[| a = b ; P <=T[M1,M2] Q |] ==> a -> P <=T[M1,M2] b -> Q"
apply (simp add: cspT_semantics)
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_traces)
apply (fast)
done

lemma cspT_Act_prefix_cong:
  "[| a = b ; P =T[M1,M2] Q |] ==> a -> P =T[M1,M2] b -> Q"
apply (simp add: cspT_eq_ref_iff)
apply (simp add: cspT_Act_prefix_mono)
done

(*********************************************************
                   Ext_pre_choice mono 
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Ext_pre_choice_mono:
  "[| X = Y ; !! a. a:Y ==> Pf a <=T[M1,M2] Qf a |] ==> ? :X -> Pf <=T[M1,M2] ? :Y -> Qf"
apply (simp add: cspT_semantics)
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_traces)
apply (fast)
done

lemma cspT_Ext_pre_choice_cong:
  "[| X = Y ; !! a. a:Y ==> Pf a =T[M1,M2] Qf a |] ==> ? :X -> Pf =T[M1,M2] ? :Y -> Qf"
by (simp add: cspT_eq_ref_iff cspT_Ext_pre_choice_mono)

(*********************************************************
                      Ext choice mono
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Ext_choice_mono:
  "[| P1 <=T[M1,M2] Q1 ; P2 <=T[M1,M2] Q2 |] ==> P1 [+] P2 <=T[M1,M2] Q1 [+] Q2"
apply (simp add: cspT_semantics)
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_traces)
apply (fast)
done

lemma cspT_Ext_choice_cong:
  "[| P1 =T[M1,M2] Q1 ; P2 =T[M1,M2] Q2 |] ==> P1 [+] P2 =T[M1,M2] Q1 [+] Q2"
by (simp add: cspT_eq_ref_iff cspT_Ext_choice_mono)

(*********************************************************
                      Int choice mono
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Int_choice_mono:
  "[| P1 <=T[M1,M2] Q1 ; P2 <=T[M1,M2] Q2 |] ==> P1 |~| P2 <=T[M1,M2] Q1 |~| Q2"
apply (simp add: cspT_semantics)
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_traces)
apply (fast)
done

lemma cspT_Int_choice_cong:
  "[| P1 =T[M1,M2] Q1 ; P2 =T[M1,M2] Q2 |] ==> P1 |~| P2 =T[M1,M2] Q1 |~| Q2"
by (simp add: cspT_eq_ref_iff cspT_Int_choice_mono)

(*********************************************************
               replicated internal choice
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

(****** mono ******)

lemma cspT_Rep_int_choice_mono_sum:
  "[| C1 = C2 ; !! c. c: sumset C1 ==> Pf c <=T[M1,M2] Qf c |]
      ==> !! :C1 .. Pf <=T[M1,M2] !! :C2 .. Qf"
apply (simp add: cspT_semantics)
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_traces)
apply (fast)
done

(* nat *)

lemma cspT_Rep_int_choice_mono_nat:
  "[| N1 = N2 ; !! n. n:N1 ==> Pf n <=T[M1,M2] Qf n |]
      ==> !nat :N1 .. Pf <=T[M1,M2] !nat :N2 .. Qf"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_Rep_int_choice_mono_sum)
apply (auto)
done

(* set *)

lemma cspT_Rep_int_choice_mono_set:
  "[| Xs1 = Xs2 ; !! X. X:Xs1 ==> Pf X <=T[M1,M2] Qf X |]
      ==> !set :Xs1 .. Pf <=T[M1,M2] !set :Xs2 .. Qf"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_Rep_int_choice_mono_sum)
apply (auto)
done

lemma cspT_Rep_int_choice_mono_com:
  "[| X1 = X2 ; !! x. x:X1 ==> Pf x <=T[M1,M2] Qf x |]
      ==> ! :X1 .. Pf <=T[M1,M2] ! :X2 .. Qf"
apply (simp add: Rep_int_choice_com_def)
apply (rule cspT_Rep_int_choice_mono_set)
apply (auto)
done

lemma cspT_Rep_int_choice_mono_f:
  "[| inj f ; X1 = X2 ; !! x. x:X1 ==> Pf x <=T[M1,M2] Qf x |]
      ==> !<f> :X1 .. Pf <=T[M1,M2] !<f> :X2 .. Qf"
apply (simp add: Rep_int_choice_f_def)
apply (rule cspT_Rep_int_choice_mono_com)
apply (auto)
done

lemmas cspT_Rep_int_choice_mono = cspT_Rep_int_choice_mono_sum
                                  cspT_Rep_int_choice_mono_set
                                  cspT_Rep_int_choice_mono_nat
                                  cspT_Rep_int_choice_mono_com
                                  cspT_Rep_int_choice_mono_f

(****** cong ******)

lemma cspT_Rep_int_choice_cong_sum:
  "[| C1 = C2 ; !! c. c: sumset C1 ==> Pf c =T[M1,M2] Qf c |]
      ==> !! :C1 .. Pf =T[M1,M2] !! :C2 .. Qf"
by (simp add: cspT_eq_ref_iff cspT_Rep_int_choice_mono)

lemma cspT_Rep_int_choice_cong_nat:
  "[| N1 = N2 ; !! n. n:N1 ==> Pf n =T[M1,M2] Qf n |]
      ==> !nat :N1 .. Pf =T[M1,M2] !nat :N2 .. Qf"
by (simp add: cspT_eq_ref_iff cspT_Rep_int_choice_mono)

lemma cspT_Rep_int_choice_cong_set:
  "[| Xs1 = Xs2 ; !! X. X:Xs1 ==> Pf X =T[M1,M2] Qf X |]
      ==> !set :Xs1 .. Pf =T[M1,M2] !set :Xs2 .. Qf"
by (simp add: cspT_eq_ref_iff cspT_Rep_int_choice_mono)

lemma cspT_Rep_int_choice_cong_com:
  "[| X1 = X2 ; !! x. x:X1 ==> Pf x =T[M1,M2] Qf x |]
      ==> ! :X1 .. Pf =T[M1,M2] ! :X2 .. Qf"
by (simp add: cspT_eq_ref_iff cspT_Rep_int_choice_mono)

lemma cspT_Rep_int_choice_cong_f:
  "[| inj f ; X1 = X2 ; !! x. x:X1 ==> Pf x =T[M1,M2] Qf x |]
      ==> !<f> :X1 .. Pf =T[M1,M2] !<f> :X2 .. Qf"
by (simp add: cspT_eq_ref_iff cspT_Rep_int_choice_mono)

lemmas cspT_Rep_int_choice_cong = cspT_Rep_int_choice_cong_sum
                                  cspT_Rep_int_choice_cong_set
                                  cspT_Rep_int_choice_cong_nat
                                  cspT_Rep_int_choice_cong_com
                                  cspT_Rep_int_choice_cong_f

(*********************************************************
                   IF mono
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_IF_mono:
  "[| b1 = b2 ; P1 <=T[M1,M2] Q1 ; P2 <=T[M1,M2] Q2 |]
           ==> IF b1 THEN P1 ELSE P2 <=T[M1,M2]
               IF b2 THEN Q1 ELSE Q2"
apply (simp add: cspT_semantics)
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_traces)
done

lemma cspT_IF_cong:
  "[| b1 = b2 ; P1 =T[M1,M2] Q1 ;  P2 =T[M1,M2] Q2 |]
           ==> IF b1 THEN P1 ELSE P2 =T[M1,M2]
               IF b2 THEN Q1 ELSE Q2"
by (simp add: cspT_eq_ref_iff cspT_IF_mono)


(*********************************************************
                     Interrupt mono 
 *********************************************************)

lemma cspT_Interrupt_mono:
  "[| P1 <=T[M1,M2] Q1 ; P2 <=T[M1,M2] Q2 |] ==> P1 /> P2 <=T[M1,M2] Q1 /> Q2"
apply (simp add: cspT_semantics)
apply (rule subdomTI)
apply (simp add: subdomT_iff)
apply (simp add: in_traces_Interrupt)
apply (auto)
done

lemma cspT_Interrupt_cong:
  "[| P1 =T[M1,M2] Q1 ; P2 =T[M1,M2] Q2 |] ==> P1 /> P2 =T[M1,M2] Q1 /> Q2"
by (simp add: cspT_eq_ref_iff cspT_Interrupt_mono)


(*********************************************************
                     Parallel mono 
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Parallel_mono:
  "[| X = Y ; P1 <=T[M1,M2] Q1 ; P2 <=T[M1,M2] Q2 |]
           ==> P1 |[X]| P2 <=T[M1,M2] Q1 |[Y]| Q2"
apply (simp add: cspT_semantics)
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_traces)
apply (fast)
done

lemma cspT_Parallel_cong:
  "[| X = Y ; P1 =T[M1,M2] Q1 ; P2 =T[M1,M2] Q2 |]
           ==> P1 |[X]| P2 =T[M1,M2] Q1 |[Y]| Q2"
by (simp add: cspT_eq_ref_iff cspT_Parallel_mono)

(*********************************************************
                        Hiding mono
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Hiding_mono:
  "[| X = Y ; P <=T[M1,M2] Q |] ==> P -- X <=T[M1,M2] Q -- Y"
apply (simp add: cspT_semantics)
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_traces)
apply (fast)
done

lemma cspT_Hiding_cong:
  "[| X = Y ; P =T[M1,M2] Q |] ==> P -- X =T[M1,M2] Q -- Y"
by (simp add: cspT_eq_ref_iff cspT_Hiding_mono)

(*********************************************************
                        Renaming mono
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Renaming_mono:
  "[| r1 = r2 ; P <=T[M1,M2] Q |] ==> P [[r1]] <=T[M1,M2] Q [[r2]]"
apply (simp add: cspT_semantics)
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_traces)
apply (fast)
done

lemma cspT_Renaming_cong:
  "[| r1 = r2 ; P =T[M1,M2] Q |] ==> P [[r1]] =T[M1,M2] Q [[r2]]"
by (simp add: cspT_eq_ref_iff cspT_Renaming_mono)

(*********************************************************
               Sequential composition mono 
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Seq_compo_mono:
  "[| P1 <=T[M1,M2] Q1 ; P2 <=T[M1,M2] Q2 |]
           ==> P1 ;; P2 <=T[M1,M2] Q1 ;; Q2"
apply (simp add: cspT_semantics)
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_traces)
apply (fast)
done

lemma cspT_Seq_compo_cong:
  "[| P1 =T[M1,M2] Q1 ; P2 =T[M1,M2] Q2 |] ==> P1 ;; P2 =T[M1,M2] Q1 ;; Q2"
by (simp add: cspT_eq_ref_iff cspT_Seq_compo_mono)

lemma cspT_Seq_compo_rw_left:
  "[| P1 =T[M,M] P2 |] ==> P1 ;; Q =T[M,M] P2 ;; Q"
by (rule cspT_Seq_compo_cong, simp_all)

lemma cspT_Seq_compo_rw_right:
  "[| Q1 =T[M,M] Q2 |] ==> P ;; Q1 =T[M,M] P ;; Q2"
by (rule cspT_Seq_compo_cong, simp_all)

(*********************************************************
                        Depth_rest mono
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Depth_rest_mono:
  "[| n1 = n2 ; P <=T[M1,M2] Q |] ==> P |. n1 <=T[M1,M2] Q |. n2"
apply (simp add: cspT_semantics)
apply (simp add: subdomT_iff)
apply (intro allI impI)
apply (simp add: in_traces)
done

lemma cspT_Depth_rest_cong:
  "[| n1 = n2 ; P =T[M1,M2] Q |] ==> P |. n1 =T[M1,M2] Q |. n2"
by (simp add: cspT_eq_ref_iff cspT_Depth_rest_mono)

(*********************************************************
                        Timeout mono
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Timeout_mono:
  "[| P1 <=T[M1,M2] Q1 ; P2 <=T[M1,M2] Q2 |]
      ==> P1 [> P2 <=T[M1,M2] Q1 [> Q2"
apply (rule cspT_Ext_choice_mono)
apply (rule cspT_Int_choice_mono)
apply (simp_all)
done

lemma cspT_Timeout_cong:
  "[| P1 =T[M1,M2] Q1 ; P2 =T[M1,M2] Q2 |]
      ==> P1 [> P2 =T[M1,M2] Q1 [> Q2"
by (simp add: cspT_eq_ref_iff cspT_Timeout_mono)

(*------------------------------------------------------*
 |                       alias                          |
 *------------------------------------------------------*)

lemmas cspT_free_mono =
   cspT_Ext_choice_mono cspT_Int_choice_mono cspT_Interrupt_mono
   cspT_Parallel_mono
   cspT_Hiding_mono cspT_Renaming_mono cspT_Seq_compo_mono
   cspT_Depth_rest_mono

lemmas cspT_mono = cspT_free_mono
   cspT_Act_prefix_mono cspT_Ext_pre_choice_mono 
   cspT_Rep_int_choice_mono cspT_IF_mono 

lemmas cspT_free_cong =
   cspT_Ext_choice_cong cspT_Int_choice_cong cspT_Interrupt_cong
   cspT_Parallel_cong
   cspT_Hiding_cong cspT_Renaming_cong cspT_Seq_compo_cong
   cspT_Depth_rest_cong

lemmas cspT_cong = cspT_free_cong
   cspT_Act_prefix_cong cspT_Ext_pre_choice_cong 
   cspT_Rep_int_choice_cong cspT_IF_cong 

lemmas cspT_free_decompo = cspT_free_mono cspT_free_cong
lemmas cspT_decompo = cspT_mono cspT_cong

lemmas cspT_rm_head_mono = cspT_Act_prefix_mono cspT_Ext_pre_choice_mono 
lemmas cspT_rm_head_cong = cspT_Act_prefix_cong cspT_Ext_pre_choice_cong
lemmas cspT_rm_head      = cspT_rm_head_mono cspT_rm_head_cong

(*-------------------------------------------------------*
 |            decomposition with ALL and EX              |
 *-------------------------------------------------------*)

(*** Rep_int_choice ***)

lemma cspT_Rep_int_choice_sum_decompo_ALL_EX_ref:
  "ALL c2: sumset C2. EX c1: sumset C1. (Pf c1) <=T[M1,M2] (Qf c2)
   ==> !! :C1 .. Pf <=T[M1,M2] !! :C2 .. Qf"
apply (simp add: cspT_semantics)
apply (rule, simp add: in_traces)
apply (erule disjE)
apply (simp)
apply (elim bexE)
apply (drule_tac x="c" in bspec, simp)
apply (erule bexE)
apply (rule disjI2)
apply (rule_tac x="c1" in bexI)
apply (erule subdomTE)
apply (simp_all)
done

lemma cspT_Rep_int_choice_nat_decompo_ALL_EX_ref:
  "ALL n2:N2. EX n1:N1. (Pf n1) <=T[M1,M2] (Qf n2)
   ==> !nat :N1 .. Pf <=T[M1,M2] !nat :N2 .. Qf"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_Rep_int_choice_sum_decompo_ALL_EX_ref)
apply (auto)
apply (drule_tac x="a" in bspec, simp)
apply (auto)
done

lemma cspT_Rep_int_choice_set_decompo_ALL_EX_ref:
  "ALL X2:Xs2. EX X1:Xs1. (Pf X1) <=T[M1,M2] (Qf X2)
   ==> !set :Xs1 .. Pf <=T[M1,M2] !set :Xs2 .. Qf"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_Rep_int_choice_sum_decompo_ALL_EX_ref)
apply (auto)
apply (drule_tac x="a" in bspec, simp)
apply (auto)
done

lemmas cspT_Rep_int_choice_decompo_ALL_EX_ref =
       cspT_Rep_int_choice_sum_decompo_ALL_EX_ref
       cspT_Rep_int_choice_nat_decompo_ALL_EX_ref
       cspT_Rep_int_choice_set_decompo_ALL_EX_ref

lemma cspT_Rep_int_choice_sum_decompo_ALL_EX_eq:
  "[| ALL c1: sumset C1. EX c2: sumset C2. (Pf c1) =T[M1,M2] (Qf c2) ;
      ALL c2: sumset C2. EX c1: sumset C1. (Pf c1) =T[M1,M2] (Qf c2) |]
   ==> !! :C1 .. Pf =T[M1,M2] !! :C2 .. Qf"
apply (simp add: cspT_eq_ref_iff)
apply (rule conjI)
apply (rule cspT_Rep_int_choice_decompo_ALL_EX_ref)
apply (force)
apply (rule cspT_Rep_int_choice_decompo_ALL_EX_ref)
apply (force)
done

lemma cspT_Rep_int_choice_nat_decompo_ALL_EX_eq:
  "[| ALL n1:N1. EX n2:N2. (Pf n1) =T[M1,M2] (Qf n2) ;
      ALL n2:N2. EX n1:N1. (Pf n1) =T[M1,M2] (Qf n2) |]
   ==> !nat :N1 .. Pf =T[M1,M2] !nat :N2 .. Qf"
apply (simp add: cspT_eq_ref_iff)
apply (rule conjI)
apply (rule cspT_Rep_int_choice_decompo_ALL_EX_ref)
apply (force)
apply (rule cspT_Rep_int_choice_decompo_ALL_EX_ref)
apply (force)
done

lemma cspT_Rep_int_choice_set_decompo_ALL_EX_eq:
  "[| ALL X1:Xs1. EX X2:Xs2. (Pf X1) =T[M1,M2] (Qf X2) ;
      ALL X2:Xs2. EX X1:Xs1. (Pf X1) =T[M1,M2] (Qf X2) |]
   ==> !set :Xs1 .. Pf =T[M1,M2] !set :Xs2 .. Qf"
apply (simp add: cspT_eq_ref_iff)
apply (rule conjI)
apply (rule cspT_Rep_int_choice_decompo_ALL_EX_ref)
apply (force)
apply (rule cspT_Rep_int_choice_decompo_ALL_EX_ref)
apply (force)
done

lemmas cspT_Rep_int_choice_decompo_ALL_EX_eq =
       cspT_Rep_int_choice_sum_decompo_ALL_EX_eq
       cspT_Rep_int_choice_nat_decompo_ALL_EX_eq
       cspT_Rep_int_choice_set_decompo_ALL_EX_eq

lemmas cspT_Rep_int_choice_decompo_ALL_EX
     = cspT_Rep_int_choice_decompo_ALL_EX_ref
       cspT_Rep_int_choice_decompo_ALL_EX_eq

(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)

(*********************************************************
                        Act_prefix mono
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

(** mono **)

lemma cspT_Send_prefix_mono:
  "[| a = b ; P <=T[M1,M2] Q |] ==> a ! v -> P <=T[M1,M2] b ! v -> Q"
apply (simp add: csp_prefix_ss_def)
apply (simp add: cspT_decompo)
done

lemma cspT_Rec_prefix_mono:
  "[| inj a; a = b ; X = Y ; 
      !! x. x:Y ==> Pf x <=T[M1,M2] Qf x |]
    ==> a ? x:X -> Pf x <=T[M1,M2] b ? x:Y -> Qf x"
apply (simp add: csp_prefix_ss_def)
apply (rule cspT_Ext_pre_choice_mono)
apply (simp)
apply (simp add: image_iff)
apply (erule bexE)
apply (simp)
done

lemma cspT_Int_pre_choice_mono:
  "[| X = Y ; 
      !! x. x:Y ==> Pf x <=T[M1,M2] Qf x |]
    ==> ! :X -> Pf <=T[M1,M2] ! :Y -> Qf"
apply (simp add: csp_prefix_ss_def)
apply (simp add: cspT_decompo)
done

lemma cspT_Nondet_send_prefix_mono:
  "[| inj a; a = b ; X = Y ; 
      !! x. x:Y ==> Pf x <=T[M1,M2] Qf x |]
    ==> a !? x:X -> Pf x <=T[M1,M2] b !? x:Y -> Qf x"
apply (simp add: csp_prefix_ss_def)
apply (rule cspT_mono)
apply (simp)
apply (rule cspT_mono)
apply (simp)
apply (simp add: image_iff)
apply (erule bexE)
apply (simp)
done

(** cong **)

lemma cspT_Send_prefix_cong:
  "[| a = b ; P =T[M1,M2] Q |] ==> a ! v -> P =T[M1,M2] b ! v -> Q"
apply (simp add: csp_prefix_ss_def)
apply (simp add: cspT_decompo)
done

lemma cspT_Rec_prefix_cong:
  "[| inj a; a = b ; X = Y ; 
      !! x. x:Y ==> Pf x =T[M1,M2] Qf x |]
    ==> a ? x:X -> Pf x =T[M1,M2] b ? x:Y -> Qf x"
by (simp add: cspT_eq_ref_iff cspT_Rec_prefix_mono)

lemma cspT_Int_pre_choice_cong:
  "[| X = Y ; 
      !! x. x:Y ==> Pf x =T[M1,M2] Qf x |]
    ==> ! :X -> Pf =T[M1,M2] ! :Y -> Qf"
apply (simp add: csp_prefix_ss_def)
apply (simp add: cspT_decompo)
done

lemma cspT_Nondet_send_prefix_cong:
  "[| inj a; a = b ; X = Y ; 
      !! x. x:Y ==> Pf x =T[M1,M2] Qf x |]
    ==> a !? x:X -> Pf x =T[M1,M2] b !? x:Y -> Qf x"
by (simp add: cspT_eq_ref_iff cspT_Nondet_send_prefix_mono)

lemmas cspT_prefix_ss_mono = cspT_Send_prefix_mono
                             cspT_Rec_prefix_mono
                             cspT_Int_pre_choice_mono
                             cspT_Nondet_send_prefix_mono

lemmas cspT_prefx_ss_cong = cspT_Send_prefix_cong
                            cspT_Rec_prefix_cong
                            cspT_Int_pre_choice_cong
                            cspT_Nondet_send_prefix_cong


(* ------------------------------------------------------ *
                 decomposition with ss
 * ------------------------------------------------------ *)

lemmas cspT_mono_ss = cspT_mono  cspT_prefix_ss_mono
lemmas cspT_cong_ss = cspT_cong  cspT_prefx_ss_cong
lemmas cspT_decompo_ss = cspT_mono_ss cspT_cong_ss

(*********************************************************
             Rep_internal_choice for UNIV 
              this is useful for tactic
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

(* mono_UNIV *)

lemma cspT_Rep_int_choice_mono_UNIV_nat:
  "[| !! n. Pf n <=T[M1,M2] Qf n |]
      ==> !nat n .. Pf n <=T[M1,M2] !nat n .. Qf n"
by (simp add: cspT_Rep_int_choice_mono)

lemma cspT_Rep_int_choice_mono_UNIV_set:
  "[| !! X. Pf X <=T[M1,M2] Qf X |]
      ==> !set X .. Pf X <=T[M1,M2] !set X .. Qf X"
by (simp add: cspT_Rep_int_choice_mono)

lemma cspT_Rep_int_choice_mono_UNIV_com:
  "[| !! x. Pf x <=T[M1,M2] Qf x |]
      ==> ! x .. Pf x <=T[M1,M2] ! x .. Qf x"
by (simp add: cspT_Rep_int_choice_mono)

lemma cspT_Rep_int_choice_mono_UNIV_f:
  "[| inj f ; !! x. Pf x <=T[M1,M2] Qf x |]
      ==> !<f> x .. Pf x <=T[M1,M2] !<f> x .. Qf x"
by (simp add: cspT_Rep_int_choice_mono)

lemmas cspT_Rep_int_choice_mono_UNIV = 
      cspT_Rep_int_choice_mono_UNIV_nat
      cspT_Rep_int_choice_mono_UNIV_set
      cspT_Rep_int_choice_mono_UNIV_com
      cspT_Rep_int_choice_mono_UNIV_f

(* cong *)

lemma cspT_Rep_int_choice_cong_UNIV_nat:
  "[| !! n. Pf n =T[M1,M2] Qf n |]
      ==> !nat n .. Pf n =T[M1,M2] !nat n .. Qf n"
by (simp add: cspT_Rep_int_choice_cong)

lemma cspT_Rep_int_choice_cong_UNIV_set:
  "[| !! X. Pf X =T[M1,M2] Qf X |]
      ==> !set X .. Pf X =T[M1,M2] !set X .. Qf X"
by (simp add: cspT_Rep_int_choice_cong)

lemma cspT_Rep_int_choice_cong_UNIV_com:
  "[| !! x. Pf x =T[M1,M2] Qf x |]
      ==> ! x .. Pf x =T[M1,M2] ! x .. Qf x"
by (simp add: cspT_Rep_int_choice_cong)

lemma cspT_Rep_int_choice_cong_UNIV_f:
  "[| inj f ; !! x. Pf x =T[M1,M2] Qf x |]
      ==> !<f> x .. Pf x =T[M1,M2] !<f> x .. Qf x"
by (simp add: cspT_Rep_int_choice_cong)

lemmas cspT_Rep_int_choice_cong_UNIV = 
      cspT_Rep_int_choice_cong_UNIV_nat
      cspT_Rep_int_choice_cong_UNIV_set
      cspT_Rep_int_choice_cong_UNIV_com
      cspT_Rep_int_choice_cong_UNIV_f

end
