           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_law_decompo
imports CSP_F_domain CSP_T.CSP_T_law_decompo
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

lemma cspF_Act_prefix_mono:
  "[| a = b ; P <=F[M1,M2] Q |] ==> a -> P <=F[M1,M2] b -> Q"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Act_prefix_mono)
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (simp add: in_failures)
apply (fast)
done

lemma cspF_Act_prefix_cong:
  "[| a = b ; P =F[M1,M2] Q |] ==> a -> P =F[M1,M2] b -> Q"
apply (simp add: cspF_eq_ref_iff)
apply (simp add: cspF_Act_prefix_mono)
done

(*********************************************************
                   Ext_pre_choice mono 
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Ext_pre_choice_mono:
  "[| X = Y ; !! a. a:Y ==> Pf a <=F[M1,M2] Qf a |]
    ==> ? :X -> Pf <=F[M1,M2] ? :Y -> Qf"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Ext_pre_choice_mono)
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (simp add: in_failures)
apply (fast)
done

lemma cspF_Ext_pre_choice_cong:
  "[| X = Y ; !! a. a:Y ==> Pf a =F[M1,M2] Qf a |]
    ==> ? :X -> Pf =F[M1,M2] ? :Y -> Qf"
by (simp add: cspF_eq_ref_iff cspF_Ext_pre_choice_mono)

(*********************************************************
                      Ext choice mono
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Ext_choice_mono:
  "[| P1 <=F[M1,M2] Q1 ; P2 <=F[M1,M2] Q2 |] ==> P1 [+] P2 <=F[M1,M2] Q1 [+] Q2"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Ext_choice_mono)
apply (simp add: cspT_semantics)
apply (simp add: subdomT_iff)
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (simp add: in_failures)
apply (elim conjE disjE)
apply (force)+
done

lemma cspF_Ext_choice_cong:
  "[| P1 =F[M1,M2] Q1 ; P2 =F[M1,M2] Q2 |] ==> P1 [+] P2 =F[M1,M2] Q1 [+] Q2"
by (simp add: cspF_eq_ref_iff cspF_Ext_choice_mono)

(*********************************************************
                      Int choice mono
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Int_choice_mono:
  "[| P1 <=F[M1,M2] Q1 ; P2 <=F[M1,M2] Q2 |] ==> P1 |~| P2 <=F[M1,M2] Q1 |~| Q2"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Int_choice_mono)
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (simp add: in_failures)
apply (fast)
done

lemma cspF_Int_choice_cong:
  "[| P1 =F[M1,M2] Q1 ; P2 =F[M1,M2] Q2 |] ==> P1 |~| P2 =F[M1,M2] Q1 |~| Q2"
by (simp add: cspF_eq_ref_iff cspF_Int_choice_mono)

(*********************************************************
               replicated internal choice
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

(* mono *)

lemma cspF_Rep_int_choice_mono_sum:
  "[| C1 = C2 ; !! c. c: sumset C1 ==> Pf c <=F[M1,M2] Qf c |]
      ==> !! :C1 .. Pf <=F[M1,M2] !! :C2 .. Qf"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_mono_sum)
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (simp add: in_failures)
apply (fast)
done

lemma cspF_Rep_int_choice_mono_nat:
  "[| N1 = N2 ; !! n. n:N2 ==> Pf n <=F[M1,M2] Qf n |]
      ==> !nat :N1 .. Pf <=F[M1,M2] !nat :N2 .. Qf"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_Rep_int_choice_mono_sum, auto)

lemma cspF_Rep_int_choice_mono_set:
  "[| Xs1 = Xs2 ; !! X. X:Xs2 ==> Pf X <=F[M1,M2] Qf X |]
      ==> !set :Xs1 .. Pf <=F[M1,M2] !set :Xs2 .. Qf"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_Rep_int_choice_mono_sum, auto)

lemma cspF_Rep_int_choice_mono_com:
  "[| X1 = X2 ; !! x. x:X2 ==> Pf x <=F[M1,M2] Qf x |]
      ==> ! :X1 .. Pf <=F[M1,M2] ! :X2 .. Qf"
apply (simp add: Rep_int_choice_com_def)
by (rule cspF_Rep_int_choice_mono_set, auto)

lemma cspF_Rep_int_choice_mono_f:
  "[| inj f ; X1 = X2 ; !! x. x:X2 ==> Pf x <=F[M1,M2] Qf x |]
      ==> !<f> :X1 .. Pf <=F[M1,M2] !<f> :X2 .. Qf"
apply (simp add: Rep_int_choice_f_def)
by (rule cspF_Rep_int_choice_mono_com, auto)

lemmas cspF_Rep_int_choice_mono = cspF_Rep_int_choice_mono_sum
                                  cspF_Rep_int_choice_mono_nat
                                  cspF_Rep_int_choice_mono_set
                                  cspF_Rep_int_choice_mono_com
                                  cspF_Rep_int_choice_mono_f

(* cong *)

lemma cspF_Rep_int_choice_cong_sum:
  "[| C1 = C2 ; !! c. c: sumset C1 ==> Pf c =F[M1,M2] Qf c |]
      ==> !! :C1 .. Pf =F[M1,M2] !! :C2 .. Qf"
by (simp add: cspF_eq_ref_iff cspF_Rep_int_choice_mono)

lemma cspF_Rep_int_choice_cong_nat:
  "[| N1 = N2 ; !! n. n:N2 ==> Pf n =F[M1,M2] Qf n |]
      ==> !nat :N1 .. Pf =F[M1,M2] !nat :N2 .. Qf"
by (simp add: cspF_eq_ref_iff cspF_Rep_int_choice_mono)

lemma cspF_Rep_int_choice_cong_set:
  "[| Xs1 = Xs2 ; !! X. X:Xs2 ==> Pf X =F[M1,M2] Qf X |]
      ==> !set :Xs1 .. Pf =F[M1,M2] !set :Xs2 .. Qf"
by (simp add: cspF_eq_ref_iff cspF_Rep_int_choice_mono)

lemma cspF_Rep_int_choice_cong_com:
  "[| X1 = X2 ; !! x. x:X2 ==> Pf x =F[M1,M2] Qf x |]
      ==> ! :X1 .. Pf =F[M1,M2] ! :X2 .. Qf"
by (simp add: cspF_eq_ref_iff cspF_Rep_int_choice_mono)

lemma cspF_Rep_int_choice_cong_f:
  "[| inj f ; X1 = X2 ; !! x. x:X2 ==> Pf x =F[M1,M2] Qf x |]
      ==> !<f> :X1 .. Pf =F[M1,M2] !<f> :X2 .. Qf"
by (simp add: cspF_eq_ref_iff cspF_Rep_int_choice_mono)

lemmas cspF_Rep_int_choice_cong = cspF_Rep_int_choice_cong_sum
                                  cspF_Rep_int_choice_cong_nat
                                  cspF_Rep_int_choice_cong_set
                                  cspF_Rep_int_choice_cong_com
                                  cspF_Rep_int_choice_cong_f

(*********************************************************
                   IF mono
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_IF_mono:
  "[| b1 = b2 ; P1 <=F[M1,M2] Q1 ; P2 <=F[M1,M2] Q2 |]
           ==> IF b1 THEN P1 ELSE P2 <=F[M1,M2]
               IF b2 THEN Q1 ELSE Q2"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_IF_mono)
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (simp add: in_failures)
done

lemma cspF_IF_cong:
  "[| b1 = b2 ; P1 =F[M1,M2] Q1 ;  P2 =F[M1,M2] Q2 |]
           ==> IF b1 THEN P1 ELSE P2 =F[M1,M2]
               IF b2 THEN Q1 ELSE Q2"
by (simp add: cspF_eq_ref_iff cspF_IF_mono)

(*********************************************************
                   Interrupt mono
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Interrupt_mono:
  "[| P1 <=F[M1,M2] Q1 ; P2 <=F[M1,M2] Q2 |]
           ==> P1 /> P2 <=F[M1,M2] Q1 /> Q2"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Interrupt_mono)
apply (simp add: cspT_semantics)
apply (simp add: subdomT_iff)
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (simp add: in_failures)
apply (elim conjE disjE)
apply (force)+
done

lemma cspF_Interrupt_cong:
  "[| P1 =F[M1,M2] Q1 ;  P2 =F[M1,M2] Q2 |]
           ==> P1 /> P2 =F[M1,M2] Q1 /> Q2"
by (simp add: cspF_eq_ref_iff cspF_Interrupt_mono)

(*********************************************************
                     Parallel mono 
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Parallel_mono:
  "[| X = Y ; P1 <=F[M1,M2] Q1 ; P2 <=F[M1,M2] Q2 |]
           ==> P1 |[X]| P2 <=F[M1,M2] Q1 |[Y]| Q2"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Parallel_mono)
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (simp add: in_failures)
apply (fast)
done

lemma cspF_Parallel_cong:
  "[| X = Y ; P1 =F[M1,M2] Q1 ; P2 =F[M1,M2] Q2 |]
           ==> P1 |[X]| P2 =F[M1,M2] Q1 |[Y]| Q2"
by (simp add: cspF_eq_ref_iff cspF_Parallel_mono)

(*********************************************************
                        Hiding mono
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Hiding_mono:
  "[| X = Y ; P <=F[M1,M2] Q |] ==> P -- X <=F[M1,M2] Q -- Y"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Hiding_mono)
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (simp add: in_failures)
apply (fast)
done

lemma cspF_Hiding_cong:
  "[| X = Y ; P =F[M1,M2] Q |] ==> P -- X =F[M1,M2] Q -- Y"
by (simp add: cspF_eq_ref_iff cspF_Hiding_mono)

(*********************************************************
                        Renaming mono
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Renaming_mono:
  "[| r1 = r2 ; P <=F[M1,M2] Q |] ==> P [[r1]] <=F[M1,M2] Q [[r2]]"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Renaming_mono)
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (simp add: in_failures)
apply (fast)
done

lemma cspF_Renaming_cong:
  "[| r1 = r2 ; P =F[M1,M2] Q |] ==> P [[r1]] =F[M1,M2] Q [[r2]]"
by (simp add: cspF_eq_ref_iff cspF_Renaming_mono)

(*********************************************************
               Sequential composition mono 
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Seq_compo_mono:
  "[| P1 <=F[M1,M2] Q1 ; P2 <=F[M1,M2] Q2 |]
           ==> P1 ;; P2 <=F[M1,M2] Q1 ;; Q2"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Seq_compo_mono)
apply (simp add: cspT_semantics)
apply (simp add: subdomT_iff)
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (simp add: in_failures)
apply (fast)
done

lemma cspF_Seq_compo_cong:
  "[| P1 =F[M1,M2] Q1 ; P2 =F[M1,M2] Q2 |] ==> P1 ;; P2 =F[M1,M2] Q1 ;; Q2"
by (simp add: cspF_eq_ref_iff cspF_Seq_compo_mono)

(*********************************************************
                       Depth_rest mono
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Depth_rest_mono:
  "[| n1 = n2 ; P <=F[M1,M2] Q |] ==> P |. n1 <=F[M1,M2] Q |. n2"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Depth_rest_mono)
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (simp add: in_failures)
done

lemma cspF_Depth_rest_cong:
  "[| n1 = n2 ; P =F[M1,M2] Q |] ==> P |. n1 =F[M1,M2] Q |. n2"
by (simp add: cspF_eq_ref_iff cspF_Depth_rest_mono)

(*********************************************************
                        Timeout mono
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Timeout_mono:
  "[| P1 <=F[M1,M2] Q1 ; P2 <=F[M1,M2] Q2 |]
      ==> P1 [> P2 <=F[M1,M2] Q1 [> Q2"
apply (rule cspF_Ext_choice_mono)
apply (rule cspF_Int_choice_mono)
by (simp_all)

lemma cspF_Timeout_cong:
  "[| P1 =F[M1,M2] Q1 ; P2 =F[M1,M2] Q2 |]
      ==> P1 [> P2 =F[M1,M2] Q1 [> Q2"
by (simp add: cspF_eq_ref_iff cspF_Timeout_mono)

(*------------------------------------------------------*
 |                       alias                          |
 *------------------------------------------------------*)

lemmas cspF_free_mono =
   cspF_Ext_choice_mono cspF_Int_choice_mono cspF_Parallel_mono
   cspF_Hiding_mono cspF_Renaming_mono cspF_Seq_compo_mono
   cspF_Depth_rest_mono cspF_Interrupt_mono

lemmas cspF_mono = cspF_free_mono
   cspF_Act_prefix_mono cspF_Ext_pre_choice_mono 
   cspF_Rep_int_choice_mono cspF_IF_mono

lemmas cspF_free_cong =
   cspF_Ext_choice_cong cspF_Int_choice_cong cspF_Parallel_cong
   cspF_Hiding_cong cspF_Renaming_cong cspF_Seq_compo_cong
   cspF_Depth_rest_cong cspF_Interrupt_cong

lemmas cspF_cong = cspF_free_cong
   cspF_Act_prefix_cong cspF_Ext_pre_choice_cong 
   cspF_Rep_int_choice_cong cspF_IF_cong 

lemmas cspF_free_decompo = cspF_free_mono cspF_free_cong
lemmas cspF_decompo = cspF_mono cspF_cong

lemmas cspF_rm_head_mono = cspF_Act_prefix_mono cspF_Ext_pre_choice_mono 
lemmas cspF_rm_head_cong = cspF_Act_prefix_cong cspF_Ext_pre_choice_cong
lemmas cspF_rm_head      = cspF_rm_head_mono cspF_rm_head_cong

(*-------------------------------------------------------*
 |            decomposition with ALL and EX              |
 *-------------------------------------------------------*)

(*** Rep_int_choice ***)

lemma cspF_Rep_int_choice_sum_decompo_ALL_EX_ref:
  "ALL c2: sumset C2. EX c1: sumset C1. (Pf c1) <=F[M1,M2] (Qf c2)
   ==> !! :C1 .. Pf <=F[M1,M2] !! :C2 .. Qf"
apply (simp add: cspF_cspT_semantics)
apply (rule conjI)
apply (rule cspT_Rep_int_choice_decompo_ALL_EX)
apply (force)
apply (rule, simp add: in_failures)
apply (erule bexE)
apply (drule_tac x="c" in bspec, simp)
apply (erule bexE)
apply (rule_tac x="c1" in bexI)
apply (force)
apply (simp)
done

lemma cspF_Rep_int_choice_nat_decompo_ALL_EX_ref:
  "ALL n2:N2. EX n1:N1. (Pf n1) <=F[M1,M2] (Qf n2)
   ==> !nat :N1 .. Pf <=F[M1,M2] !nat :N2 .. Qf"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspF_Rep_int_choice_sum_decompo_ALL_EX_ref)
apply (auto)
apply (drule_tac x="a" in bspec, simp)
apply (auto)
done

lemma cspF_Rep_int_choice_set_decompo_ALL_EX_ref:
  "ALL X2:Xs2. EX X1:Xs1. (Pf X1) <=F[M1,M2] (Qf X2)
   ==> !set :Xs1 .. Pf <=F[M1,M2] !set :Xs2 .. Qf"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspF_Rep_int_choice_sum_decompo_ALL_EX_ref)
apply (auto)
apply (drule_tac x="a" in bspec, simp)
apply (auto)
done

lemmas cspF_Rep_int_choice_decompo_ALL_EX_ref =
       cspF_Rep_int_choice_sum_decompo_ALL_EX_ref
       cspF_Rep_int_choice_nat_decompo_ALL_EX_ref
       cspF_Rep_int_choice_set_decompo_ALL_EX_ref

lemma cspF_Rep_int_choice_sum_decompo_ALL_EX_eq:
  "[| ALL c1: sumset C1. EX c2: sumset C2. (Pf c1) =F[M1,M2] (Qf c2) ;
      ALL c2: sumset C2. EX c1: sumset C1. (Pf c1) =F[M1,M2] (Qf c2) |]
   ==> !! :C1 .. Pf =F[M1,M2] !! :C2 .. Qf"
apply (simp add: cspF_eq_ref_iff)
apply (rule conjI)
apply (rule cspF_Rep_int_choice_decompo_ALL_EX_ref)
apply (force)
apply (rule cspF_Rep_int_choice_decompo_ALL_EX_ref)
apply (force)
done

lemma cspF_Rep_int_choice_nat_decompo_ALL_EX_eq:
  "[| ALL n1:N1. EX n2:N2. (Pf n1) =F[M1,M2] (Qf n2) ;
      ALL n2:N2. EX n1:N1. (Pf n1) =F[M1,M2] (Qf n2) |]
   ==> !nat :N1 .. Pf =F[M1,M2] !nat :N2 .. Qf"
apply (simp add: cspF_eq_ref_iff)
apply (rule conjI)
apply (rule cspF_Rep_int_choice_decompo_ALL_EX_ref)
apply (force)
apply (rule cspF_Rep_int_choice_decompo_ALL_EX_ref)
apply (force)
done

lemma cspF_Rep_int_choice_set_decompo_ALL_EX_eq:
  "[| ALL X1:Xs1. EX X2:Xs2. (Pf X1) =F[M1,M2] (Qf X2) ;
      ALL X2:Xs2. EX X1:Xs1. (Pf X1) =F[M1,M2] (Qf X2) |]
   ==> !set :Xs1 .. Pf =F[M1,M2] !set :Xs2 .. Qf"
apply (simp add: cspF_eq_ref_iff)
apply (rule conjI)
apply (rule cspF_Rep_int_choice_decompo_ALL_EX_ref)
apply (force)
apply (rule cspF_Rep_int_choice_decompo_ALL_EX_ref)
apply (force)
done

lemmas cspF_Rep_int_choice_decompo_ALL_EX_eq =
       cspF_Rep_int_choice_sum_decompo_ALL_EX_eq
       cspF_Rep_int_choice_nat_decompo_ALL_EX_eq
       cspF_Rep_int_choice_set_decompo_ALL_EX_eq

lemmas cspF_Rep_int_choice_decompo_ALL_EX
     = cspF_Rep_int_choice_decompo_ALL_EX_ref
       cspF_Rep_int_choice_decompo_ALL_EX_eq

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

lemma cspF_Send_prefix_mono:
  "[| a = b ; P <=F[M1,M2] Q |] ==> a ! v -> P <=F[M1,M2] b ! v -> Q"
apply (simp add: csp_prefix_ss_def)
apply (simp add: cspF_decompo)
done

lemma cspF_Rec_prefix_mono:
  "[| inj a; a = b ; X = Y ; 
      !! x. x:Y ==> Pf x <=F[M1,M2] Qf x |]
    ==> a ? x:X -> Pf x <=F[M1,M2] b ? x:Y -> Qf x"
apply (simp add: csp_prefix_ss_def)
apply (rule cspF_Ext_pre_choice_mono)
apply (simp)
apply (simp add: image_iff)
apply (erule bexE)
apply (simp)
done

lemma cspF_Int_pre_choice_mono:
  "[| X = Y ; 
      !! x. x:Y ==> Pf x <=F[M1,M2] Qf x |]
    ==> ! :X -> Pf <=F[M1,M2] ! :Y -> Qf"
apply (simp add: csp_prefix_ss_def)
apply (simp add: cspF_decompo)
done

lemma cspF_Nondet_send_prefix_mono:
  "[| inj a; a = b ; X = Y ; 
      !! x. x:Y ==> Pf x <=F[M1,M2] Qf x |]
    ==> a !? x:X -> Pf x <=F[M1,M2] b !? x:Y -> Qf x"
apply (simp add: csp_prefix_ss_def)
apply (rule cspF_mono)
apply (simp)
apply (rule cspF_mono)
apply (simp)
apply (simp add: image_iff)
apply (erule bexE)
apply (simp)
done

(** cong **)

lemma cspF_Send_prefix_cong:
  "[| a = b ; P =F[M1,M2] Q |] ==> a ! v -> P =F[M1,M2] b ! v -> Q"
apply (simp add: csp_prefix_ss_def)
apply (simp add: cspF_decompo)
done

lemma cspF_Rec_prefix_cong:
  "[| inj a; a = b ; X = Y ; 
      !! x. x:Y ==> Pf x =F[M1,M2] Qf x |]
    ==> a ? x:X -> Pf x =F[M1,M2] b ? x:Y -> Qf x"
by (simp add: cspF_eq_ref_iff cspF_Rec_prefix_mono)

lemma cspF_Int_pre_choice_cong:
  "[| X = Y ; 
      !! x. x:Y ==> Pf x =F[M1,M2] Qf x |]
    ==> ! :X -> Pf =F[M1,M2] ! :Y -> Qf"
apply (simp add: csp_prefix_ss_def)
apply (simp add: cspF_decompo)
done

lemma cspF_Nondet_send_prefix_cong:
  "[| inj a; a = b ; X = Y ; 
      !! x. x:Y ==> Pf x =F[M1,M2] Qf x |]
    ==> a !? x:X -> Pf x =F[M1,M2] b !? x:Y -> Qf x"
by (simp add: cspF_eq_ref_iff cspF_Nondet_send_prefix_mono)

lemmas cspF_prefix_ss_mono = cspF_Send_prefix_mono
                             cspF_Rec_prefix_mono
                             cspF_Int_pre_choice_mono
                             cspF_Nondet_send_prefix_mono

lemmas cspF_prefx_ss_cong = cspF_Send_prefix_cong
                            cspF_Rec_prefix_cong
                            cspF_Int_pre_choice_cong
                            cspF_Nondet_send_prefix_cong


(* ------------------------------------------------------ *
                 decomposition with ss
 * ------------------------------------------------------ *)

lemmas cspF_mono_ss = cspF_mono  cspF_prefix_ss_mono
lemmas cspF_cong_ss = cspF_cong  cspF_prefx_ss_cong
lemmas cspF_decompo_ss = cspF_mono_ss cspF_cong_ss

(*********************************************************
             Rep_internal_choice for UNIV 
              this is useful for tactic
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

(* mono_UNIV *)

lemma cspF_Rep_int_choice_mono_UNIV_nat:
  "[| !! n. Pf n <=F[M1,M2] Qf n |]
      ==> !nat n .. Pf n <=F[M1,M2] !nat n .. Qf n"
by (simp add: cspF_Rep_int_choice_mono)

lemma cspF_Rep_int_choice_mono_UNIV_set:
  "[| !! X. Pf X <=F[M1,M2] Qf X |]
      ==> !set X .. Pf X <=F[M1,M2] !set X .. Qf X"
by (simp add: cspF_Rep_int_choice_mono)

lemma cspF_Rep_int_choice_mono_UNIV_com:
  "[| !! x. Pf x <=F[M1,M2] Qf x |]
      ==> ! x .. Pf x <=F[M1,M2] ! x .. Qf x"
by (simp add: cspF_Rep_int_choice_mono)

lemma cspF_Rep_int_choice_mono_UNIV_f:
  "[| inj f ; !! x. Pf x <=F[M1,M2] Qf x |]
      ==> !<f> x .. Pf x <=F[M1,M2] !<f> x .. Qf x"
by (simp add: cspF_Rep_int_choice_mono)

lemmas cspF_Rep_int_choice_mono_UNIV = 
      cspF_Rep_int_choice_mono_UNIV_nat
      cspF_Rep_int_choice_mono_UNIV_set
      cspF_Rep_int_choice_mono_UNIV_com
      cspF_Rep_int_choice_mono_UNIV_f

(* cong *)

lemma cspF_Rep_int_choice_cong_UNIV_nat:
  "[| !! n. Pf n =F[M1,M2] Qf n |]
      ==> !nat n .. Pf n =F[M1,M2] !nat n .. Qf n"
by (simp add: cspF_Rep_int_choice_cong)

lemma cspF_Rep_int_choice_cong_UNIV_set:
  "[| !! X. Pf X =F[M1,M2] Qf X |]
      ==> !set X .. Pf X =F[M1,M2] !set X .. Qf X"
by (simp add: cspF_Rep_int_choice_cong)

lemma cspF_Rep_int_choice_cong_UNIV_com:
  "[| !! x. Pf x =F[M1,M2] Qf x |]
      ==> ! x .. Pf x =F[M1,M2] ! x .. Qf x"
by (simp add: cspF_Rep_int_choice_cong)

lemma cspF_Rep_int_choice_cong_UNIV_f:
  "[| inj f ; !! x. Pf x =F[M1,M2] Qf x |]
      ==> !<f> x .. Pf x =F[M1,M2] !<f> x .. Qf x"
by (simp add: cspF_Rep_int_choice_cong)

lemmas cspF_Rep_int_choice_cong_UNIV = 
      cspF_Rep_int_choice_cong_UNIV_nat
      cspF_Rep_int_choice_cong_UNIV_set
      cspF_Rep_int_choice_cong_UNIV_com
      cspF_Rep_int_choice_cong_UNIV_f


end
