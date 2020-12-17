           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_law_ref
imports CSP_T_law_basic
begin

(*****************************************************************

         1. rules for refinement

 *****************************************************************)

(*-------------------------------------------------------*
 |            refinement and equality                    |
 *-------------------------------------------------------*)

lemma cspT_ref_eq_iff: "(P <=T[M,M] Q) = (P =T[M,M] Q |~| P)"
apply (simp add: cspT_semantics)
apply (rule)

(* <= *)
 apply (rule order_antisym)
 apply (simp add: subdomT_iff)
 apply (simp add: in_traces)
 apply (simp add: subdomT_iff)
 apply (simp add: in_traces)

(* => *)
 apply (erule order_antisymE)
 apply (rule)
 apply (rotate_tac 1)
 apply (erule subdomTE_ALL)
 apply (drule_tac x="t" in spec)
 apply (simp add: in_traces)
done

(*-------------------------------------------------------*
 |             simp STOP [+]                             |
 *-------------------------------------------------------*)

lemma cspT_Ent_choice_left1_ref:"P [+] Q <=T[M,M] P"
apply (simp add: cspT_semantics)
apply (rule, simp add: in_traces)
done

lemma cspT_Ent_choice_left2_ref:"P [+] Q <=T[M,M] Q"
apply (simp add: cspT_semantics)
apply (rule, simp add: in_traces)
done

lemmas cspT_Ent_choice_left_ref =
       cspT_Ent_choice_left1_ref
       cspT_Ent_choice_left2_ref

(*-------------------------------------------------------*
 |              decompose Internal choice                |
 *-------------------------------------------------------*)

(*** or <= ***)                                         (* unsafe *)

lemma cspT_Int_choice_left1:
  "P1 <=T[M1,M2] Q ==> P1 |~| P2 <=T[M1,M2] Q"
apply (simp add: cspT_semantics)
apply (rule, simp add: in_traces)
apply (force)
done

lemma cspT_Int_choice_left2:
  "P2 <=T[M1,M2] Q ==> P1 |~| P2 <=T[M1,M2] Q"
apply (rule cspT_rw_left)
apply (rule cspT_commut)
by (simp add: cspT_Int_choice_left1)

(*** <= and ***)                                          (* safe *)

lemma cspT_Int_choice_right:
  "[| P <=T[M1,M2] Q1 ; P <=T[M1,M2] Q2 |]
      ==> P <=T[M1,M2] Q1 |~| Q2"
apply (simp add: cspT_semantics)
apply (rule, simp add: in_traces)
apply (force)
done

(*-------------------------------------------------------*
 |        decompose Replicated internal choice           |
 *-------------------------------------------------------*)

(*** EX <= ***)                                           (* unsafe *)

lemma cspT_Rep_int_choice_sum_left:
  "(EX c. c:sumset C & Pf c <=T[M1,M2] Q)
      ==> !! :C .. Pf <=T[M1,M2] Q"
apply (simp add: cspT_semantics)
apply (rule, simp add: in_traces)
apply (force)
done

lemma cspT_Rep_int_choice_sum_left_x:
  "[| c: sumset C ; Pf c <=T[M1,M2] Q |]
  ==> !! :C .. Pf <=T[M1,M2] Q"
by (rule cspT_Rep_int_choice_sum_left, fast)

lemma cspT_Rep_int_choice_nat_left:
  "(EX n. n:N & Pf n <=T[M1,M2] Q)
      ==> !nat :N .. Pf <=T[M1,M2] Q"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_Rep_int_choice_sum_left, force)

lemma cspT_Rep_int_choice_nat_left_x:
  "[| n:N ; Pf n <=T[M1,M2] Q |]
  ==> !nat :N .. Pf <=T[M1,M2] Q"
by (rule cspT_Rep_int_choice_nat_left, fast)

lemma cspT_Rep_int_choice_set_left:
  "(EX X. X:Xs & Pf X <=T[M1,M2] Q)
      ==> !set :Xs .. Pf <=T[M1,M2] Q"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_Rep_int_choice_sum_left, force)

lemma cspT_Rep_int_choice_set_left_x:
  "[| X:Xs ; Pf X <=T[M1,M2] Q |]
  ==> !set :Xs .. Pf <=T[M1,M2] Q"
by (rule cspT_Rep_int_choice_set_left, fast)

lemma cspT_Rep_int_choice_com_left:
  "(EX a. a:X & Pf a <=T[M1,M2] Q)
      ==> ! :X .. Pf <=T[M1,M2] Q"
apply (simp add: Rep_int_choice_com_def)
by (rule cspT_Rep_int_choice_set_left, force)

lemma cspT_Rep_int_choice_com_left_x:
  "[| a:X ; Pf a <=T[M1,M2] Q |]
  ==> ! :X .. Pf <=T[M1,M2] Q"
by (rule cspT_Rep_int_choice_com_left, fast)

lemma cspT_Rep_int_choice_f_left:
  "[| inj f ; (EX a. a:X & Pf a <=T[M1,M2] Q) |]
      ==> !<f> :X .. Pf <=T[M1,M2] Q"
apply (simp add: Rep_int_choice_f_def)
by (rule cspT_Rep_int_choice_com_left, force)

lemma cspT_Rep_int_choice_f_left_x:
  "[| inj f ; a:X ; Pf a <=T[M1,M2] Q |]
  ==> !<f> :X .. Pf <=T[M1,M2] Q"
by (rule cspT_Rep_int_choice_f_left, simp, fast)

lemmas cspT_Rep_int_choice_left = cspT_Rep_int_choice_sum_left
                                  cspT_Rep_int_choice_nat_left
                                  cspT_Rep_int_choice_set_left
                                  cspT_Rep_int_choice_com_left
                                  cspT_Rep_int_choice_f_left

lemmas cspT_Rep_int_choice_left_x = cspT_Rep_int_choice_sum_left_x
                                  cspT_Rep_int_choice_nat_left_x
                                  cspT_Rep_int_choice_set_left_x
                                  cspT_Rep_int_choice_com_left_x
                                  cspT_Rep_int_choice_f_left_x

(*** <= ALL ***)                                         (* safe *)

lemma cspT_Rep_int_choice_sum_right:
  "[| !!c. c:sumset C ==> P <=T[M1,M2] Qf c |]
               ==> P <=T[M1,M2] !! :C .. Qf"
apply (simp add: cspT_semantics)
apply (rule, simp add: in_traces)
apply (force)
done

lemma cspT_Rep_int_choice_nat_right:
  "[| !!n. n:N ==> P <=T[M1,M2] Qf n |]
               ==> P <=T[M1,M2] !nat :N .. Qf"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_Rep_int_choice_sum_right, force)

lemma cspT_Rep_int_choice_set_right:
  "[| !!X. X:Xs ==> P <=T[M1,M2] Qf X |]
               ==> P <=T[M1,M2] !set :Xs .. Qf"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_Rep_int_choice_sum_right, force)

lemma cspT_Rep_int_choice_com_right:
  "[| !!a. a:X ==> P <=T[M1,M2] Qf a |]
               ==> P <=T[M1,M2] ! :X .. Qf"
apply (simp add: Rep_int_choice_com_def)
by (rule cspT_Rep_int_choice_set_right, force)

lemma cspT_Rep_int_choice_f_right:
  "[| inj f ; !!a. a:X ==> P <=T[M1,M2] Qf a |]
               ==> P <=T[M1,M2] !<f> :X .. Qf"
apply (simp add: Rep_int_choice_f_def)
by (rule cspT_Rep_int_choice_com_right, force)

lemmas cspT_Rep_int_choice_right 
     = cspT_Rep_int_choice_sum_right
       cspT_Rep_int_choice_nat_right
       cspT_Rep_int_choice_set_right
       cspT_Rep_int_choice_com_right
       cspT_Rep_int_choice_f_right

(* 1,2,3,f E *)

lemma cspT_Rep_int_choice_sum_rightE:
  "[| P <=T[M1,M2] !! :C .. Qf ;
      ALL c:sumset C. P <=T[M1,M2] Qf c ==> R
   |] ==> R"
apply (simp add: cspT_semantics)
apply (simp add: subdomT_iff)
apply (simp add: in_traces)
apply (force)
done

lemma cspT_Rep_int_choice_nat_rightE:
  "[| P <=T[M1,M2] !nat :N .. Qf ;
      ALL n:N. P <=T[M1,M2] Qf n ==> R
   |] ==> R"
apply (simp add: Rep_int_choice_ss_def)
by (erule cspT_Rep_int_choice_sum_rightE, force)

lemma cspT_Rep_int_choice_set_rightE:
  "[| P <=T[M1,M2] !set :Xs .. Qf ;
      ALL X:Xs. P <=T[M1,M2] Qf X ==> R
   |] ==> R"
apply (simp add: Rep_int_choice_ss_def)
by (erule cspT_Rep_int_choice_sum_rightE, force)

lemma cspT_Rep_int_choice_com_rightE:
  "[| P <=T[M1,M2] ! :X .. Qf ;
      ALL a:X. P <=T[M1,M2] Qf a ==> R
   |] ==> R"
apply (simp add: Rep_int_choice_com_def)
by (erule cspT_Rep_int_choice_set_rightE, force)

lemma cspT_Rep_int_choice_f_rightE:
  "[| P <=T[M1,M2] !<f> :X .. Qf ; inj f ;
      [| ALL a:X. P <=T[M1,M2] Qf a |] ==> R
   |] ==> R"
apply (simp add: Rep_int_choice_f_def)
by (erule cspT_Rep_int_choice_com_rightE, force)

lemmas cspT_Rep_int_choice_rightE =
       cspT_Rep_int_choice_sum_rightE
       cspT_Rep_int_choice_nat_rightE
       cspT_Rep_int_choice_set_rightE
       cspT_Rep_int_choice_com_rightE
       cspT_Rep_int_choice_f_rightE

(*-------------------------------------------------------*
 |             decomposition with subset                 |
 *-------------------------------------------------------*)

(*** Rep_int_choice ***)                                        (* unsafe *)

lemma cspT_Rep_int_choice_sum_subset:
  "[| sumset C2 <= sumset C1  ; !!c. c:sumset C2 ==> Pf c <=T[M1,M2] Qf c |]
                    ==> !! :C1 .. Pf <=T[M1,M2] !! :C2 .. Qf"
apply (simp add: cspT_semantics)
apply (rule, simp add: in_traces)
apply (force)
done

lemma cspT_Rep_int_choice_nat_subset:
  "[| N2 <= N1  ; !!n. n:N2 ==> Pf n <=T[M1,M2] Qf n |]
                    ==> !nat :N1 .. Pf <=T[M1,M2] !nat :N2 .. Qf"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_Rep_int_choice_sum_subset, auto)

lemma cspT_Rep_int_choice_set_subset:
  "[| Ys <= Xs  ; !!X. X:Ys ==> Pf X <=T[M1,M2] Qf X |]
                    ==> !set :Xs .. Pf <=T[M1,M2] !set :Ys .. Qf"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_Rep_int_choice_sum_subset, auto)

lemma cspT_Rep_int_choice_com_subset:
  "[| Y <= X  ; !!a. a:Y ==> Pf a <=T[M1,M2] Qf a |]
                    ==> ! :X .. Pf <=T[M1,M2] ! :Y .. Qf"
apply (simp add: Rep_int_choice_com_def)
by (rule cspT_Rep_int_choice_set_subset, auto)

lemma cspT_Rep_int_choice_f_subset:
  "[| inj f ; Y <= X  ; !!a. a:Y ==> Pf a <=T[M1,M2] Qf a |]
                    ==> !<f> :X .. Pf <=T[M1,M2] !<f> :Y .. Qf"
apply (simp add: Rep_int_choice_f_def)
by (rule cspT_Rep_int_choice_com_subset, auto)

lemmas cspT_Rep_int_choice_subset 
     = cspT_Rep_int_choice_sum_subset
       cspT_Rep_int_choice_nat_subset
       cspT_Rep_int_choice_set_subset
       cspT_Rep_int_choice_com_subset
       cspT_Rep_int_choice_f_subset

(*** ! x:X .. and ? -> ***)

lemma cspT_Int_Ext_pre_choice_subset:
  "[| Y ~={} ; Y <= X ; !!a. a:Y ==> Pf a <=T[M1,M2] Qf a |]
        ==> ! x:X .. (x -> Pf x) <=T[M1,M2]
            ? :Y -> Qf"
apply (simp add: cspT_semantics)
apply (rule, simp add: in_traces)
apply (force)
done

lemmas cspT_decompo_subset = cspT_Rep_int_choice_subset
                             cspT_Int_Ext_pre_choice_subset

(*-------------------------------------------------------*
 |               decompose external choice               |
 *-------------------------------------------------------*)

lemma cspT_Ext_choice_right:
  "[| P <=T[M1,M2] Q1 ;
      P <=T[M1,M2] Q2 |]
      ==> P <=T[M1,M2] Q1 [+] Q2"
apply (simp add: cspT_semantics)
apply (rule, simp add: in_traces)
apply (force)
done

end
