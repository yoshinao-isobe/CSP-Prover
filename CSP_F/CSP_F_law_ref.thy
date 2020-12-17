           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_law_ref
imports CSP_F_law_basic CSP_T.CSP_T_law_ref
begin

(*****************************************************************

         1. rules for refinement

 *****************************************************************)

(*-------------------------------------------------------*
 |            refinement and equality                    |
 *-------------------------------------------------------*)

lemma cspF_ref_eq_iff: "(P <=F[M,M] Q) = (P =F[M,M] Q |~| P)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_ref_eq_iff)
apply (rule)

(* <= *)
 apply (simp)
 apply (rule order_antisym)
 apply (simp add: subsetF_iff)
 apply (simp add: in_failures)
 apply (simp add: subsetF_iff)
 apply (simp add: in_failures)

(* => *)
 apply (simp)
 apply (erule conjE)
 apply (erule order_antisymE)
 apply (rule)
 apply (rotate_tac 2)
 apply (erule subsetFE_ALL)
 apply (drule_tac x="s" in spec)
 apply (drule_tac x="X" in spec)
 apply (simp add: in_failures)
done

(*-------------------------------------------------------*
 |              decompose Internal choice                |
 *-------------------------------------------------------*)

(*** or <= ***)                                         (* unsafe *)

lemma cspF_Int_choice_left1:
  "P1 <=F[M1,M2] Q ==> P1 |~| P2 <=F[M1,M2] Q"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Int_choice_left1)
apply (rule, simp add: in_failures)
apply (force)
done

lemma cspF_Int_choice_left2:
  "P2 <=F[M1,M2] Q ==> P1 |~| P2 <=F[M1,M2] Q"
apply (rule cspF_rw_left)
apply (rule cspF_commut)
by (simp add: cspF_Int_choice_left1)

(*** <= and ***)                                          (* safe *)

lemma cspF_Int_choice_right:
  "[| P <=F[M1,M2] Q1 ; P <=F[M1,M2] Q2 |]
      ==> P <=F[M1,M2] Q1 |~| Q2"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Int_choice_right)
apply (rule, simp add: in_failures)
apply (force)
done

(*-------------------------------------------------------*
 |        decompose Replicated internal choice           |
 *-------------------------------------------------------*)

(*** EX <= ***)                                           (* unsafe *)

lemma cspF_Rep_int_choice_nat_left:
  "(EX n. n:N & Pf n <=F[M1,M2] Q)
      ==> !nat :N .. Pf <=F[M1,M2] Q"
apply (simp add: cspF_cspT_semantics)
apply (rule conjI)

apply (rule cspT_Rep_int_choice_left)
apply (fast)

apply (rule, simp add: in_failures)
apply (force)
done

lemma cspF_Rep_int_choice_nat_left_x:
  "[| n:N ; Pf n <=F[M1,M2] Q |]
  ==> !nat :N .. Pf <=F[M1,M2] Q"
apply (rule cspF_Rep_int_choice_nat_left)
by (fast)

lemma cspF_Rep_int_choice_set_left:
  "(EX X. X:Xs & Pf X <=F[M1,M2] Q)
      ==> !set :Xs .. Pf <=F[M1,M2] Q"
apply (simp add: cspF_cspT_semantics)
apply (rule conjI)

apply (rule cspT_Rep_int_choice_left)
apply (fast)

apply (rule, simp add: in_failures)
apply (force)
done

lemma cspF_Rep_int_choice_set_left_x:
  "[| X:Xs ; Pf X <=F[M1,M2] Q |]
  ==> !set :Xs .. Pf <=F[M1,M2] Q"
apply (rule cspF_Rep_int_choice_set_left)
by (fast)

lemma cspF_Rep_int_choice_com_left:
  "(EX a. a:X & Pf a <=F[M1,M2] Q)
      ==> ! :X .. Pf <=F[M1,M2] Q"
apply (simp add: Rep_int_choice_com_def)
apply (rule cspF_Rep_int_choice_set_left)
apply (erule exE)
apply (rule_tac x="{a}" in exI)
apply (auto)
done

lemma cspF_Rep_int_choice_com_left_x:
  "[| a:X ; Pf a <=F[M1,M2] Q |]
  ==> ! :X .. Pf <=F[M1,M2] Q"
apply (rule cspF_Rep_int_choice_com_left)
by (fast)

lemma cspF_Rep_int_choice_f_left:
  "[| inj f ; (EX a. a:X & Pf a <=F[M1,M2] Q) |]
      ==> !<f> :X .. Pf <=F[M1,M2] Q"
apply (simp add: Rep_int_choice_f_def)
apply (rule cspF_Rep_int_choice_com_left)
apply (erule exE)
apply (rule_tac x="f a" in exI)
apply (auto)
done

lemma cspF_Rep_int_choice_f_left_x:
  "[| inj f ; a:X ; Pf a <=F[M1,M2] Q |]
  ==> !<f> :X .. Pf <=F[M1,M2] Q"
apply (rule cspF_Rep_int_choice_f_left)
apply (simp)
by (fast)

lemmas cspF_Rep_int_choice_left = cspF_Rep_int_choice_nat_left
                                  cspF_Rep_int_choice_set_left
                                  cspF_Rep_int_choice_com_left
                                  cspF_Rep_int_choice_f_left

lemmas cspF_Rep_int_choice_left_x = cspF_Rep_int_choice_nat_left_x
                                  cspF_Rep_int_choice_set_left_x
                                  cspF_Rep_int_choice_com_left_x
                                  cspF_Rep_int_choice_f_left_x

(*** <= ALL ***)                                         (* safe *)

lemma cspF_Rep_int_choice_nat_right:
  "[| !!n. n:N ==> P <=F[M1,M2] Qf n |]
               ==> P <=F[M1,M2] !nat :N .. Qf"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_right)
apply (rule, simp add: in_failures)
apply (force)
done

lemma cspF_Rep_int_choice_set_right:
  "[| !!X. X:Xs ==> P <=F[M1,M2] Qf X |]
               ==> P <=F[M1,M2] !set :Xs .. Qf"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_right)
apply (rule, simp add: in_failures)
apply (force)
done

lemma cspF_Rep_int_choice_com_right:
  "[| !!a. a:X ==> P <=F[M1,M2] Qf a |]
               ==> P <=F[M1,M2] ! :X .. Qf"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_right)
apply (rule, simp add: in_failures)
apply (force)
done

lemma cspF_Rep_int_choice_f_right:
  "[| inj f ; !!a. a:X ==> P <=F[M1,M2] Qf a |]
               ==> P <=F[M1,M2] !<f> :X .. Qf"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_right)
apply (rule, simp add: in_failures)
apply (force)
done

lemmas cspF_Rep_int_choice_right 
     = cspF_Rep_int_choice_nat_right
       cspF_Rep_int_choice_set_right
       cspF_Rep_int_choice_com_right
       cspF_Rep_int_choice_f_right

(* 1,2,3,f E *)

lemma cspF_Rep_int_choice_nat_rightE:
  "[| P <=F[M1,M2] !nat :N .. Qf ;
      ALL n:N. P <=F[M1,M2] Qf n ==> R
   |] ==> R"
apply (simp add: cspF_cspT_semantics)
apply (elim conjE exE)
apply (erule cspT_Rep_int_choice_rightE)

apply (simp add: subsetF_iff)
apply (simp add: in_failures)
apply (force)
done

lemma cspF_Rep_int_choice_set_rightE:
  "[| P <=F[M1,M2] !set :Xs .. Qf ;
      ALL X:Xs. P <=F[M1,M2] Qf X ==> R
   |] ==> R"
apply (simp add: cspF_cspT_semantics)
apply (elim conjE exE)
apply (erule cspT_Rep_int_choice_rightE)

apply (simp add: subsetF_iff)
apply (simp add: in_failures)
apply (force)
done

lemma cspF_Rep_int_choice_com_rightE:
  "[| P <=F[M1,M2] ! :X .. Qf ;
      ALL a:X. P <=F[M1,M2] Qf a ==> R
   |] ==> R"
apply (simp add: cspF_cspT_semantics)
apply (elim conjE exE)
apply (erule cspT_Rep_int_choice_rightE)

apply (simp add: subsetF_iff)
apply (simp add: in_failures)
apply (force)
done

lemma cspF_Rep_int_choice_f_rightE:
  "[| P <=F[M1,M2] !<f> :X .. Qf ; inj f ;
      [| ALL a:X. P <=F[M1,M2] Qf a |] ==> R
   |] ==> R"
apply (simp add: cspF_cspT_semantics)
apply (elim conjE exE)
apply (erule cspT_Rep_int_choice_rightE)
apply (simp)

apply (simp add: subsetF_iff)
apply (simp add: in_failures)
apply (force)
done

lemmas cspF_Rep_int_choice_rightE =
       cspF_Rep_int_choice_nat_rightE
       cspF_Rep_int_choice_set_rightE
       cspF_Rep_int_choice_com_rightE
       cspF_Rep_int_choice_f_rightE

(*-------------------------------------------------------*
 |             decomposition with subset                 |
 *-------------------------------------------------------*)

lemma cspF_Rep_int_choice_nat_subset:
  "[| N2 <= N1  ; !!n. n:N2 ==> Pf n <=F[M1,M2] Qf n |]
                    ==> !nat :N1 .. Pf <=F[M1,M2] !nat :N2 .. Qf"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_subset)
apply (rule, simp add: in_failures)
apply (force)
done

lemma cspF_Rep_int_choice_set_subset:
  "[| Ys <= Xs  ; !!X. X:Ys ==> Pf X <=F[M1,M2] Qf X |]
                    ==> !set :Xs .. Pf <=F[M1,M2] !set :Ys .. Qf"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_subset)
apply (rule, simp add: in_failures)
apply (force)
done

lemma cspF_Rep_int_choice_com_subset:
  "[| Y <= X  ; !!a. a:Y ==> Pf a <=F[M1,M2] Qf a |]
                    ==> ! :X .. Pf <=F[M1,M2] ! :Y .. Qf"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_subset)
apply (rule, simp add: in_failures)
apply (force)
done

lemma cspF_Rep_int_choice_f_subset:
  "[| inj f ; Y <= X  ; !!a. a:Y ==> Pf a <=F[M1,M2] Qf a |]
                    ==> !<f> :X .. Pf <=F[M1,M2] !<f> :Y .. Qf"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_subset)
apply (rule, simp add: in_failures)
apply (force)
done

lemmas cspF_Rep_int_choice_subset 
     = cspF_Rep_int_choice_nat_subset
       cspF_Rep_int_choice_set_subset
       cspF_Rep_int_choice_com_subset
       cspF_Rep_int_choice_f_subset

(*** ! x:X .. and ? -> ***)

lemma cspF_Int_Ext_pre_choice_subset:
  "[| Y ~={} ; Y <= X ; !!a. a:Y ==> Pf a <=F[M1,M2] Qf a |]
        ==> ! x:X .. (x -> Pf x) <=F[M1,M2]
            ? :Y -> Qf"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Int_Ext_pre_choice_subset)
apply (rule, simp add: in_failures)
apply (force)
done

lemmas cspF_decompo_subset = cspF_Rep_int_choice_subset
                             cspF_Int_Ext_pre_choice_subset

(*-------------------------------------------------------*
 |               decompose external choice               |
 *-------------------------------------------------------*)

lemma cspF_Ext_choice_right:
  "[| P <=F[M1,M2] Q1 ;
      P <=F[M1,M2] Q2 |]
      ==> P <=F[M1,M2] Q1 [+] Q2"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Ext_choice_right)
apply (rule)

 apply (simp add: in_failures)
 apply (elim disjE conjE exE, simp)
 apply (force, force, force)
 apply (simp_all)

 apply (subgoal_tac "(<>, X) :f failures(Q1) M2")
 apply (force)
 apply (rule proc_F2_F4)
 apply (simp_all)
 apply (rule proc_F2_F4)
 apply (simp_all)
 apply (simp add: cspT_semantics)
 apply (auto)
done

end
