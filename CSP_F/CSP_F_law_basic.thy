           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                January 2006  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_law_basic
imports CSP_F_law_decompo CSP_T.CSP_T_law_basic
begin

(*****************************************************************

         1. Commutativity
         2. Associativity
         3. Idempotence
         4. Left Commutativity
         5. IF

 *****************************************************************)

(*********************************************************
                       IF bool
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_IF_split: 
  "IF b THEN P ELSE Q =F[M,M] (if b then P else Q)"
apply (simp add: cspF_semantics)
apply (simp add: traces_iff)
apply (simp add: failures_iff)
done

lemma cspF_IF_True:
  "IF True THEN P ELSE Q =F[M,M] P"
apply (rule cspF_rw_left)
apply (rule cspF_IF_split)
by (simp)

lemma cspF_IF_False:
  "IF False THEN P ELSE Q =F[M,M] Q"
apply (rule cspF_rw_left)
apply (rule cspF_IF_split)
by (simp)

lemmas cspF_IF = cspF_IF_True cspF_IF_False

(*-----------------------------------*
 |           Idempotence             |
 *-----------------------------------*)

lemma cspF_Ext_choice_idem: 
  "P [+] P =F[M,M] P"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Ext_choice_idem)
apply (rule order_antisym)
 apply (rule, simp add: in_traces in_failures)
 apply (elim conjE disjE)
 apply (simp_all)
 apply (rule proc_F2_F4)
 apply (simp_all)
 apply (rule, simp add: in_traces in_failures)
done

lemma cspF_Int_choice_idem: 
  "P |~| P =F[M,M] P"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Int_choice_idem)
apply (rule order_antisym)
 apply (rule, simp add: in_failures)+
done

(*------------------*
 |      csp law     |
 *------------------*)

lemmas cspF_idem = cspF_Ext_choice_idem cspF_Int_choice_idem

(*-----------------------------------*
 |          Commutativity            |
 *-----------------------------------*)

(*********************************************************
                      Ext choice
 *********************************************************)

lemma cspF_Ext_choice_commut:
  "P [+] Q =F[M,M] Q [+] P"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Ext_choice_commut)

apply (rule order_antisym)
apply (rule, simp add: in_failures, fast)+
done

(*********************************************************
                      Int choice
 *********************************************************)

lemma cspF_Int_choice_commut:
  "P |~| Q =F[M,M] Q |~| P"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Int_choice_commut)
apply (rule order_antisym)
apply (rule, simp add: in_failures, fast)+
done

(*********************************************************
                      Parallel
 *********************************************************)

lemma cspF_Parallel_commut:
  "P |[X]| Q =F[M,M] Q |[X]| P"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Parallel_commut)
apply (rule order_antisym)

apply (rule, simp add: in_failures)
apply (elim conjE exE)
apply (rule_tac x="Z" in exI)
apply (rule_tac x="Y" in exI, simp)
apply (rule conjI, fast)
apply (rule_tac x="t" in exI)
apply (rule_tac x="sa" in exI)
apply (simp add: par_tr_sym)

apply (rule, simp add: in_failures)
apply (elim conjE exE)
apply (rule_tac x="Z" in exI)
apply (rule_tac x="Y" in exI, simp)
apply (rule conjI, fast)
apply (rule_tac x="t" in exI)
apply (rule_tac x="sa" in exI)
apply (simp add: par_tr_sym)
done

(*------------------*
 |      csp law     |
 *------------------*)

lemmas cspF_commut = cspF_Ext_choice_commut cspF_Int_choice_commut cspF_Parallel_commut

(*-----------------------------------*
 |          Associativity            |
 *-----------------------------------*)

lemma cspF_Ext_choice_assoc:
  "P [+] (Q [+] R) =F[M,M] (P [+] Q) [+] R"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Ext_choice_assoc)
apply (rule order_antisym)
apply (rule, simp add: in_failures in_traces)
apply (force)
apply (rule, simp add: in_failures in_traces)
apply (force)
done

lemma cspF_Ext_choice_assoc_sym:
  "(P [+] Q) [+] R =F[M,M] P [+] (Q [+] R)"
apply (rule cspF_sym)
apply (simp add: cspF_Ext_choice_assoc)
done

lemma cspF_Int_choice_assoc:
  "P |~| (Q |~| R) =F[M,M] (P |~| Q) |~| R"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Int_choice_assoc)
apply (rule order_antisym)
apply (rule, simp add: in_failures)+
done

lemma cspF_Int_choice_assoc_sym:
  "(P |~| Q) |~| R =F[M,M] P |~| (Q |~| R)"
apply (rule cspF_sym)
apply (simp add: cspF_Int_choice_assoc)
done

(*------------------*
 |      csp law     |
 *------------------*)

lemmas cspF_assoc = cspF_Ext_choice_assoc cspF_Int_choice_assoc
lemmas cspF_assoc_sym = cspF_Ext_choice_assoc_sym cspF_Int_choice_assoc_sym

(*-----------------------------------*
 |        Left Commutativity         |
 *-----------------------------------*)

lemma cspF_Ext_choice_left_commut:
  "P [+] (Q [+] R) =F[M,M] Q [+] (P [+] R)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Ext_choice_left_commut)
apply (rule order_antisym)
apply (rule, simp add: in_failures in_traces)
apply (force)
apply (rule, simp add: in_failures in_traces)
apply (force)
done

lemma cspF_Int_choice_left_commut:
  "P |~| (Q |~| R) =F[M,M] Q |~| (P |~| R)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Int_choice_left_commut)
apply (rule order_antisym)
 apply (rule, simp add: in_failures)+
done

lemmas cspF_left_commut = 
       cspF_Ext_choice_left_commut cspF_Int_choice_left_commut

(*-----------------------------------*
 |              Unit                 |
 *-----------------------------------*)

(*** STOP [+] P ***)

lemma cspF_Ext_choice_unit_l: 
  "STOP [+] P =F[M,M] P"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Ext_choice_unit_l)
apply (rule order_antisym)
 apply (rule, simp add: in_traces in_failures)
 apply (elim conjE disjE)
 apply (simp_all)
 apply (rule proc_F2_F4)
 apply (simp_all)

 apply (rule, simp add: in_failures)
done

lemma cspF_Ext_choice_unit_r: 
  "P [+] STOP =F[M,M] P"
apply (rule cspF_rw_left)
apply (rule cspF_Ext_choice_commut)
apply (simp add: cspF_Ext_choice_unit_l)
done

lemmas cspF_Ext_choice_unit = 
       cspF_Ext_choice_unit_l cspF_Ext_choice_unit_r

lemma cspF_Int_choice_unit_l: 
  "DIV |~| P =F[M,M] P"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Int_choice_unit_l)
apply (rule order_antisym)
 apply (rule, simp add: in_failures)
 apply (rule, simp add: in_failures)
done

lemma cspF_Int_choice_unit_r: 
  "P |~| DIV =F[M,M] P"
apply (rule cspF_rw_left)
apply (rule cspF_Int_choice_commut)
apply (simp add: cspF_Int_choice_unit_l)
done

lemmas cspF_Int_choice_unit = 
       cspF_Int_choice_unit_l cspF_Int_choice_unit_r

lemmas cspF_unit = cspF_Ext_choice_unit cspF_Int_choice_unit

(*-----------------------------------*
 |           !!-empty                |
 *-----------------------------------*)

lemma cspF_Rep_int_choice_sum_DIV:
   "sumset C = {} ==> !! : C .. Pf =F[M1,M2] DIV"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_DIV)
apply (simp add: failures_iff)
apply (simp add: empF_def)
done

lemma cspF_Rep_int_choice_nat_DIV:
   "!nat :{} .. Pf =F[M1,M2] DIV"
by (simp add: Rep_int_choice_ss_def cspF_Rep_int_choice_sum_DIV)

lemma cspF_Rep_int_choice_set_DIV:
   "!set :{} .. Pf =F[M1,M2] DIV"
by (simp add: Rep_int_choice_ss_def cspF_Rep_int_choice_sum_DIV)

lemma cspF_Rep_int_choice_com_DIV:
   "! :{} .. Pf =F[M1,M2] DIV"
by (simp add: Rep_int_choice_com_def cspF_Rep_int_choice_set_DIV)

lemma cspF_Rep_int_choice_f_DIV:
   "inj f ==> !<f> :{} .. Pf =F[M1,M2] DIV"
by (simp add: Rep_int_choice_f_def cspF_Rep_int_choice_com_DIV)

lemmas cspF_Rep_int_choice_DIV = cspF_Rep_int_choice_sum_DIV
                                 cspF_Rep_int_choice_nat_DIV
                                 cspF_Rep_int_choice_set_DIV
                                 cspF_Rep_int_choice_com_DIV
                                 cspF_Rep_int_choice_f_DIV

lemmas cspF_Rep_int_choice_DIV_sym = cspF_Rep_int_choice_DIV[THEN cspF_sym]
lemmas cspF_Rep_int_choice_empty = cspF_Rep_int_choice_DIV

lemma cspF_DIV_top: "P <=F DIV"
apply (simp add: cspF_semantics)
apply (simp add: traces_iff failures_iff)
done

(*-----------------------------------*
 |             !!-unit               |
 *-----------------------------------*)

lemma cspF_Rep_int_choice_sum_unit:
  "sumset C ~= {} ==> !! c:C .. P =F[M,M] P"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_unit)
apply (rule order_antisym)
 apply (rule, simp add: in_failures)
 apply (rule, simp add: in_failures)
 apply (force)
done

lemma cspF_Rep_int_choice_nat_unit:
  "N ~= {} ==> !nat n:N .. P =F[M,M] P"
by (simp add: Rep_int_choice_ss_def cspF_Rep_int_choice_sum_unit)

lemma cspF_Rep_int_choice_set_unit:
  "Xs ~= {} ==> !set X:Xs .. P =F[M,M] P"
by (simp add: Rep_int_choice_ss_def cspF_Rep_int_choice_sum_unit)

lemma cspF_Rep_int_choice_com_unit:
  "X ~= {} ==> ! a:X .. P =F[M,M] P"
by (simp add: Rep_int_choice_com_def cspF_Rep_int_choice_set_unit)

lemma cspF_Rep_int_choice_f_unit:
  "X ~= {} ==> !<f> a:X .. P =F[M,M] P"
by (simp add: Rep_int_choice_f_def cspF_Rep_int_choice_com_unit)

lemmas cspF_Rep_int_choice_unit = 
       cspF_Rep_int_choice_sum_unit
       cspF_Rep_int_choice_nat_unit
       cspF_Rep_int_choice_set_unit
       cspF_Rep_int_choice_com_unit
       cspF_Rep_int_choice_f_unit

(*-----------------------------------*
 |             !!-const              |
 *-----------------------------------*)

(* const *)

lemma cspF_Rep_int_choice_sum_const:
  "[| sumset C ~= {} ; ALL c: sumset C. Pf c = P |] ==> !! :C .. Pf =F[M,M] P"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_const)
apply (rule order_antisym)
 apply (rule, simp add: in_failures)
 apply (rule, simp add: in_failures)
 apply (force)
done

lemma cspF_Rep_int_choice_nat_const:
  "[| N ~= {} ; ALL n:N. Pf n = P |] ==> !nat :N .. Pf =F[M,M] P"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_Rep_int_choice_sum_const, auto)

lemma cspF_Rep_int_choice_set_const:
  "[| Xs ~= {} ; ALL X:Xs. Pf X = P |] ==> !set :Xs .. Pf =F[M,M] P"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_Rep_int_choice_sum_const, auto)

lemma cspF_Rep_int_choice_com_const:
  "[| X ~= {} ; ALL a:X. Pf a = P |] ==> ! :X .. Pf =F[M,M] P"
apply (simp add: Rep_int_choice_com_def)
by (rule cspF_Rep_int_choice_set_const, auto)

lemma cspF_Rep_int_choice_f_const:
  "[| inj f ; X ~= {} ; ALL a:X. Pf a = P |] ==> !<f> :X .. Pf =F[M,M] P"
apply (simp add: Rep_int_choice_f_def)
by (rule cspF_Rep_int_choice_com_const, auto)

lemmas cspF_Rep_int_choice_const =
       cspF_Rep_int_choice_sum_const
       cspF_Rep_int_choice_nat_const
       cspF_Rep_int_choice_set_const
       cspF_Rep_int_choice_com_const
       cspF_Rep_int_choice_f_const

(*-----------------------------------*
 |           |~|-!!-union            |
 *-----------------------------------*)

lemma cspF_Int_Rep_int_choice_sum_union:
  "C1 =type= C2 ==>
   (!! :C1 .. P1f) |~| (!! :C2 .. P2f)
   =F[M,M] (!! c:(C1 Uns C2) ..
          IF (c : sumset C1 & c : sumset C2) THEN (P1f c |~| P2f c)
          ELSE IF (c : sumset C1) THEN P1f c ELSE P2f c)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Int_Rep_int_choice_union)
apply (rule order_antisym)

 apply (rule)
 apply (simp add: in_failures)
 apply (elim conjE bexE disjE)
  apply (rule_tac x="c" in bexI)
  apply (simp)
  apply (simp)
  apply (rule_tac x="c" in bexI)
  apply (simp)
  apply (simp)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim conjE exE bexE)
 apply (simp_all)
 apply (elim disjE)
 apply (simp_all)
 apply (case_tac "c : sumset C2")
 apply (simp add: in_failures)
 apply (force)
 apply (simp add: in_failures)
 apply (force)
 apply (case_tac "c : sumset C1")
 apply (simp add: in_failures)
 apply (force)
 apply (simp add: in_failures)
 apply (force)
done

lemma cspF_Int_Rep_int_choice_nat_union:
  "(!nat :N1 .. P1f) |~| (!nat :N2 .. P2f)
   =F[M,M] (!nat n:(N1 Un N2) ..
          IF (n : N1 & n : N2) THEN (P1f n |~| P2f n)
          ELSE IF (n : N1) THEN P1f n ELSE P2f n)"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspF_rw_left)
apply (rule cspF_Int_Rep_int_choice_sum_union)
apply (simp_all)
apply (rule cspF_decompo)
by (auto)

lemma cspF_Int_Rep_int_choice_set_union:
  "(!set :Xs1 .. P1f) |~| (!set :Xs2 .. P2f)
   =F[M,M] (!set X:(Xs1 Un Xs2) ..
          IF (X : Xs1 & X : Xs2) THEN (P1f X |~| P2f X)
          ELSE IF (X : Xs1) THEN P1f X ELSE P2f X)"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspF_rw_left)
apply (rule cspF_Int_Rep_int_choice_sum_union)
apply (simp_all)
apply (rule cspF_decompo)
by (auto)

lemma cspF_Int_Rep_int_choice_com_union:
  "(! :X1 .. P1f) |~| (! :X2 .. P2f)
   =F[M,M] (! a:(X1 Un X2) ..
          IF (a : X1 & a : X2) THEN (P1f a |~| P2f a)
          ELSE IF (a : X1) THEN P1f a ELSE P2f a)"
apply (simp add: Rep_int_choice_com_def)
apply (rule cspF_rw_left)
apply (rule cspF_Int_Rep_int_choice_set_union)
apply (simp_all)
apply (rule cspF_decompo)
by (auto)

lemma cspF_Int_Rep_int_choice_f_union:
  "inj f ==>
  (!<f> :X1 .. P1f) |~| (!<f> :X2 .. P2f)
   =F[M,M] (!<f> a:(X1 Un X2) ..
          IF (a : X1 & a : X2) THEN (P1f a |~| P2f a)
          ELSE IF (a : X1) THEN P1f a ELSE P2f a)"
apply (simp add: Rep_int_choice_f_def)
apply (rule cspF_rw_left)
apply (rule cspF_Int_Rep_int_choice_com_union)
apply (rule cspF_decompo)
apply (auto simp add: inj_image_mem_iff)
done

lemmas cspF_Int_Rep_int_choice_union =
       cspF_Int_Rep_int_choice_sum_union
       cspF_Int_Rep_int_choice_nat_union
       cspF_Int_Rep_int_choice_set_union
       cspF_Int_Rep_int_choice_com_union
       cspF_Int_Rep_int_choice_f_union

(*-----------------------------------*
 |           !!-union-|~|            |
 *-----------------------------------*)

lemma cspF_Rep_int_choice_sum_union_Int:
  "C1 =type= C2 ==>
  (!! :(C1 Uns C2) .. Pf)
   =F[M,M] (!! c:C1 .. Pf c) |~| (!! c:C2 .. Pf c)"
apply (rule cspF_rw_right)
apply (rule cspF_Int_Rep_int_choice_union)
apply (simp)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_IF_split)
apply (simp)
apply (simp add: cspF_idem[THEN cspF_sym])
apply (intro impI)
apply (rule cspF_rw_right)
apply (rule cspF_IF_split)
apply (simp)
done

lemma cspF_Rep_int_choice_nat_union_Int:
  "(!nat :(N1 Un N2) .. Pf)
   =F[M,M] (!nat n:N1 .. Pf n) |~| (!nat n:N2 .. Pf n)"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspF_rw_right)
apply (rule cspF_Rep_int_choice_sum_union_Int[THEN cspF_sym])
apply (simp_all)
done

lemma cspF_Rep_int_choice_set_union_Int:
  "(!set :(Xs1 Un Xs2) .. Pf)
   =F[M,M] (!set X:Xs1 .. Pf X) |~| (!set X:Xs2 .. Pf X)"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspF_rw_right)
apply (rule cspF_Rep_int_choice_sum_union_Int[THEN cspF_sym])
apply (simp_all)
done

lemma cspF_Rep_int_choice_com_union_Int:
  "(! :(X1 Un X2) .. Pf)
   =F[M,M] (! a:X1 .. Pf a) |~| (! a:X2 .. Pf a)"
apply (simp add: Rep_int_choice_com_def)
apply (rule cspF_rw_right)
apply (rule cspF_Rep_int_choice_set_union_Int[THEN cspF_sym])
apply (rule cspF_decompo)
apply (auto)
done

lemma cspF_Rep_int_choice_f_union_Int:
  "(!<f> :(X1 Un X2) .. Pf)
   =F[M,M] (!<f> x:X1 .. Pf x) |~| (!<f> x:X2 .. Pf x)"
apply (simp add: Rep_int_choice_f_def)
apply (rule cspF_rw_right)
apply (rule cspF_Rep_int_choice_com_union_Int[THEN cspF_sym])
apply (rule cspF_decompo)
apply (auto)
done

lemmas cspF_Rep_int_choice_union_Int =
       cspF_Rep_int_choice_sum_union_Int
       cspF_Rep_int_choice_nat_union_Int
       cspF_Rep_int_choice_set_union_Int
       cspF_Rep_int_choice_com_union_Int
       cspF_Rep_int_choice_f_union_Int

(*********************************************************
                     Depth_rest
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Depth_rest_Zero:
  "P |. 0 =F[M1,M2] DIV"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Depth_rest_Zero)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (force)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
done

lemma cspF_Depth_rest_min:
  "P |. n |. m =F[M,M] P |. min n m"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Depth_rest_min)
apply (simp add: failures.simps)
apply (simp add: min_rs)
done

lemma cspF_Depth_rest_congE:
  "[| P =F[M1,M2] Q ; ALL m. P |. m =F[M1,M2] Q |. m ==> S |] ==> S"
apply (simp add: cspF_semantics)
apply (simp add: traces.simps)
apply (simp add: failures.simps)
done

lemma cspF_Depth_rest_n:
  "P |. n |. n =F[M,M] P |. n"
apply (rule cspF_rw_left)
apply (rule cspF_Depth_rest_min)
apply (simp)
done

(*------------------*
 |     !nat-rest    |
 *------------------*)

lemma cspF_nat_Depth_rest_UNIV: 
  "P =F[M,M] !nat n .. (P |. n)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_nat_Depth_rest_UNIV)
apply (rule order_antisym)

 (* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (case_tac "noTick s")

  apply (rule_tac x="Suc (lengtht s)" in exI)
  apply (simp)

  apply (rule_tac x="lengtht s" in exI)
  apply (simp)
  apply (rule_tac x="(butlastt s)" in exI)
  apply (simp add: Tick_decompo)
  apply (simp add: noTick_butlast)

 (* => *)
 apply (rule)
 apply (simp add: in_failures)
done

lemma cspF_nat_Depth_rest_lengthset:
   "P =F[M,M] !nat n:(lengthset P (fstF o M)) .. (P |. n)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_nat_Depth_rest_lengthset)
apply (rule order_antisym)

 (* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (case_tac "noTick s")

  apply (rule_tac x="Suc (lengtht s)" in bexI)
  apply (simp)
  apply (simp add: lengthset_def)
  apply (rule_tac x="s" in exI)
  apply (simp add: proc_T2)

  apply (rule_tac x="lengtht s" in bexI)
  apply (simp)
  apply (rule_tac x="(butlastt s)" in exI)
  apply (simp add: Tick_decompo)
  apply (simp add: noTick_butlast)
  apply (simp add: lengthset_def)
  apply (rule_tac x="s" in exI)
  apply (simp add: proc_T2)

 (* => *)
 apply (rule)
 apply (simp add: in_failures)
done

lemmas cspF_nat_Depth_rest = cspF_nat_Depth_rest_UNIV
                             cspF_nat_Depth_rest_lengthset

(*------------------*
 |    ?-partial     |
 *------------------*)

lemma cspF_Ext_pre_choice_partial:
  "? :X -> Pf =F[M,M] ? x:X -> (IF (x:X) THEN Pf x ELSE DIV)"
apply (rule cspF_decompo)
apply (simp_all)
apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (simp)
done

(*------------------*
 |   !!-partial     |
 *------------------*)

lemma cspF_Rep_int_choice_sum_partial:
  "!! :C .. Pf =F[M,M] !! c:C .. (IF (c: sumset C) THEN Pf c ELSE DIV)"
apply (rule cspF_decompo)
apply (simp_all)
apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (simp)
done

lemma cspF_Rep_int_choice_nat_partial:
  "!nat :N .. Pf =F[M,M] !nat n:N .. (IF (n:N) THEN Pf n ELSE DIV)"
apply (rule cspF_decompo)
apply (simp_all)
apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (simp)
done

lemma cspF_Rep_int_choice_set_partial:
  "!set :Xs .. Pf =F[M,M] !set X:Xs .. (IF (X:Xs) THEN Pf X ELSE DIV)"
apply (rule cspF_decompo)
apply (simp_all)
apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (simp)
done

lemma cspF_Rep_int_choice_com_partial:
  "! :X .. Pf =F[M,M] ! a:X .. (IF (a:X) THEN Pf a ELSE DIV)"
apply (rule cspF_decompo)
apply (simp_all)
apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (simp)
done

lemma cspF_Rep_int_choice_f_partial:
  "inj f ==> !<f> :X .. Pf =F[M,M] !<f> a:X .. (IF (a:X) THEN Pf a ELSE DIV)"
apply (rule cspF_decompo)
apply (simp_all)
apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (simp)
done

lemmas cspF_Rep_int_choice_partial =
       cspF_Rep_int_choice_sum_partial
       cspF_Rep_int_choice_nat_partial
       cspF_Rep_int_choice_set_partial
       cspF_Rep_int_choice_com_partial
       cspF_Rep_int_choice_f_partial


(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)

(* --------------------------------------------------- *
       unfold only the first Sending and Receiving
 * --------------------------------------------------- *)

lemma cspF_first_Send_prefix:
  "a ! v -> P =F[M,M] a v -> P"
by (simp add: csp_prefix_ss_def)

lemma cspF_first_Rec_prefix:
  "a ? x:X -> Pf x =F[M,M] ? : (a ` X) -> (%x. (Pf ((inv a) x)))"
by (simp add: csp_prefix_ss_def)

lemma cspF_first_Int_pre_choice:
  "! :X -> Pf =F[M,M]  ! :X .. (%x. x -> (Pf x))"
by (simp add: csp_prefix_ss_def)

lemma cspF_first_Nondet_send_prefix:
  "a !? x:X -> Pf x =F[M,M] ! :(a ` X) -> (%x. (Pf ((inv a) x)))"
by (simp add: csp_prefix_ss_def)

lemmas cspF_first_prefix_ss =
       cspF_first_Send_prefix
       cspF_first_Rec_prefix
       cspF_first_Int_pre_choice
       cspF_first_Nondet_send_prefix

(* --------------------------------------------------- *
      Associativity of Sequential composition
 * --------------------------------------------------- *)

lemma cspF_Seq_compo_assoc:
  "(P ;; Q) ;; R =F[M,M] P ;; (Q ;; R)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Seq_compo_assoc)
apply (rule order_antisym)

 apply (rule)
 apply (simp add: in_traces in_failures)
 apply (elim disjE conjE exE)
  apply (force)

  apply (rule disjI2)
  apply (simp)
  apply (rule_tac x="sa" in exI)
  apply (rule_tac x="t" in exI)
  apply (simp)

  apply (subgoal_tac "noTick (sa ^^^ <Tick>)")
  apply (rotate_tac 3)
  apply (erule rem_asmE)
  apply (simp)
  apply (simp)

  apply (simp)
  apply (rule disjI2)
  apply (simp add: appt_decompo)
  apply (elim disjE conjE exE)

   apply (simp)
   apply (elim disjE conjE exE)
   apply (simp)
   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="t" in exI)
   apply (simp)
   apply (rule disjI2)
   apply (rule_tac x="<>" in exI)
   apply (rule_tac x="t" in exI)
   apply (simp)

   apply (simp)
   apply (rotate_tac -2)
   apply (drule sym)
   apply (simp)
   apply (rotate_tac -2)
   apply (drule sym)
   apply (simp)

   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="u ^^^ t" in exI)
   apply (simp add: appt_assoc)
   apply (rule disjI2)
   apply (rule_tac x="u" in exI)
   apply (rule_tac x="t" in exI)
   apply (simp)

(* => *)
 apply (rule)
 apply (simp add: in_traces in_failures)
 apply (elim disjE conjE exE)

  apply (simp)

  apply (rule disjI1)
  apply (simp)
  apply (rule disjI2)
  apply (rule_tac x="sa" in exI)
  apply (rule_tac x="t" in exI)
  apply (simp)

  apply (rule disjI2)
  apply (rule_tac x="sa ^^^ sb" in exI)
  apply (rule_tac x="ta" in exI)
  apply (simp add: appt_assoc)
  apply (rule disjI2)
  apply (rule_tac x="sa" in exI)
  apply (rule_tac x="sb ^^^ <Tick>" in exI)
  apply (simp)
done

lemma cspF_Seq_compo_assoc_sym:
  "P ;; (Q ;; R) =F[M,M] (P ;; Q) ;; R"
apply (rule cspF_sym)
apply (simp add: cspF_Seq_compo_assoc)
done

(* ---------------------------------------------- *
         decompose right internal choice
 * ---------------------------------------------- *)

lemma cspF_Int_choice_eq_right:
  "[| P =F[M1,M2] Q1 ; P =F[M1,M2] Q2 |]
   ==> P =F[M1,M2] Q1 |~| Q2"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Int_choice_eq_right)
apply (rule order_antisym)
apply (rule)
apply (simp add: in_failures)
apply (rule)
apply (simp add: in_failures)
done

(* -------- right -------- *)

lemma cspF_Rep_int_choice_sum_eq_right_ALL:
  "[| sumset C ~= {} ; ALL c : (sumset C). P =F[M1,M2] Qf c |]
               ==> P =F[M1,M2] !! :C .. Qf"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_sum_eq_right_ALL)
apply (rule order_antisym)
apply (rule)
apply (simp add: in_failures)
apply (subgoal_tac "EX c. c: sumset C")
apply (erule exE)
apply (drule_tac x="c" in bspec, simp)
apply (erule conjE)
apply (erule order_antisymE)
apply (erule subsetFE_ALL)
apply (drule_tac x="s" in spec)
apply (drule_tac x="X" in spec)
apply (simp)
apply (fast)
apply (fast)

apply (rule)
apply (simp add: in_failures)
apply (erule bexE)
apply (drule_tac x="c" in bspec, simp)
apply (erule conjE)
apply (erule order_antisymE)
apply (rotate_tac -1)
apply (erule subsetFE_ALL)
apply (drule_tac x="s" in spec)
apply (drule_tac x="X" in spec)
apply (simp)
done

lemma cspF_Rep_int_choice_sum_eq_right:
  "[| sumset C ~= {} ; !! c. c : (sumset C) ==> P =F[M1,M2] Qf c |]
               ==> P =F[M1,M2] !! :C .. Qf"
by (simp add: cspF_Rep_int_choice_sum_eq_right_ALL)

(* nat *)

lemma cspF_Rep_int_choice_nat_eq_right:
  "[| N ~= {} ; !! n. n : N ==> P =F[M1,M2] Qf n |]
               ==> P =F[M1,M2] !nat :N .. Qf"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_Rep_int_choice_sum_eq_right, auto)

lemma cspF_Rep_int_choice_set_eq_right:
  "[| Xs ~= {} ; !! X. X : Xs ==> P =F[M1,M2] Qf X |]
               ==> P =F[M1,M2] !set :Xs .. Qf"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_Rep_int_choice_sum_eq_right, auto)

lemma cspF_Rep_int_choice_com_eq_right:
  "[| X ~= {} ; !! a. a:X ==> P =F[M1,M2] Qf a |]
               ==> P =F[M1,M2] ! :X .. Qf"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_Rep_int_choice_sum_eq_right, auto)

lemma cspF_Rep_int_choice_f_eq_right:
  "[| inj f ; X ~= {} ; !! a. a:X ==> P =F[M1,M2] Qf a |]
               ==> P =F[M1,M2] !<f> :X .. Qf"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_Rep_int_choice_sum_eq_right, auto)

lemmas cspF_int_eq_right =
       cspF_Rep_int_choice_sum_eq_right
       cspF_Rep_int_choice_nat_eq_right
       cspF_Rep_int_choice_set_eq_right
       cspF_Rep_int_choice_com_eq_right
       cspF_Rep_int_choice_f_eq_right
       cspF_Int_choice_eq_right

(* -------- left -------- *)

lemma cspF_Int_choice_eq_left:
  "[| Q1 =F[M1,M2] P ; Q2 =F[M1,M2] P |]
   ==> Q1 |~| Q2 =F[M1,M2] P"
apply (rule cspF_sym)
apply (rule cspF_int_eq_right)
apply (rule cspF_sym, simp)
apply (rule cspF_sym, simp)
done

lemma cspF_Rep_int_choice_sum_eq_left:
  "[| sumset C ~= {} ; !! c. c : (sumset C) ==> Qf c =F[M1,M2] P |]
               ==> !! :C .. Qf =F[M1,M2] P"
apply (rule cspF_sym, rule cspF_int_eq_right, simp)
apply (rule cspF_sym, simp)
done

lemma cspF_Rep_int_choice_nat_eq_left:
  "[| N ~= {} ; !! n. n : N ==> Qf n =F[M1,M2] P |]
               ==> !nat :N .. Qf =F[M1,M2] P"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_Rep_int_choice_sum_eq_left, auto)

lemma cspF_Rep_int_choice_set_eq_left:
  "[| Xs ~= {} ; !! X. X : Xs ==> Qf X =F[M1,M2] P |]
               ==> !set :Xs .. Qf =F[M1,M2] P"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_Rep_int_choice_sum_eq_left, auto)

lemma cspF_Rep_int_choice_com_eq_left:
  "[| X ~= {} ; !! a. a:X ==> Qf a =F[M1,M2] P |]
               ==> ! :X .. Qf =F[M1,M2] P"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_Rep_int_choice_sum_eq_left, auto)

lemma cspF_Rep_int_choice_f_eq_left:
  "[| inj f ; X ~= {} ; !! a. a:X ==> Qf a =F[M1,M2] P |]
               ==> !<f> :X .. Qf =F[M1,M2] P"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_Rep_int_choice_sum_eq_left, auto)

lemmas cspF_int_eq_left =
       cspF_Rep_int_choice_sum_eq_left
       cspF_Rep_int_choice_nat_eq_left
       cspF_Rep_int_choice_set_eq_left
       cspF_Rep_int_choice_com_eq_left
       cspF_Rep_int_choice_f_eq_left
       cspF_Int_choice_eq_left

(* ---------------------------------------------- *
      replicated internal choice -> binary ...
 * ---------------------------------------------- *)

(* ---- Un ---- *)

(* nat *)

lemma cspF_Rep_int_choice_nat_Un:
  "!nat n:(N1 Un N2) .. Pf n =F[M,M] !nat n:N1 .. Pf n |~| !nat n:N2 .. Pf n"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_nat_Un)
apply (rule order_antisym)
apply (auto simp add: in_failures)
done

(* set *)

lemma cspF_Rep_int_choice_set_Un:
  "!set X:(Xs1 Un Xs2) .. Pf X =F[M,M] !set X:Xs2 .. Pf X |~| !set X:Xs1 .. Pf X"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_set_Un)
apply (rule order_antisym)
apply (auto simp add: in_failures)
done

(* com *)

lemma cspF_Rep_int_choice_com_Un:
  "! x:(X1 Un X2) .. Pf x =F[M,M] ! x:X1 .. Pf x |~| ! x:X2 .. Pf x"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_com_Un)
apply (rule order_antisym)
apply (auto simp add: in_failures)
done

(* f *)

lemma cspF_Rep_int_choice_f_Un:
  "inj f ==> 
   !<f> x:(X1 Un X2) .. Pf x =F[M,M] !<f> x:X1 .. Pf x |~| !<f> x:X2 .. Pf x"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_f_Un)
apply (rule order_antisym)
apply (auto simp add: in_failures)
done

lemmas cspF_Rep_int_choice_Un =
       cspF_Rep_int_choice_nat_Un
       cspF_Rep_int_choice_set_Un
       cspF_Rep_int_choice_com_Un
       cspF_Rep_int_choice_f_Un

(* ---- insert ---- *)

(* nat *)

lemma cspF_Rep_int_choice_nat_insert:
  "!nat n:(insert m N) .. Pf n =F[M,M] Pf m |~| !nat n:N .. Pf n"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_nat_insert)
apply (rule order_antisym)
apply (auto simp add: in_failures)
done

(* set *)

lemma cspF_Rep_int_choice_set_insert:
  "!set X:(insert Y Xs) .. Pf X =F[M,M] Pf Y |~| !set X:Xs .. Pf X"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_set_insert)
apply (rule order_antisym)
apply (auto simp add: in_failures)
done

(* com *)

lemma cspF_Rep_int_choice_com_insert:
  "! x:(insert a X) .. Pf x =F[M,M] Pf a |~| ! x:X .. Pf x"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_com_insert)
apply (rule order_antisym)
apply (auto simp add: in_failures)
done

(* f *)

lemma cspF_Rep_int_choice_f_insert:
  "inj f ==> !<f> x:(insert a X) .. Pf x =F[M,M] Pf a |~| !<f> x:X .. Pf x"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_f_insert)
apply (rule order_antisym)
apply (auto simp add: in_failures)
done

lemmas cspF_Rep_int_choice_insert =
       cspF_Rep_int_choice_nat_insert
       cspF_Rep_int_choice_set_insert
       cspF_Rep_int_choice_com_insert
       cspF_Rep_int_choice_f_insert

lemmas cspF_Rep_int_choice_sepa =
       cspF_Rep_int_choice_insert
       cspF_Rep_int_choice_Un

(* ---------------------------------------------- *
       simplify replicated internal choice
 * ---------------------------------------------- *)

lemma cspF_Rep_int_choice_com_map_f:
  "inj f ==> ! x:(f ` X) .. Pf x =F[M,M] !<f> x:X .. Pf (f x)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_com_map_f)
apply (rule order_antisym)
apply (auto simp add: in_failures)
done

lemma cspF_Rep_int_choice_f_map_f:
  "[| inj f ; inj g |] ==> !<f> x:(g ` X) .. Pf x =F[M,M] !<f o g> x:X .. Pf (g x)"
apply (subgoal_tac "inj (f o g)")
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_f_map_f)
apply (rule order_antisym)
apply (auto simp add: in_failures)
apply (auto simp add: inj_on_def)
done

lemmas cspF_Rep_int_choice_f_map =
       cspF_Rep_int_choice_com_map_f
       cspF_Rep_int_choice_f_map_f

end
