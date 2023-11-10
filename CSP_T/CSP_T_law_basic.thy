           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
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

theory CSP_T_law_basic
imports CSP_T_law_decompo
begin

(*****************************************************************

         1. Commutativity
         2. Associativity
         3. Idempotence
         4. Left Commutativity
         5. IF

 *****************************************************************)

(*********************************************************
                          top
 *********************************************************)

lemma cspT_STOP_top: "P <=T STOP"
apply (simp add: cspT_semantics)
apply (simp add: traces_iff)
done

lemma cspT_DIV_top: "P <=T DIV"
apply (simp add: cspT_semantics)
apply (simp add: traces_iff)
done

lemmas cspT_top = cspT_STOP_top cspT_DIV_top

(*********************************************************
                       IF bool
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_IF_split: 
  "IF b THEN P ELSE Q =T[M,M] (if b then P else Q)"
apply (simp add: cspT_semantics)
apply (simp add: traces_iff)
done

lemma cspT_IF_True:
  "IF True THEN P ELSE Q =T[M,M] P"
apply (rule cspT_rw_left)
apply (rule cspT_IF_split)
by (simp)

lemma cspT_IF_False:
  "IF False THEN P ELSE Q =T[M,M] Q"
apply (rule cspT_rw_left)
apply (rule cspT_IF_split)
by (simp)

lemmas cspT_IF = cspT_IF_True cspT_IF_False

(*-----------------------------------*
 |           Idempotence             |
 *-----------------------------------*)

lemma cspT_Ext_choice_idem: 
  "P [+] P =T[M,M] P"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
 apply (rule, simp add: in_traces)+
done

lemma cspT_Int_choice_idem: 
  "P |~| P =T[M,M] P"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
 apply (rule, simp add: in_traces)+
done

(*------------------*
 |      csp law     |
 *------------------*)

lemmas cspT_idem = cspT_Ext_choice_idem cspT_Int_choice_idem

(*-----------------------------------*
 |          Commutativity            |
 *-----------------------------------*)

(*********************************************************
                      Ext choice
 *********************************************************)

lemma cspT_Ext_choice_commut:
  "P [+] Q =T[M,M] Q [+] P"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces, fast)+
done

(*********************************************************
                      Int choice
 *********************************************************)

lemma cspT_Int_choice_commut:
  "P |~| Q =T[M,M] Q |~| P"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces, fast)+
done

(*********************************************************
                      Parallel
 *********************************************************)

lemma cspT_Parallel_commut:
  "P |[X]| Q =T[M,M] Q |[X]| P"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

apply (rule, simp add: in_traces)
apply (elim conjE exE)
apply (rule_tac x="ta" in exI)
apply (rule_tac x="s" in exI)
apply (simp add: par_tr_sym)

apply (rule, simp add: in_traces)
apply (elim conjE exE)
apply (rule_tac x="ta" in exI)
apply (rule_tac x="s" in exI)
apply (simp add: par_tr_sym)
done

(*------------------*
 |      csp law     |
 *------------------*)

lemmas cspT_commut = cspT_Ext_choice_commut 
                      cspT_Int_choice_commut
                      cspT_Parallel_commut

(*-----------------------------------*
 |          Associativity            |
 *-----------------------------------*)

lemma cspT_Ext_choice_assoc:
  "P [+] (Q [+] R) =T[M,M] (P [+] Q) [+] R"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces)+
done

lemma cspT_Ext_choice_assoc_sym:
  "(P [+] Q) [+] R =T[M,M] P [+] (Q [+] R)"
apply (rule cspT_sym)
apply (simp add: cspT_Ext_choice_assoc)
done

lemma cspT_Int_choice_assoc:
  "P |~| (Q |~| R) =T[M,M] (P |~| Q) |~| R"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces)+
done

lemma cspT_Int_choice_assoc_sym:
  "(P |~| Q) |~| R =T[M,M] P |~| (Q |~| R)"
apply (rule cspT_sym)
apply (simp add: cspT_Int_choice_assoc)
done


(* --------------------------------------------------- *
              Associativity of Interleave
 * --------------------------------------------------- *)



lemma cspT_Interleave_assoc :
    "P ||| (Q ||| R) =T[M,M] (P ||| Q) ||| R"                 
  apply (simp add: cspT_semantics)
  apply (simp add: traces_iff)

  apply (simp add: CollectT_open_memT Parallel_domT)
  apply (rule CollectT_eq)

  apply (simp only: ex_simps[THEN sym] conj_assoc conj_left_commute)

  apply (rule sym, rule trans, rule ex_comm3, rule sym)
  apply (rule ex_cong1)
  apply (rule trans, rule ex_comm)
  apply (rule sym, rule trans, rule ex_comm3, rule sym)
  apply (rule ex_cong1)
  apply (rule trans, rule ex_comm)
  apply (rule sym, rule trans, rule ex_comm, rule sym)
  apply (rule ex_cong1)

  apply (simp only: ex_simps)
  apply (rule conj_cong, simp)+
  apply (simp only: conj_assoc[THEN sym])

  by (simp only: ex_simps inter_tr_assoc)


(*------------------*
 |      csp law     |
 *------------------*)

lemmas cspT_assoc = cspT_Ext_choice_assoc cspT_Int_choice_assoc
lemmas cspT_assoc_sym = cspT_Ext_choice_assoc_sym cspT_Int_choice_assoc_sym

(*-----------------------------------*
 |        Left Commutativity         |
 *-----------------------------------*)

lemma cspT_Ext_choice_left_commut:
  "P [+] (Q [+] R) =T[M,M] Q [+] (P [+] R)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces)+
done

lemma cspT_Int_choice_left_commut:
  "P |~| (Q |~| R) =T[M,M] Q |~| (P |~| R)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces)+
done

lemmas cspT_left_commut = 
       cspT_Ext_choice_left_commut cspT_Int_choice_left_commut



(*-----------------------------------*
 |     Interleave Commutativity      |
 *-----------------------------------*)

lemma cspT_Interleave_commute :
    "P ||| Q =T[M,M] Q ||| P"
  by (rule cspT_Parallel_commut)

lemma cspT_Interleave_left_commute :
    "P ||| (Q ||| R) =T[M,M] Q ||| (P ||| R)"
  apply (rule cspT_rw_left, rule cspT_Interleave_commute)
  apply (rule cspT_rw_left, rule cspT_Interleave_assoc[THEN cspT_sym])
  apply (rule cspT_decompo, simp_all, rule cspT_Interleave_commute)
  done



(*-----------------------------------*
 |              Unit                 |
 *-----------------------------------*)

(*** STOP [+] P ***)

lemma cspT_Ext_choice_unit_l: 
  "STOP [+] P =T[M,M] P"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
 apply (rule, simp add: in_traces)
 apply (force)
 apply (rule, simp add: in_traces)
done

lemma cspT_Ext_choice_unit_r: 
  "P [+] STOP =T[M,M] P"
apply (rule cspT_rw_left)
apply (rule cspT_Ext_choice_commut)
apply (simp add: cspT_Ext_choice_unit_l)
done

lemmas cspT_Ext_choice_unit = 
       cspT_Ext_choice_unit_l cspT_Ext_choice_unit_r

lemma cspT_Int_choice_unit_l: 
  "DIV |~| P =T[M,M] P"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
 apply (rule, simp add: in_traces)
 apply (force)
 apply (rule, simp add: in_traces)
done

lemma cspT_Int_choice_unit_r: 
  "P |~| DIV =T[M,M] P"
apply (rule cspT_rw_left)
apply (rule cspT_Int_choice_commut)
apply (simp add: cspT_Int_choice_unit_l)
done

lemmas cspT_Int_choice_unit = 
       cspT_Int_choice_unit_l cspT_Int_choice_unit_r

lemmas cspT_unit = cspT_Ext_choice_unit cspT_Int_choice_unit


(*-----------------------------------*
 |             guard proc            |
 *-----------------------------------*)

lemma cspT_guard_False [simp]:
    "False &: P =T[M,M] STOP"
  by (rule cspT_IF_False)

lemma cspT_guard_True [simp]:
    "True &: P =T[M,M] P"
  by (rule cspT_IF_True)

lemma cspT_Ext_choice_guard_IF :
    "g &: P [+] \<not> g &: Q =T[M,M] (IF g THEN P ELSE Q)"
  apply (case_tac g, auto)
  apply (rule cspT_rw_left, rule cspT_Ext_choice_cong)
  apply (rule cspT_IF, rule cspT_IF)
  apply (rule cspT_rw_right, rule cspT_IF)
  apply (rule cspT_rw_left, rule cspT_Ext_choice_unit)
  apply (rule cspT_reflex)
  apply (rule cspT_rw_left, rule cspT_Ext_choice_cong)
  apply (rule cspT_IF, rule cspT_IF)
  apply (rule cspT_rw_right, rule cspT_IF)
  apply (rule cspT_rw_left, rule cspT_Ext_choice_unit)
  apply (rule cspT_reflex)
  done


(*-----------------------------------*
 |             !-empty               |
 *-----------------------------------*)

lemma cspT_Rep_int_choice_sum_DIV:
   "sumset C = {} ==> !! : C .. Pf =T[M1,M2] DIV"
apply (simp add: cspT_semantics)
apply (simp add: traces_iff)
done

lemma cspT_Rep_int_choice_nat_DIV:
   "!nat :{} .. Pf =T[M1,M2] DIV"
by (simp add: Rep_int_choice_ss_def cspT_Rep_int_choice_sum_DIV)

lemma cspT_Rep_int_choice_set_DIV:
   "!set :{} .. Pf =T[M1,M2] DIV"
by (simp add: Rep_int_choice_ss_def cspT_Rep_int_choice_sum_DIV)

lemma cspT_Rep_int_choice_com_DIV:
   "! :{} .. Pf =T[M1,M2] DIV"
apply (simp add: Rep_int_choice_com_def)
apply (simp add: cspT_Rep_int_choice_set_DIV)
done

lemma cspT_Rep_int_choice_f_DIV:
   "inj f ==> !<f> :{} .. Pf =T[M1,M2] DIV"
apply (simp add: cspT_semantics)
apply (simp add: traces_iff)
done

lemmas cspT_Rep_int_choice_DIV = cspT_Rep_int_choice_sum_DIV
                                 cspT_Rep_int_choice_nat_DIV
                                 cspT_Rep_int_choice_set_DIV
                                 cspT_Rep_int_choice_com_DIV
                                 cspT_Rep_int_choice_f_DIV

lemmas cspT_Rep_int_choice_DIV_sym = cspT_Rep_int_choice_DIV[THEN cspT_sym]
lemmas cspT_Rep_int_choice_empty = cspT_Rep_int_choice_DIV

(*-----------------------------------*
 |             !-unit                |
 *-----------------------------------*)

lemma cspT_Rep_int_choice_sum_unit:
  "sumset C ~= {} ==> !! c:C .. P =T[M,M] P"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
 apply (rule)
 apply (simp only: in_traces)
 apply (force)
 apply (rule)
 apply (simp only: in_traces)
 apply (force)
done

lemma cspT_Rep_int_choice_nat_unit:
  "N ~= {} ==> !nat n:N .. P =T[M,M] P"
by (simp add: Rep_int_choice_ss_def cspT_Rep_int_choice_sum_unit)

lemma cspT_Rep_int_choice_set_unit:
  "Xs ~= {} ==> !set X:Xs .. P =T[M,M] P"
by (simp add: Rep_int_choice_ss_def cspT_Rep_int_choice_sum_unit)

lemma cspT_Rep_int_choice_com_unit:
  "X ~= {} ==> ! a:X .. P =T[M,M] P"
by (simp add: Rep_int_choice_com_def cspT_Rep_int_choice_set_unit)

lemma cspT_Rep_int_choice_f_unit:
  "X ~= {} ==> !<f> a:X .. P =T[M,M] P"
apply (simp add: Rep_int_choice_f_def)
apply (simp add: cspT_Rep_int_choice_com_unit)
done

lemmas cspT_Rep_int_choice_unit = 
       cspT_Rep_int_choice_sum_unit
       cspT_Rep_int_choice_nat_unit
       cspT_Rep_int_choice_set_unit
       cspT_Rep_int_choice_com_unit
       cspT_Rep_int_choice_f_unit

(*-----------------------------------*
 |              !-const              |
 *-----------------------------------*)

(* const *)

lemma cspT_Rep_int_choice_sum_const:
  "[| sumset C ~= {} ; ALL c: sumset C. Pf c = P |] ==> !! :C .. Pf =T[M,M] P"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
 apply (rule)
 apply (simp only: in_traces)
 apply (force)
 apply (rule)
 apply (simp only: in_traces)
 apply (force)
done

lemma cspT_Rep_int_choice_nat_const:
  "[| N ~= {} ; ALL n:N. Pf n = P |] ==> !nat :N .. Pf =T[M,M] P"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_Rep_int_choice_sum_const)
by (auto)

lemma cspT_Rep_int_choice_set_const:
  "[| Xs ~= {} ; ALL X:Xs. Pf X = P |] ==> !set :Xs .. Pf =T[M,M] P"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_Rep_int_choice_sum_const)
by (auto)

lemma cspT_Rep_int_choice_com_const:
  "[| X ~= {} ; ALL a:X. Pf a = P |] ==> ! :X .. Pf =T[M,M] P"
apply (simp add: Rep_int_choice_com_def)
apply (rule cspT_Rep_int_choice_set_const)
by (auto)

lemma cspT_Rep_int_choice_f_const:
  "[| inj f ; X ~= {} ; ALL a:X. Pf a = P |] ==> !<f> :X .. Pf =T[M,M] P"
apply (simp add: Rep_int_choice_f_def)
apply (rule cspT_Rep_int_choice_com_const)
by (auto)

lemmas cspT_Rep_int_choice_const =
       cspT_Rep_int_choice_sum_const
       cspT_Rep_int_choice_nat_const
       cspT_Rep_int_choice_set_const
       cspT_Rep_int_choice_com_const
       cspT_Rep_int_choice_f_const

(*-----------------------------------*
 |            |~|-!-union            |
 *-----------------------------------*)

lemma cspT_Int_Rep_int_choice_sum_union:
  "C1 =type= C2 ==>
   (!! :C1 .. P1f) |~| (!! :C2 .. P2f)
   =T[M,M] (!! c:(C1 Uns C2) ..
          IF (c : sumset C1 & c : sumset C2) THEN (P1f c |~| P2f c)
          ELSE IF (c : sumset C1) THEN P1f c ELSE P2f c)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE bexE disjE)
 apply (simp_all)
  apply (rule disjI2)
  apply (rule_tac x="c" in bexI)
  apply (simp add: in_traces)
  apply (simp)
  apply (rule disjI2)
  apply (rule_tac x="c" in bexI)
  apply (simp add: in_traces)
  apply (simp)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE bexE disjE)
 apply (simp_all)
 apply (elim conjE exE bexE disjE)
 apply (simp_all)
 apply (case_tac "c : sumset C2")
 apply (simp add: in_traces)
 apply (force)
 apply (simp add: in_traces)
 apply (force)
 apply (case_tac "c : sumset C1")
 apply (simp add: in_traces)
 apply (force)
 apply (simp add: in_traces)
 apply (force)
done

lemma cspT_Int_Rep_int_choice_nat_union:
  "(!nat :N1 .. P1f) |~| (!nat :N2 .. P2f)
   =T[M,M] (!nat n:(N1 Un N2) ..
          IF (n : N1 & n : N2) THEN (P1f n |~| P2f n)
          ELSE IF (n : N1) THEN P1f n ELSE P2f n)"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Int_Rep_int_choice_sum_union)
apply (simp_all)
apply (rule cspT_decompo)
by (auto)

lemma cspT_Int_Rep_int_choice_set_union:
  "(!set :Xs1 .. P1f) |~| (!set :Xs2 .. P2f)
   =T[M,M] (!set X:(Xs1 Un Xs2) ..
          IF (X : Xs1 & X : Xs2) THEN (P1f X |~| P2f X)
          ELSE IF (X : Xs1) THEN P1f X ELSE P2f X)"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Int_Rep_int_choice_sum_union)
apply (simp_all)
apply (rule cspT_decompo)
by (auto)

lemma cspT_Int_Rep_int_choice_com_union:
  "(! :X1 .. P1f) |~| (! :X2 .. P2f)
   =T[M,M] (! a:(X1 Un X2) ..
          IF (a : X1 & a : X2) THEN (P1f a |~| P2f a)
          ELSE IF (a : X1) THEN P1f a ELSE P2f a)"
apply (simp add: Rep_int_choice_com_def)
apply (rule cspT_rw_left)
apply (rule cspT_Int_Rep_int_choice_set_union)
apply (rule cspT_decompo)
by (auto)

lemma cspT_Int_Rep_int_choice_f_union:
  "inj f ==>
  (!<f> :X1 .. P1f) |~| (!<f> :X2 .. P2f)
   =T[M,M] (!<f> a:(X1 Un X2) ..
          IF (a : X1 & a : X2) THEN (P1f a |~| P2f a)
          ELSE IF (a : X1) THEN P1f a ELSE P2f a)"
apply (simp add: Rep_int_choice_f_def)
apply (rule cspT_rw_left)
apply (rule cspT_Int_Rep_int_choice_com_union)
apply (rule cspT_decompo)
apply (auto simp add: inj_image_mem_iff)
done

lemmas cspT_Int_Rep_int_choice_union =
       cspT_Int_Rep_int_choice_sum_union
       cspT_Int_Rep_int_choice_nat_union
       cspT_Int_Rep_int_choice_set_union
       cspT_Int_Rep_int_choice_com_union
       cspT_Int_Rep_int_choice_f_union

(*-----------------------------------*
 |           !!-union-|~|            |
 *-----------------------------------*)

lemma cspT_Rep_int_choice_sum_union_Int:
  "C1 =type= C2 ==>
  (!! :(C1 Uns C2) .. Pf)
   =T[M,M] (!! c:C1 .. Pf c) |~| (!! c:C2 .. Pf c)"
apply (rule cspT_rw_right)
apply (rule cspT_Int_Rep_int_choice_union)
apply (simp)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (simp)
apply (simp add: cspT_idem[THEN cspT_sym])
apply (intro impI)
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (simp)
done

lemma cspT_Rep_int_choice_nat_union_Int:
  "(!nat :(N1 Un N2) .. Pf)
   =T[M,M] (!nat n:N1 .. Pf n) |~| (!nat n:N2 .. Pf n)"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_rw_right)
apply (rule cspT_Rep_int_choice_sum_union_Int[THEN cspT_sym])
apply (simp_all)
done

lemma cspT_Rep_int_choice_set_union_Int:
  "(!set :(Xs1 Un Xs2) .. Pf)
   =T[M,M] (!set X:Xs1 .. Pf X) |~| (!set X:Xs2 .. Pf X)"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_rw_right)
apply (rule cspT_Rep_int_choice_sum_union_Int[THEN cspT_sym])
apply (simp_all)
done

lemma cspT_Rep_int_choice_com_union_Int:
  "(! :(X1 Un X2) .. Pf)
   =T[M,M] (! a:X1 .. Pf a) |~| (! a:X2 .. Pf a)"
apply (simp add: Rep_int_choice_com_def)
apply (rule cspT_rw_right)
apply (rule cspT_Rep_int_choice_set_union_Int[THEN cspT_sym])
apply (rule cspT_decompo)
apply (auto)
done

lemma cspT_Rep_int_choice_f_union_Int:
  "inj f ==>
   (!<f> :(X1 Un X2) .. Pf)
   =T[M,M] (!<f> a:X1 .. Pf a) |~| (!<f> a:X2 .. Pf a)"
apply (simp add: Rep_int_choice_f_def)
apply (rule cspT_rw_right)
apply (rule cspT_Rep_int_choice_com_union_Int[THEN cspT_sym])
apply (rule cspT_decompo)
apply (auto)
done

lemmas cspT_Rep_int_choice_union_Int =
       cspT_Rep_int_choice_sum_union_Int
       cspT_Rep_int_choice_nat_union_Int
       cspT_Rep_int_choice_set_union_Int
       cspT_Rep_int_choice_com_union_Int
       cspT_Rep_int_choice_f_union_Int

(*********************************************************
                     Depth_rest
 *********************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Depth_rest_Zero:
  "P |. 0 =T[M1,M2] DIV"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (simp add: lengtht_zero)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
done

lemma cspT_Depth_rest_min:
  "P |. n |. m =T[M,M] P |. min n m"
apply (simp add: cspT_semantics)
apply (simp add: traces.simps)
apply (simp add: min_rs)
done

lemma cspT_Depth_rest_congE:
  "[| P =T[M1,M2] Q ; ALL m. P |. m =T[M1,M2] Q |. m ==> S |] ==> S"
apply (simp add: cspT_semantics)
apply (simp add: traces.simps)
done

(*------------------*
 |     !nat-rest    |
 *------------------*)

lemma cspT_nat_Depth_rest_UNIV: 
  "P =T[M,M] !nat n .. (P |. n)"
apply (simp add: cspT_eqT_semantics)
apply (rule order_antisym)

 (* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (rule disjI2)
 apply (rule_tac x="lengtht t" in exI)
 apply (simp)

 (* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (erule disjE)
 apply (simp_all)
done

lemma cspT_nat_Depth_rest_lengthset: 
  "P =T[M,M] !nat n:(lengthset P M) .. (P |. n)"
apply (simp add: cspT_eqT_semantics)
apply (rule order_antisym)

 (* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (rule disjI2)
 apply (rule_tac x="lengtht t" in bexI)
 apply (simp)
 apply (simp add: lengthset_def)
 apply (rule_tac x="t" in exI)
 apply (simp)

 (* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (erule disjE)
 apply (simp_all)
done

lemmas cspT_nat_Depth_rest = cspT_nat_Depth_rest_UNIV
                             cspT_nat_Depth_rest_lengthset

(*------------------*
 |    ?-partial     |
 *------------------*)

lemma cspT_Ext_pre_choice_partial:
  "? :X -> Pf =T[M,M] ? x:X -> (IF (x:X) THEN Pf x ELSE DIV)"
apply (rule cspT_decompo)
apply (simp_all)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (simp)
done

(*------------------*
 |   !!-partial     |
 *------------------*)

lemma cspT_Rep_int_choice_sum_partial:
  "!! :C .. Pf =T[M,M] !! c:C .. (IF (c: sumset C) THEN Pf c ELSE DIV)"
apply (rule cspT_decompo)
apply (simp_all)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (simp)
done

lemma cspT_Rep_int_choice_nat_partial:
  "!nat :N .. Pf =T[M,M] !nat n:N .. (IF (n:N) THEN Pf n ELSE DIV)"
apply (rule cspT_decompo)
apply (simp_all)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (simp)
done

lemma cspT_Rep_int_choice_set_partial:
  "!set :Xs .. Pf =T[M,M] !set X:Xs .. (IF (X:Xs) THEN Pf X ELSE DIV)"
apply (rule cspT_decompo)
apply (simp_all)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (simp)
done

lemma cspT_Rep_int_choice_com_partial:
  "! :X .. Pf =T[M,M] ! a:X .. (IF (a:X) THEN Pf a ELSE DIV)"
apply (rule cspT_decompo)
apply (simp_all)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (simp)
done

lemma cspT_Rep_int_choice_f_partial:
  "inj f ==> !<f> :X .. Pf =T[M,M] !<f> a:X .. (IF (a:X) THEN Pf a ELSE DIV)"
apply (rule cspT_decompo)
apply (simp_all)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (simp)
done

lemmas cspT_Rep_int_choice_partial =
       cspT_Rep_int_choice_sum_partial
       cspT_Rep_int_choice_nat_partial
       cspT_Rep_int_choice_set_partial
       cspT_Rep_int_choice_com_partial
       cspT_Rep_int_choice_f_partial

(*********************************************************
                    Rep_int_choice
 *********************************************************)

lemma cspT_Rep_int_choice_sum_set:
  "!! : type1 Xs .. Pf =T[M,M] !set X: Xs .. Pf (type1 X)"
apply (simp add: _Rep_int_choice_ss_def)
apply (rule cspT_decompo)
apply (auto simp add: image_def)
done

lemma cspT_Rep_int_choice_sum_nat:
  "!! : type2 N .. Pf =T[M,M] !nat n: N .. Pf (type2 n)"
apply (simp add: _Rep_int_choice_ss_def)
apply (rule cspT_decompo)
apply (auto simp add: image_def)
done


lemma cspT_Rep_int_choice_sum:
  "!! :C .. Pf =T[M,M]
   IF type1? C
   THEN (!set X: open1 C .. Pf (type1 X))
   ELSE (!nat n: open2 C .. Pf (type2 n))"
apply (insert type1_or_type2)
apply (drule_tac x="C" in spec)
apply (elim disjE exE)
apply (simp_all)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (simp add: cspT_Rep_int_choice_sum_set)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (simp add: cspT_Rep_int_choice_sum_nat)
done

(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)

(* --------------------------------------------------- *
       unfold only the first Sending and Receiving
 * --------------------------------------------------- *)

lemma cspT_first_Send_prefix:
  "a ! v -> P =T[M,M] a v -> P"
by (simp add: csp_prefix_ss_def)

lemma cspT_first_Rec_prefix:
  "a ? x:X -> Pf x =T[M,M] ? : (a ` X) -> (%x. (Pf ((inv a) x)))"
by (simp add: csp_prefix_ss_def)

lemma cspT_first_Int_pre_choice:
  "! :X -> Pf =T[M,M]  ! :X .. (%x. x -> (Pf x))"
by (simp add: csp_prefix_ss_def)

lemma cspT_first_Nondet_send_prefix:
  "a !? x:X -> Pf x =T[M,M] ! :(a ` X) -> (%x. (Pf ((inv a) x)))"
by (simp add: csp_prefix_ss_def)

lemmas cspT_first_prefix_ss =
       cspT_first_Send_prefix
       cspT_first_Rec_prefix
       cspT_first_Int_pre_choice
       cspT_first_Nondet_send_prefix


lemma cspT_Rec_prefix_cong_right :
    "\<forall>x. Pf x =T[M1,M2] Qf x
     \<Longrightarrow> a ? u:T -> Pf u =T[M1,M2] a ? u:T -> Qf u"
  apply (rule cspT_rw_left, rule cspT_first_Rec_prefix)
  apply (rule cspT_rw_right, rule cspT_first_Rec_prefix)
  apply (simp only: image_def)
  apply (rule cspT_decompo, simp_all add: inv_def)
done


(* --------------------------------------------------- *
      Associativity of Sequential composition
 * --------------------------------------------------- *)

lemma cspT_Seq_compo_assoc:
  "(P ;; Q) ;; R =T[M,M] P ;; (Q ;; R)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE)
  apply (force)

  apply (rule disjI2)
  apply (rule_tac x="sa" in exI)
  apply (insert Trace.trace_last_noTick_or_Tick)
  apply (drule_tac x="ta" in spec)
  apply (elim disjE conjE exE)

   apply (rule_tac x="ta" in exI)
   apply (simp)
   apply (rule disjI1)
   apply (rule_tac x="ta" in exI)
   apply (simp)

   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (simp)
   apply (rule disjI2)
   apply (rule_tac x="sb" in exI)
   apply (rule_tac x="<>" in exI)
   apply (simp)

   apply (subgoal_tac "noTick (s ^^^ <Tick>)")
   apply (rotate_tac 3)
   apply (erule rem_asmE)
   apply (simp)
   apply (simp)

   apply (rule disjI2)
   apply (simp add: appt_decompo)
   apply (elim disjE conjE exE)

    apply (simp)
    apply (elim disjE conjE exE)
    apply (simp)
    apply (simp)
    apply (rule_tac x="sa" in exI)
    apply (rule_tac x="ta" in exI)
    apply (simp)
    apply (rule disjI2)
    apply (rule_tac x="<>" in exI)
    apply (rule_tac x="ta" in exI)
    apply (simp)

    apply (simp)
    apply (rotate_tac -2)
    apply (drule sym)
    apply (simp)
    apply (rotate_tac -2)
    apply (drule sym)
    apply (simp)

    apply (simp)
    apply (rule_tac x="sa" in exI)
    apply (rule_tac x="u ^^^ ta" in exI)
    apply (simp add: appt_assoc)
    apply (rule disjI2)
    apply (rule_tac x="u" in exI)
    apply (rule_tac x="ta" in exI)
    apply (simp)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE)

  apply (rule disjI1)
  apply (rule_tac x="t" in exI)
  apply (simp)
  apply (rule disjI1)
  apply (rule_tac x="s" in exI)
  apply (simp)

  apply (rule disjI1)
  apply (rule_tac x="s ^^^ ta" in exI)
  apply (simp)
  apply (rule disjI2)
  apply (rule_tac x="s" in exI)
  apply (rule_tac x="ta" in exI)
  apply (simp)
  apply (rule memT_prefix_closed)
  apply (simp)
  apply (simp)

  apply (rule disjI2)
  apply (rule_tac x="s ^^^ sa" in exI)
  apply (rule_tac x="tb" in exI)
  apply (simp add: appt_assoc)
  apply (rule disjI2)
  apply (rule_tac x="s" in exI)
  apply (rule_tac x="sa ^^^ <Tick>" in exI)
  apply (simp)
done


(* ---------------------------------------------- *
         decompose right internal choice
 * ---------------------------------------------- *)

lemma cspT_Int_choice_eq_right:
  "[| P =T[M1,M2] Q1 ; P =T[M1,M2] Q2 |]
   ==> P =T[M1,M2] Q1 |~| Q2"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule)
apply (simp add: in_traces)
apply (rule)
apply (simp add: in_traces)
done

(* -------- right -------- *)

lemma cspT_Rep_int_choice_sum_eq_right_ALL:
  "[| sumset C ~= {} ; ALL c : (sumset C). P =T[M1,M2] Qf c |]
               ==> P =T[M1,M2] !! :C .. Qf"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

apply (rule)
apply (simp add: in_traces)
apply (subgoal_tac "EX c. c: sumset C")
apply (erule exE)
apply (drule_tac x="c" in bspec, simp)
apply (erule order_antisymE)
apply (erule subdomTE_ALL)
apply (drule_tac x="t" in spec)
apply (fast)
apply (fast)

apply (rule)
apply (simp add: in_traces)
apply (erule disjE)
apply (simp)
apply (erule bexE)
apply (drule_tac x="c" in bspec, simp)
apply (erule order_antisymE)
apply (rotate_tac -1)
apply (erule subdomTE_ALL)
apply (drule_tac x="t" in spec)
apply (simp)
done

lemma cspT_Rep_int_choice_sum_eq_right:
  "[| sumset C ~= {} ; !! c. c : (sumset C) ==> P =T[M1,M2] Qf c |]
               ==> P =T[M1,M2] !! :C .. Qf"
by (simp add: cspT_Rep_int_choice_sum_eq_right_ALL)

(* nat *)

lemma cspT_Rep_int_choice_nat_eq_right:
  "[| N ~= {} ; !! n. n : N ==> P =T[M1,M2] Qf n |]
               ==> P =T[M1,M2] !nat :N .. Qf"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_Rep_int_choice_sum_eq_right, auto)

lemma cspT_Rep_int_choice_set_eq_right:
  "[| Xs ~= {} ; !! X. X : Xs ==> P =T[M1,M2] Qf X |]
               ==> P =T[M1,M2] !set :Xs .. Qf"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_Rep_int_choice_sum_eq_right, auto)

lemma cspT_Rep_int_choice_com_eq_right:
  "[| X ~= {} ; !! a. a:X ==> P =T[M1,M2] Qf a |]
               ==> P =T[M1,M2] ! :X .. Qf"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_Rep_int_choice_sum_eq_right, auto)

lemma cspT_Rep_int_choice_f_eq_right:
  "[| inj f ; X ~= {} ; !! a. a:X ==> P =T[M1,M2] Qf a |]
               ==> P =T[M1,M2] !<f> :X .. Qf"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_Rep_int_choice_sum_eq_right, auto)

lemmas cspT_int_eq_right =
       cspT_Rep_int_choice_sum_eq_right
       cspT_Rep_int_choice_nat_eq_right
       cspT_Rep_int_choice_set_eq_right
       cspT_Rep_int_choice_com_eq_right
       cspT_Rep_int_choice_f_eq_right
       cspT_Int_choice_eq_right

(* -------- left -------- *)

lemma cspT_Int_choice_eq_left:
  "[| Q1 =T[M1,M2] P ; Q2 =T[M1,M2] P |]
   ==> Q1 |~| Q2 =T[M1,M2] P"
apply (rule cspT_sym)
apply (rule cspT_int_eq_right)
apply (rule cspT_sym, simp)
apply (rule cspT_sym, simp)
done

lemma cspT_Rep_int_choice_sum_eq_left:
  "[| sumset C ~= {} ; !! c. c : (sumset C) ==> Qf c =T[M1,M2] P |]
               ==> !! :C .. Qf =T[M1,M2] P"
apply (rule cspT_sym, rule cspT_int_eq_right, simp)
apply (rule cspT_sym, simp)
done

lemma cspT_Rep_int_choice_nat_eq_left:
  "[| N ~= {} ; !! n. n : N ==> Qf n =T[M1,M2] P |]
               ==> !nat :N .. Qf =T[M1,M2] P"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_Rep_int_choice_sum_eq_left, auto)

lemma cspT_Rep_int_choice_set_eq_left:
  "[| Xs ~= {} ; !! X. X : Xs ==> Qf X =T[M1,M2] P |]
               ==> !set :Xs .. Qf =T[M1,M2] P"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_Rep_int_choice_sum_eq_left, auto)

lemma cspT_Rep_int_choice_com_eq_left:
  "[| X ~= {} ; !! a. a:X ==> Qf a =T[M1,M2] P |]
               ==> ! :X .. Qf =T[M1,M2] P"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_Rep_int_choice_sum_eq_left, auto)

lemma cspT_Rep_int_choice_f_eq_left:
  "[| inj f ; X ~= {} ; !! a. a:X ==> Qf a =T[M1,M2] P |]
               ==> !<f> :X .. Qf =T[M1,M2] P"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_Rep_int_choice_sum_eq_left, auto)

lemmas cspT_int_eq_left =
       cspT_Rep_int_choice_sum_eq_left
       cspT_Rep_int_choice_nat_eq_left
       cspT_Rep_int_choice_set_eq_left
       cspT_Rep_int_choice_com_eq_left
       cspT_Rep_int_choice_f_eq_left
       cspT_Int_choice_eq_left

(* ---------------------------------------------- *
      replicated internal choice -> binary ...
 * ---------------------------------------------- *)

(* ---- Un ---- *)

(* nat *)

lemma cspT_Rep_int_choice_nat_Un:
  "!nat n:(N1 Un N2) .. Pf n =T[M,M] !nat n:N1 .. Pf n |~| !nat n:N2 .. Pf n"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (auto simp add: in_traces)
done

(* set *)

lemma cspT_Rep_int_choice_set_Un:
  "!set X:(Xs1 Un Xs2) .. Pf X =T[M,M] !set X:Xs2 .. Pf X |~| !set X:Xs1 .. Pf X"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (auto simp add: in_traces)
done

(* com *)

lemma cspT_Rep_int_choice_com_Un:
  "! x:(X1 Un X2) .. Pf x =T[M,M] ! x:X1 .. Pf x |~| ! x:X2 .. Pf x"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (auto simp add: in_traces)
done

(* f *)

lemma cspT_Rep_int_choice_f_Un:
  "inj f ==> 
   !<f> x:(X1 Un X2) .. Pf x =T[M,M] !<f> x:X1 .. Pf x |~| !<f> x:X2 .. Pf x"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (auto simp add: in_traces)
done

lemmas cspT_Rep_int_choice_Un =
       cspT_Rep_int_choice_nat_Un
       cspT_Rep_int_choice_set_Un
       cspT_Rep_int_choice_com_Un
       cspT_Rep_int_choice_f_Un

(* ---- insert ---- *)

(* nat *)

lemma cspT_Rep_int_choice_nat_insert:
  "!nat n:(insert m N) .. Pf n =T[M,M] Pf m |~| !nat n:N .. Pf n"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (auto simp add: in_traces)
done

(* set *)

lemma cspT_Rep_int_choice_set_insert:
  "!set X:(insert Y Xs) .. Pf X =T[M,M] Pf Y |~| !set X:Xs .. Pf X"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (auto simp add: in_traces)
done

(* com *)

lemma cspT_Rep_int_choice_com_insert:
  "! x:(insert a X) .. Pf x =T[M,M] Pf a |~| ! x:X .. Pf x"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (auto simp add: in_traces)
done

(* f *)

lemma cspT_Rep_int_choice_f_insert:
  "inj f ==> !<f> x:(insert a X) .. Pf x =T[M,M] Pf a |~| !<f> x:X .. Pf x"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (auto simp add: in_traces)
done

lemmas cspT_Rep_int_choice_insert =
       cspT_Rep_int_choice_nat_insert
       cspT_Rep_int_choice_set_insert
       cspT_Rep_int_choice_com_insert
       cspT_Rep_int_choice_f_insert

lemmas cspT_Rep_int_choice_sepa =
       cspT_Rep_int_choice_insert
       cspT_Rep_int_choice_Un

(* ---------------------------------------------- *
       simplify replicated internal choice
 * ---------------------------------------------- *)

lemma cspT_Rep_int_choice_com_map_f:
  "inj f ==> ! x:(f ` X) .. Pf x =T[M,M] !<f> x:X .. Pf (f x)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (auto simp add: in_traces)
done

lemma cspT_Rep_int_choice_f_map_f:
  "[| inj f ; inj g |] ==> !<f> x:(g ` X) .. Pf x =T[M,M] !<f o g> x:X .. Pf (g x)"
apply (subgoal_tac "inj (f o g)")
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (auto simp add: in_traces)
apply (auto simp add: inj_on_def)
done

lemmas cspT_Rep_int_choice_f_map =
       cspT_Rep_int_choice_com_map_f
       cspT_Rep_int_choice_f_map_f

end
