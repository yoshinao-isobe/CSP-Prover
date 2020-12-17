           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_law_dist
imports CSP_F_law_basic CSP_F_law_decompo CSP_T.CSP_T_law_dist
        CSP_F_law_alpha_par
begin

(*****************************************************************

      distribution over internal choice

         1. (P1 |~| P2) [+] Q
         2. Q [+] (P1 |~| P2)
         3. (P1 |~| P2) |[X]| Q
         4. Q |[X]| (P1 |~| P2)
         5. (P1 |~| P2) -- X
         6. (P1 |~| P2) [[r]]
         7. (P1 |~| P2) ;; Q
         8. (P1 |~| P2) |. n
         9. !! x:X .. (P1 |~| P2)

 *****************************************************************)

(*********************************************************
                dist law for Ext_choice (l)
 *********************************************************)

lemma cspF_Ext_choice_dist_l: 
  "(P1 |~| P2) [+] Q =F[M,M]
   (P1 [+] Q) |~| (P2 [+] Q)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Ext_choice_dist_l)
apply (rule order_antisym)
apply (rule, simp add: in_traces in_failures, fast)+
done

(*********************************************************
                dist law for Ext_choice (r)
 *********************************************************)

lemma cspF_Ext_choice_dist_r: 
  "P [+] (Q1 |~| Q2) =F[M,M]
   (P [+] Q1) |~| (P [+] Q2)"
apply (rule cspF_rw_left)
apply (rule cspF_commut)
apply (rule cspF_rw_left)
apply (rule cspF_Ext_choice_dist_l)
apply (rule cspF_decompo)
apply (rule cspF_commut)+
done

(*********************************************************
                dist law for Parallel (l)
 *********************************************************)

lemma cspF_Parallel_dist_l: 
  "(P1 |~| P2) |[X]| Q =F[M,M]
   (P1 |[X]| Q) |~| (P2 |[X]| Q)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Parallel_dist_l)
apply (rule order_antisym)

  apply (rule, simp add: in_failures)
  apply (elim disjE conjE exE)
  apply (rule disjI1)
  apply (rule_tac x="Y" in exI)
  apply (rule_tac x="Z" in exI)
  apply (fast)
  apply (rule disjI2)
  apply (rule_tac x="Y" in exI)
  apply (rule_tac x="Z" in exI)
  apply (fast)

  apply (rule, simp add: in_failures)
  apply (elim disjE conjE exE)
  apply (rule_tac x="Y" in exI)
  apply (rule_tac x="Z" in exI)
  apply (fast)
  apply (rule_tac x="Y" in exI)
  apply (rule_tac x="Z" in exI)
  apply (fast)
done

(*********************************************************
                dist law for Parallel (r)
 *********************************************************)

lemma cspF_Parallel_dist_r: 
  "P |[X]| (Q1 |~| Q2) =F[M,M]
   (P |[X]| Q1) |~| (P |[X]| Q2)"
apply (rule cspF_rw_left)
apply (rule cspF_commut)
apply (rule cspF_rw_left)
apply (rule cspF_Parallel_dist_l)
apply (rule cspF_decompo)
apply (rule cspF_commut)+
done

(*********************************************************
                dist law for Hiding
 *********************************************************)

lemma cspF_Hiding_dist: 
  "(P1 |~| P2) -- X =F[M,M]
   (P1 -- X) |~| (P2 -- X)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Hiding_dist)
apply (rule order_antisym)
apply (rule, simp add: in_failures, fast)+
done

(*********************************************************
               dist law for Renaming
 *********************************************************)

lemma cspF_Renaming_dist: 
  "(P1 |~| P2) [[r]] =F[M,M]
   (P1 [[r]]) |~| (P2 [[r]])"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Renaming_dist)
apply (rule order_antisym)
apply (rule, simp add: in_failures, fast)+
done

(*********************************************************
         dist law for Sequential composition
 *********************************************************)

lemma cspF_Seq_compo_dist: 
  "(P1 |~| P2) ;; Q =F[M,M]
   (P1 ;; Q) |~| (P2 ;; Q)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Seq_compo_dist)
apply (rule order_antisym)
apply (rule, simp add: in_traces in_failures, fast)+
done

(*********************************************************
               dist law for Depth_rest
 *********************************************************)

lemma cspF_Depth_rest_dist: 
  "(P1 |~| P2) |. n =F[M,M]
   (P1 |. n) |~| (P2 |. n)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Depth_rest_dist)
apply (rule order_antisym)
apply (rule, simp add: in_failures)
apply (rule, simp add: in_failures)
apply (fast)
done

(*********************************************************
               dist law for Rep_int_choice
 *********************************************************)

lemma cspF_Rep_int_choice_sum_dist:
  "!! c:C .. (Pf c |~| Qf c) =F[M,M] (!! c:C .. Pf c) |~| (!! c:C .. Qf c)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_dist)
apply (rule order_antisym)
apply (rule, simp add: in_failures, fast)+
done

lemma cspF_Rep_int_choice_nat_dist:
  "!nat n:N .. (Pf n |~| Qf n) =F[M,M] (!nat n:N .. Pf n) |~| (!nat n:N .. Qf n)"
by (simp add: Rep_int_choice_ss_def cspF_Rep_int_choice_sum_dist)

lemma cspF_Rep_int_choice_set_dist:
  "!set X:Xs .. (Pf X |~| Qf X) =F[M,M] (!set X:Xs .. Pf X) |~| (!set X:Xs .. Qf X)"
by (simp add: Rep_int_choice_ss_def cspF_Rep_int_choice_sum_dist)

lemma cspF_Rep_int_choice_com_dist:
  "! a:X .. (Pf a |~| Qf a) =F[M,M] (! a:X .. Pf a) |~| (! a:X .. Qf a)"
by (simp add: Rep_int_choice_com_def cspF_Rep_int_choice_set_dist)

lemma cspF_Rep_int_choice_f_dist:
  "inj f ==>
   !<f> a:X .. (Pf a |~| Qf a) =F[M,M] (!<f> a:X .. Pf a) |~| (!<f> a:X .. Qf a)"
by (simp add: Rep_int_choice_f_def cspF_Rep_int_choice_com_dist)

lemmas cspF_Rep_int_choice_dist =
       cspF_Rep_int_choice_sum_dist
       cspF_Rep_int_choice_nat_dist
       cspF_Rep_int_choice_set_dist
       cspF_Rep_int_choice_com_dist
       cspF_Rep_int_choice_f_dist

(*********************************************************
                     dist laws
 *********************************************************)

lemmas cspF_dist = cspF_Ext_choice_dist_l cspF_Ext_choice_dist_r
                   cspF_Parallel_dist_l   cspF_Parallel_dist_r
                   cspF_Hiding_dist       cspF_Renaming_dist
                   cspF_Seq_compo_dist    cspF_Depth_rest_dist
                   cspF_Rep_int_choice_dist


(*****************************************************************

      distribution over replicated internal choice

         1. (!! :C .. Pf) [+] Q
         2. Q [+] (!! :C .. Pf)
         3. (!! :C .. Pf) |[X]| Q
         4. Q |[X]| (!! :C .. Pf)
         5. (!! :C .. Pf) -- X
         6. (!! :C .. Pf) [[r]]
         7. (!! :C .. Pf) |. n

 *****************************************************************)

(*********************************************************
                Rep_dist law for Ext_choice (l)
 *********************************************************)

lemma cspF_Ext_choice_Dist_sum_l_nonempty: 
  "sumset C ~= {} ==> (!! :C .. Pf) [+] Q =F[M,M]
                      !! c:C .. (Pf c [+] Q)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Dist_nonempty)
apply (rule order_antisym)
apply (rule, simp add: in_traces in_failures, fast)+
done

(*** Dist ***)

lemma cspF_Ext_choice_Dist_sum_l: 
  "(!! :C .. Pf) [+] Q =F[M,M]
   IF (sumset C={}) THEN (DIV [+] Q) ELSE (!! c:C .. (Pf c [+] Q))"
apply (case_tac "sumset C={}")
apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (rule cspF_decompo)
apply (rule cspF_Rep_int_choice_empty)
apply (simp_all)

apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (rule cspF_Ext_choice_Dist_sum_l_nonempty)
apply (simp)
done

(*********************************************************
                Dist_sum law for Ext_choice (r)
 *********************************************************)

lemma cspF_Ext_choice_Dist_sum_r_nonempty: 
  "sumset C ~= {} ==> P [+] (!! :C .. Qf) =F[M,M]
               !! c:C .. (P [+] Qf c)"
apply (rule cspF_rw_left)
apply (rule cspF_commut)
apply (rule cspF_rw_left)
apply (rule cspF_Ext_choice_Dist_sum_l_nonempty, simp)
apply (rule cspF_decompo, simp)
apply (rule cspF_commut)
done

(*** Dist ***)

lemma cspF_Ext_choice_Dist_sum_r: 
  "P [+] (!! :C .. Qf) =F[M,M]
   IF (sumset C={}) THEN (P [+] DIV) ELSE (!! c:C .. (P [+] Qf c))"
apply (case_tac "sumset C={}")
apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (rule cspF_decompo)
apply (simp)
apply (simp add: cspF_Rep_int_choice_empty)

apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (rule cspF_Ext_choice_Dist_sum_r_nonempty)
apply (simp)
done

(*********************************************************
                Dist_sum law for Parallel (l)
 *********************************************************)

lemma cspF_Parallel_Dist_sum_l_nonempty: 
  "sumset C ~= {} ==>
     (!! :C .. Pf) |[X]| Q =F[M,M]
     !! c:C .. (Pf c |[X]| Q)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Dist_nonempty)
apply (rule order_antisym)

(* domF *)
  apply (rule)
  apply (simp add: in_failures)
  apply (elim conjE exE bexE)
   apply (rule_tac x="c" in bexI)
   apply (rule_tac x="Y" in exI)
   apply (rule_tac x="Z" in exI)
   apply (fast)
   apply (simp)
  (* *)
  apply (rule)
  apply (simp add: in_failures)
  apply (elim conjE exE bexE)
   apply (rule_tac x="Y" in exI)
   apply (rule_tac x="Z" in exI)
   apply (fast)
done

(*** Dist ***)

lemma cspF_Parallel_Dist_sum_l: 
  "(!! :C .. Pf) |[X]| Q =F[M,M]
   IF (sumset C={}) THEN (DIV |[X]| Q) ELSE (!! c:C .. (Pf c |[X]| Q))"
apply (case_tac "sumset C={}")
apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (rule cspF_decompo)
apply (simp)
apply (simp add: cspF_Rep_int_choice_empty)
apply (simp)

apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (rule cspF_Parallel_Dist_sum_l_nonempty)
apply (simp)
done

(*********************************************************
                Dist_sum law for Parallel (r)
 *********************************************************)

lemma cspF_Parallel_Dist_sum_r_nonempty: 
  "sumset C ~= {} ==>
     P |[X]| (!! :C .. Qf) =F[M,M]
     !! c:C .. (P |[X]| Qf c)"
apply (rule cspF_rw_left)
apply (rule cspF_commut)
apply (rule cspF_rw_left)
apply (rule cspF_Parallel_Dist_sum_l_nonempty, simp)
apply (rule cspF_decompo, simp)
apply (rule cspF_commut)
done

(*** Dist ***)

lemma cspF_Parallel_Dist_sum_r: 
  "P |[X]| (!! :C .. Qf) =F[M,M]
   IF (sumset C={}) THEN (P |[X]| DIV) ELSE (!! c:C .. (P |[X]| Qf c))"
apply (case_tac "sumset C={}")
apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (rule cspF_decompo)
apply (simp)
apply (simp)
apply (simp add: cspF_Rep_int_choice_empty)

apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (rule cspF_Parallel_Dist_sum_r_nonempty)
apply (simp)
done

(*********************************************************
                Dist_sum law for Hiding
 *********************************************************)

lemma cspF_Hiding_Dist_sum: 
  "(!! :C .. Pf) -- X =F[M,M]
   !! c:C .. (Pf c -- X)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Dist)
apply (rule order_antisym)
apply (rule, simp add: in_failures, fast)+
done

(*********************************************************
                Dist_sum law for Renaming
 *********************************************************)

lemma cspF_Renaming_Dist_sum: 
  "(!! :C .. Pf) [[r]] =F[M,M]
   !! c:C .. (Pf c [[r]])"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Dist)
apply (rule order_antisym)
apply (rule, simp add: in_failures, fast)+
done

(*********************************************************
          Dist_sum law for Sequential composition
 *********************************************************)

lemma cspF_Seq_compo_Dist_sum: 
  "(!! :C .. Pf) ;; Q =F[M,M]
   !! c:C .. (Pf c ;; Q)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Dist)
apply (rule order_antisym)
apply (rule, simp add: in_traces in_failures)
apply (force)
apply (rule, simp add: in_traces in_failures)
apply (force)
done

(*********************************************************
                Dist_sum law for Depth_rest
 *********************************************************)

lemma cspF_Depth_rest_Dist_sum: 
  "(!! :C .. Pf) |. m =F[M,M]
   !! c:C .. (Pf c |. m)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Dist)
apply (rule order_antisym)
apply (rule, simp add: in_failures)
apply (rule, simp add: in_failures)
done

(*********************************************************
                     Dist_sum laws
 *********************************************************)

lemmas cspF_Dist_sum = cspF_Ext_choice_Dist_sum_l cspF_Ext_choice_Dist_sum_r
                        cspF_Parallel_Dist_sum_l   cspF_Parallel_Dist_sum_r
                        cspF_Hiding_Dist_sum       cspF_Renaming_Dist_sum
                        cspF_Seq_compo_Dist_sum    cspF_Depth_rest_Dist_sum

lemmas cspF_Dist_sum_nonempty = 
       cspF_Ext_choice_Dist_sum_l_nonempty cspF_Ext_choice_Dist_sum_r_nonempty
       cspF_Parallel_Dist_sum_l_nonempty   cspF_Parallel_Dist_sum_r_nonempty
       cspF_Hiding_Dist_sum       cspF_Renaming_Dist_sum
       cspF_Seq_compo_Dist_sum    cspF_Depth_rest_Dist_sum

(*****************************************************************

      distribution of internal bind over ...

         1. (!nat :N .. Pf) [+] Q
         2. Q [+] (!nat :N .. Pf)
         3. (!nat :N .. Pf) |[X]| Q
         4. Q |[X]| (!nat :N .. Pf)
         5. (!nat :N .. Pf) -- X
         6. (!nat :N .. Pf) [[r]]
         7. (!nat :N .. Pf) |. n

 *****************************************************************)

(*********************************************************
                Dist law for Ext_choice (l)
 *********************************************************)

lemma cspF_Ext_choice_Dist_nat_l_nonempty: 
  "N ~= {} ==> (!nat :N .. Pf) [+] Q =F[M,M]
               !nat n:N .. (Pf n [+] Q)"
by (simp add: Rep_int_choice_ss_def cspF_Dist_sum_nonempty)

(*** Dist ***)

lemma cspF_Ext_choice_Dist_nat_l: 
  "(!nat :N .. Pf) [+] Q =F[M,M]
   IF (N={}) THEN (DIV [+] Q) ELSE (!nat n:N .. (Pf n [+] Q))"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspF_rw_left)
apply (rule cspF_Dist_sum)
apply (simp)
done

(*********************************************************
                Dist_nat law for Ext_choice (r)
 *********************************************************)

lemma cspF_Ext_choice_Dist_nat_r_nonempty: 
  "N ~= {} ==> P [+] (!nat :N .. Qf) =F[M,M]
               !nat n:N .. (P [+] Qf n)"
by (simp add: Rep_int_choice_ss_def cspF_Dist_sum_nonempty)

(*** Dist ***)

lemma cspF_Ext_choice_Dist_nat_r: 
  "P [+] (!nat :N .. Qf) =F[M,M]
   IF (N={}) THEN (P [+] DIV) ELSE (!nat n:N .. (P [+] Qf n))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_rw_left, rule cspF_Dist_sum, simp)

(*********************************************************
                Dist_nat law for Parallel (l)
 *********************************************************)

lemma cspF_Parallel_Dist_nat_l_nonempty: 
  "N ~= {} ==>
     (!nat :N .. Pf) |[X]| Q =F[M,M]
     !nat n:N .. (Pf n |[X]| Q)"
by (simp add: Rep_int_choice_ss_def cspF_Dist_sum_nonempty)

(*** Dist ***)

lemma cspF_Parallel_Dist_nat_l: 
  "(!nat :N .. Pf) |[X]| Q =F[M,M]
   IF (N={}) THEN (DIV |[X]| Q) ELSE (!nat n:N .. (Pf n |[X]| Q))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_rw_left, rule cspF_Dist_sum, simp)

(*********************************************************
                Dist_nat law for Parallel (r)
 *********************************************************)

lemma cspF_Parallel_Dist_nat_r_nonempty: 
  "N ~= {} ==>
     P |[X]| (!nat :N .. Qf) =F[M,M]
     !nat n:N .. (P |[X]| Qf n)"
by (simp add: Rep_int_choice_ss_def cspF_Dist_sum_nonempty)

(*** Dist ***)

lemma cspF_Parallel_Dist_nat_r: 
  "P |[X]| (!nat :N .. Qf) =F[M,M]
   IF (N={}) THEN (P |[X]| DIV) ELSE (!nat n:N .. (P |[X]| Qf n))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_rw_left, rule cspF_Dist_sum, simp)

(*********************************************************
                Dist_nat law for Hiding
 *********************************************************)

lemma cspF_Hiding_Dist_nat: 
  "(!nat :N .. Pf) -- X =F[M,M]
   !nat n:N .. (Pf n -- X)"
by (simp add: Rep_int_choice_ss_def cspF_Dist_sum_nonempty)

(*********************************************************
                Dist_nat law for Renaming
 *********************************************************)

lemma cspF_Renaming_Dist_nat: 
  "(!nat :N .. Pf) [[r]] =F[M,M]
   !nat n:N .. (Pf n [[r]])"
by (simp add: Rep_int_choice_ss_def cspF_Dist_sum_nonempty)

(*********************************************************
          Dist_nat law for Sequential composition
 *********************************************************)

lemma cspF_Seq_compo_Dist_nat: 
  "(!nat :N .. Pf) ;; Q =F[M,M]
   !nat n:N .. (Pf n ;; Q)"
by (simp add: Rep_int_choice_ss_def cspF_Dist_sum_nonempty)

(*********************************************************
                Dist_nat law for Depth_rest
 *********************************************************)

lemma cspF_Depth_rest_Dist_nat: 
  "(!nat :N .. Pf) |. m =F[M,M]
   !nat n:N .. (Pf n |. m)"
by (simp add: Rep_int_choice_ss_def cspF_Dist_sum_nonempty)

(*********************************************************
                     Dist_nat laws
 *********************************************************)

lemmas cspF_Dist_nat = cspF_Ext_choice_Dist_nat_l cspF_Ext_choice_Dist_nat_r
                        cspF_Parallel_Dist_nat_l   cspF_Parallel_Dist_nat_r
                        cspF_Hiding_Dist_nat       cspF_Renaming_Dist_nat
                        cspF_Seq_compo_Dist_nat    cspF_Depth_rest_Dist_nat

lemmas cspF_Dist_nat_nonempty = 
       cspF_Ext_choice_Dist_nat_l_nonempty cspF_Ext_choice_Dist_nat_r_nonempty
       cspF_Parallel_Dist_nat_l_nonempty   cspF_Parallel_Dist_nat_r_nonempty
       cspF_Hiding_Dist_nat       cspF_Renaming_Dist_nat
       cspF_Seq_compo_Dist_nat    cspF_Depth_rest_Dist_nat

(*****************************************************************

      distribution of internal bind over ...

         1. (!set :Xs .. Pf) [+] Q
         2. Q [+] (!set :Xs .. Pf)
         3. (!set :Xs .. Pf) |[X]| Q
         4. Q |[X]| (!set :Xs .. Pf)
         5. (!set :Xs .. Pf) -- X
         6. (!set :Xs .. Pf) [[r]]
         7. (!set :Xs .. Pf) |. n

 *****************************************************************)

(*********************************************************
                Dist law for Ext_choice (l)
 *********************************************************)

lemma cspF_Ext_choice_Dist_set_l_nonempty: 
  "Xs ~= {} ==> (!set :Xs .. Pf) [+] Q =F[M,M]
               !set X:Xs .. (Pf X [+] Q)"
by (simp add: Rep_int_choice_ss_def cspF_Dist_sum_nonempty)

(*** Dist ***)

lemma cspF_Ext_choice_Dist_set_l: 
  "(!set :Xs .. Pf) [+] Q =F[M,M]
   IF (Xs={}) THEN (DIV [+] Q) ELSE (!set X:Xs .. (Pf X [+] Q))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_rw_left, rule cspF_Dist_sum, simp)

(*********************************************************
                Dist_set law for Ext_choice (r)
 *********************************************************)

lemma cspF_Ext_choice_Dist_set_r_nonempty: 
  "Xs ~= {} ==> P [+] (!set :Xs .. Qf) =F[M,M]
               !set X:Xs .. (P [+] Qf X)"
by (simp add: Rep_int_choice_ss_def cspF_Dist_sum_nonempty)

(*** Dist ***)

lemma cspF_Ext_choice_Dist_set_r: 
  "P [+] (!set :Xs .. Qf) =F[M,M]
   IF (Xs={}) THEN (P [+] DIV) ELSE (!set X:Xs .. (P [+] Qf X))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_rw_left, rule cspF_Dist_sum, simp)

(*********************************************************
                Dist_set law for Parallel (l)
 *********************************************************)

lemma cspF_Parallel_Dist_set_l_nonempty: 
  "Xs ~= {} ==>
     (!set :Xs .. Pf) |[Y]| Q =F[M,M]
     !set X:Xs .. (Pf X |[Y]| Q)"
by (simp add: Rep_int_choice_ss_def cspF_Dist_sum_nonempty)

(*** Dist ***)

lemma cspF_Parallel_Dist_set_l: 
  "(!set :Xs .. Pf) |[Y]| Q =F[M,M]
   IF (Xs={}) THEN (DIV |[Y]| Q) ELSE (!set X:Xs .. (Pf X |[Y]| Q))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_rw_left, rule cspF_Dist_sum, simp)

(*********************************************************
                Dist_set law for Parallel (r)
 *********************************************************)

lemma cspF_Parallel_Dist_set_r_nonempty: 
  "Xs ~= {} ==>
     P |[Y]| (!set :Xs .. Qf) =F[M,M]
     !set X:Xs .. (P |[Y]| Qf X)"
by (simp add: Rep_int_choice_ss_def cspF_Dist_sum_nonempty)

(*** Dist ***)

lemma cspF_Parallel_Dist_set_r: 
  "P |[Y]| (!set :Xs .. Qf) =F[M,M]
   IF (Xs={}) THEN (P |[Y]| DIV) ELSE (!set X:Xs .. (P |[Y]| Qf X))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_rw_left, rule cspF_Dist_sum, simp)

(*********************************************************
                Dist_set law for Hiding
 *********************************************************)

lemma cspF_Hiding_Dist_set: 
  "(!set :Xs .. Pf) -- Y =F[M,M]
   !set X:Xs .. (Pf X -- Y)"
by (simp add: Rep_int_choice_ss_def cspF_Dist_sum_nonempty)

(*********************************************************
                Dist_set law for Renaming
 *********************************************************)

lemma cspF_Renaming_Dist_set: 
  "(!set :Xs .. Pf) [[r]] =F[M,M]
   !set X:Xs .. (Pf X [[r]])"
by (simp add: Rep_int_choice_ss_def cspF_Dist_sum_nonempty)

(*********************************************************
          Dist_set law for Sequential composition
 *********************************************************)

lemma cspF_Seq_compo_Dist_set: 
  "(!set :Xs .. Pf) ;; Q =F[M,M]
   !set X:Xs .. (Pf X ;; Q)"
by (simp add: Rep_int_choice_ss_def cspF_Dist_sum_nonempty)

(*********************************************************
                Dist_set law for Depth_rest
 *********************************************************)

lemma cspF_Depth_rest_Dist_set: 
  "(!set :Xs .. Pf) |. m =F[M,M]
   !set X:Xs .. (Pf X |. m)"
by (simp add: Rep_int_choice_ss_def cspF_Dist_sum_nonempty)

(*********************************************************
                     Dist_set laws
 *********************************************************)

lemmas cspF_Dist_set = cspF_Ext_choice_Dist_set_l cspF_Ext_choice_Dist_set_r
                        cspF_Parallel_Dist_set_l   cspF_Parallel_Dist_set_r
                        cspF_Hiding_Dist_set       cspF_Renaming_Dist_set
                        cspF_Seq_compo_Dist_set    cspF_Depth_rest_Dist_set

lemmas cspF_Dist_set_nonempty = 
       cspF_Ext_choice_Dist_set_l_nonempty cspF_Ext_choice_Dist_set_r_nonempty
       cspF_Parallel_Dist_set_l_nonempty   cspF_Parallel_Dist_set_r_nonempty
       cspF_Hiding_Dist_set       cspF_Renaming_Dist_set
       cspF_Seq_compo_Dist_set    cspF_Depth_rest_Dist_set

(*****************************************************************

      for convenience

         1. (! :X .. Pf) [+] Q
         2. Q [+] (! :X .. Pf)
         3. (! :X .. Pf) |[X]| Q
         4. Q |[X]| (! :X .. Pf)
         5. (! :X .. Pf) -- X
         6. (! :X .. Pf) [[r]]
         7. (! :X .. Pf) |. n

 *****************************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Ext_choice_Dist_com_l_nonempty: 
  "X ~= {}
   ==> (! :X .. Pf) [+] Q =F[M,M] ! x:X .. (Pf x [+] Q)"
by (simp add: Rep_int_choice_com_def cspF_Dist_set_nonempty)

lemma cspF_Ext_choice_Dist_com_r_nonempty: 
  "X ~= {}
   ==> P [+] (! :X .. Qf) =F[M,M] ! x:X .. (P [+] Qf x)"
by (simp add: Rep_int_choice_com_def cspF_Dist_set_nonempty)

lemma cspF_Parallel_Dist_com_l_nonempty: 
  "Y ~= {}
   ==> (! :Y .. Pf) |[X]| Q =F[M,M] ! x:Y .. (Pf x |[X]| Q)"
by (simp add: Rep_int_choice_com_def cspF_Dist_set_nonempty)

lemma cspF_Parallel_Dist_com_r_nonempty: 
  "Y ~= {}
   ==> P |[X]| (! :Y .. Qf) =F[M,M] ! x:Y .. (P |[X]| Qf x)"
by (simp add: Rep_int_choice_com_def cspF_Dist_set_nonempty)

lemma cspF_Ext_choice_Dist_com_l: 
  "(! :X .. Pf) [+] Q =F[M,M] 
   IF (X ={}) THEN (DIV [+] Q) ELSE (! x:X .. (Pf x [+] Q))"
apply (simp add: Rep_int_choice_com_def)
by (rule cspF_rw_left, rule cspF_Dist_set, simp)

lemma cspF_Ext_choice_Dist_com_r: 
  "P [+] (! :X .. Qf) =F[M,M]
   IF (X ={}) THEN (P [+] DIV) ELSE (! x:X .. (P [+] Qf x))"
apply (simp add: Rep_int_choice_com_def)
by (rule cspF_rw_left, rule cspF_Dist_set, simp)

lemma cspF_Parallel_Dist_com_l: 
  "(! :Y .. Pf) |[X]| Q =F[M,M]
   IF (Y ={}) THEN (DIV |[X]| Q) ELSE (! x:Y .. (Pf x |[X]| Q))"
apply (simp add: Rep_int_choice_com_def)
by (rule cspF_rw_left, rule cspF_Dist_set, simp)

lemma cspF_Parallel_Dist_com_r: 
  "P |[X]| (! :Y .. Qf) =F[M,M] 
   IF (Y ={}) THEN (P |[X]| DIV) ELSE (! x:Y .. (P |[X]| Qf x))"
apply (simp add: Rep_int_choice_com_def)
by (rule cspF_rw_left, rule cspF_Dist_set, simp)

lemma cspF_Hiding_Dist_com: 
  "(! :Y .. Pf) -- X =F[M,M] ! x:Y .. (Pf x -- X)"
by (simp add: Rep_int_choice_com_def cspF_Dist_set_nonempty)

lemma cspF_Renaming_Dist_com: 
  "(! :X .. Pf) [[r]] =F[M,M] ! x:X .. (Pf x [[r]])"
by (simp add: Rep_int_choice_com_def cspF_Dist_set_nonempty)

lemma cspF_Seq_compo_Dist_com:
  "(! :X .. Pf) ;; Q =F[M,M] ! x:X .. (Pf x ;; Q)"
by (simp add: Rep_int_choice_com_def cspF_Dist_set_nonempty)

lemma cspF_Depth_rest_Dist_com: 
  "(! :X .. Pf) |. n =F[M,M] ! x:X .. (Pf x |. n)"
by (simp add: Rep_int_choice_com_def cspF_Dist_set_nonempty)

(*********************************************************
                     Dist laws
 *********************************************************)

lemmas cspF_Dist_com = cspF_Ext_choice_Dist_com_l cspF_Ext_choice_Dist_com_r
                           cspF_Parallel_Dist_com_l   cspF_Parallel_Dist_com_r
                           cspF_Hiding_Dist_com       cspF_Renaming_Dist_com
                           cspF_Seq_compo_Dist_com    cspF_Depth_rest_Dist_com

lemmas cspF_Dist_com_nonempty = 
       cspF_Ext_choice_Dist_com_l_nonempty cspF_Ext_choice_Dist_com_r_nonempty
       cspF_Parallel_Dist_com_l_nonempty   cspF_Parallel_Dist_com_r_nonempty
       cspF_Hiding_Dist_com       cspF_Renaming_Dist_com
       cspF_Seq_compo_Dist_com    cspF_Depth_rest_Dist_com


(*****************************************************************

      for convenience

         1. (!<f> :X .. Pf) [+] Q
         2. Q [+] (!<f> :X .. Pf)
         3. (!<f> :X .. Pf) |[X]| Q
         4. Q |[X]| (!<f> :X .. Pf)
         5. (!<f> :X .. Pf) -- X
         6. (!<f> :X .. Pf) [[r]]
         7. (!<f> :X .. Pf) |. n

 *****************************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Ext_choice_Dist_f_l_nonempty: 
  "[| inj f ; X ~= {} |]
   ==> (!<f> :X .. Pf) [+] Q =F[M,M] !<f> x:X .. (Pf x [+] Q)"
by (simp add: Rep_int_choice_f_def cspF_Dist_com_nonempty)

lemma cspF_Ext_choice_Dist_f_r_nonempty: 
  "[| inj f ; X ~= {} |]
   ==> P [+] (!<f> :X .. Qf) =F[M,M] !<f> x:X .. (P [+] Qf x)"
by (simp add: Rep_int_choice_f_def cspF_Dist_com_nonempty)

lemma cspF_Parallel_Dist_f_l_nonempty: 
  "[| inj f ; Y ~= {} |]
   ==> (!<f> :Y .. Pf) |[X]| Q =F[M,M] !<f> x:Y .. (Pf x |[X]| Q)"
by (simp add: Rep_int_choice_f_def cspF_Dist_com_nonempty)

lemma cspF_Parallel_Dist_f_r_nonempty: 
  "[| inj f ; Y ~= {} |]
   ==> P |[X]| (!<f> :Y .. Qf) =F[M,M] !<f> x:Y .. (P |[X]| Qf x)"
by (simp add: Rep_int_choice_f_def cspF_Dist_com_nonempty)

lemma cspF_Ext_choice_Dist_f_l: 
  "(!<f> :X .. Pf) [+] Q =F[M,M] 
   IF (X ={}) THEN (DIV [+] Q) ELSE (!<f> x:X .. (Pf x [+] Q))"
apply (simp add: Rep_int_choice_f_def)
by (rule cspF_rw_left, rule cspF_Dist_com, simp)

lemma cspF_Ext_choice_Dist_f_r: 
  "P [+] (!<f> :X .. Qf) =F[M,M]
   IF (X ={}) THEN (P [+] DIV) ELSE (!<f> x:X .. (P [+] Qf x))"
apply (simp add: Rep_int_choice_f_def)
by (rule cspF_rw_left, rule cspF_Dist_com, simp)

lemma cspF_Parallel_Dist_f_l: 
  "(!<f> :Y .. Pf) |[X]| Q =F[M,M]
   IF (Y ={}) THEN (DIV |[X]| Q) ELSE (!<f> x:Y .. (Pf x |[X]| Q))"
apply (simp add: Rep_int_choice_f_def)
by (rule cspF_rw_left, rule cspF_Dist_com, simp)

lemma cspF_Parallel_Dist_f_r: 
  "P |[X]| (!<f> :Y .. Qf) =F[M,M] 
   IF (Y ={}) THEN (P |[X]| DIV) ELSE (!<f> x:Y .. (P |[X]| Qf x))"
apply (simp add: Rep_int_choice_f_def)
by (rule cspF_rw_left, rule cspF_Dist_com, simp)

lemma cspF_Hiding_Dist_f: 
  "(!<f> :Y .. Pf) -- X =F[M,M] !<f> x:Y .. (Pf x -- X)"
by (simp add: Rep_int_choice_f_def cspF_Dist_com)

lemma cspF_Renaming_Dist_f: 
  "(!<f> :X .. Pf) [[r]] =F[M,M] !<f> x:X .. (Pf x [[r]])"
by (simp add: Rep_int_choice_f_def cspF_Dist_com)

lemma cspF_Seq_compo_Dist_f:
  "(!<f> :X .. Pf) ;; Q =F[M,M] !<f> x:X .. (Pf x ;; Q)"
by (simp add: Rep_int_choice_f_def cspF_Dist_com)

lemma cspF_Depth_rest_Dist_f: 
  "(!<f> :X .. Pf) |. n =F[M,M] !<f> x:X .. (Pf x |. n)"
by (simp add: Rep_int_choice_f_def cspF_Dist_com)

(*********************************************************
                     Dist laws
 *********************************************************)

lemmas cspF_Dist_f = cspF_Ext_choice_Dist_f_l cspF_Ext_choice_Dist_f_r
                           cspF_Parallel_Dist_f_l   cspF_Parallel_Dist_f_r
                           cspF_Hiding_Dist_f       cspF_Renaming_Dist_f
                           cspF_Seq_compo_Dist_f    cspF_Depth_rest_Dist_f

lemmas cspF_Dist_f_nonempty = 
       cspF_Ext_choice_Dist_f_l_nonempty cspF_Ext_choice_Dist_f_r_nonempty
       cspF_Parallel_Dist_f_l_nonempty   cspF_Parallel_Dist_f_r_nonempty
       cspF_Hiding_Dist_f       cspF_Renaming_Dist_f
       cspF_Seq_compo_Dist_f    cspF_Depth_rest_Dist_f

(*** all rules ***)

lemmas cspF_Dist = cspF_Dist_sum
                   cspF_Dist_nat cspF_Dist_set cspF_Dist_com cspF_Dist_f

lemmas cspF_Dist_nonempty = cspF_Dist_sum_nonempty
                            cspF_Dist_nat_nonempty
                            cspF_Dist_set_nonempty
                            cspF_Dist_com_nonempty
                            cspF_Dist_f_nonempty

(*****************************************************************

      additional distribution over replicated internal choice

         1. (!! :X .. (a -> P))
         2. (!! :Y .. (? :X -> P))

 *****************************************************************)

(*********************************************************
              Dist law for Act_prefix
 *********************************************************)

lemma cspF_Act_prefix_Dist_sum:
  "sumset C ~= {} ==> 
   a -> (!! :C .. Pf) =F[M,M] !! c:C .. (a -> Pf c)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Act_prefix_Dist)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (erule disjE)
  apply (force)

  apply (elim conjE exE bexE)
  apply (rule_tac x="c" in bexI)
  apply (force)
  apply (simp)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE bexE exE)
  apply (simp)
  apply (simp)
  apply (rule_tac x="c" in bexI)
  apply (simp)
  apply (simp)
done

(*********************************************************
              Dist_nat law for Ext_pre_choice
 *********************************************************)

lemma cspF_Ext_pre_choice_Dist_sum:
  "sumset C ~= {} ==> 
   ? x:X -> (!! c:C .. (Pf c) x) =F[M,M] !! c:C .. (? :X -> (Pf c))"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Ext_pre_choice_Dist)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (erule disjE)
  apply (force)

  apply (elim conjE exE bexE)
  apply (rule_tac x="c" in bexI)
  apply (force)
  apply (simp)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE exE bexE)
  apply (simp)
  apply (simp)
  apply (rule_tac x="c" in bexI)
  apply (simp)
  apply (simp)
done

(*****************************************************************
                     for convenienve
 *****************************************************************)

(* nat *)

lemma cspF_Act_prefix_Dist_nat:
  "N ~= {} ==> 
   a -> (!nat :N .. Pf) =F[M,M] !nat n:N .. (a -> Pf n)"
by (simp add: Rep_int_choice_ss_def cspF_Act_prefix_Dist_sum)

lemma cspF_Ext_pre_choice_Dist_nat:
  "N ~= {} ==> 
   ? x:X -> (!nat n:N .. (Pf n) x) =F[M,M] !nat n:N .. (? :X -> (Pf n))"
by (simp add: Rep_int_choice_ss_def cspF_Ext_pre_choice_Dist_sum)

(* set *)

lemma cspF_Act_prefix_Dist_set:
  "Xs ~= {} ==> 
   a -> (!set :Xs .. Pf) =F[M,M] !set X:Xs .. (a -> Pf X)"
by (simp add: Rep_int_choice_ss_def cspF_Act_prefix_Dist_sum)

lemma cspF_Ext_pre_choice_Dist_set:
  "Ys ~= {} ==> 
   ? x:X -> (!set Y:Ys .. (Pf Y) x) =F[M,M] !set Y:Ys .. (? :X -> (Pf Y))"
by (simp add: Rep_int_choice_ss_def cspF_Ext_pre_choice_Dist_sum)

(* com *)

lemma cspF_Act_prefix_Dist_com:
  "X ~= {} ==> 
   a -> (! :X .. Pf) =F[M,M] ! x:X .. (a -> Pf x)"
by (simp add: Rep_int_choice_com_def cspF_Act_prefix_Dist_set)

lemma cspF_Ext_pre_choice_Dist_com:
  "Y ~= {} ==> 
   ? x:X -> (! y:Y .. (Pf y) x) =F[M,M] ! y:Y .. (? :X -> (Pf y))"
by (simp add: Rep_int_choice_com_def cspF_Ext_pre_choice_Dist_set)

(* f *)

lemma cspF_Act_prefix_Dist_f:
  "X ~= {} ==> 
   a -> (!<f> :X .. Pf) =F[M,M] !<f> x:X .. (a -> Pf x)"
by (simp add: Rep_int_choice_f_def cspF_Act_prefix_Dist_com)

lemma cspF_Ext_pre_choice_Dist_f:
  "Y ~= {} ==> 
   ? x:X -> (!<f> y:Y .. (Pf y) x) =F[M,M] !<f> y:Y .. (? :X -> (Pf y))"
by (simp add: Rep_int_choice_f_def cspF_Ext_pre_choice_Dist_com)

(*** arias ***)

lemmas cspF_Act_prefix_Dist 
     = cspF_Act_prefix_Dist_sum
       cspF_Act_prefix_Dist_nat
       cspF_Act_prefix_Dist_set
       cspF_Act_prefix_Dist_com
       cspF_Act_prefix_Dist_f

lemmas cspF_Ext_pre_choice_Dist
     = cspF_Ext_pre_choice_Dist_sum
       cspF_Ext_pre_choice_Dist_nat
       cspF_Ext_pre_choice_Dist_set
       cspF_Ext_pre_choice_Dist_com
       cspF_Ext_pre_choice_Dist_f

(*****************************************************************
      distribution over external choice
         1. (P1 [+] P2) [[r]]
         2. (P1 [+] P2) |. n
 *****************************************************************)

(*********************
     [[r]]-[+]-dist
 *********************)

lemma cspF_Renaming_Ext_dist: 
  "(P1 [+] P2) [[r]] =F[M,M]
   (P1 [[r]]) [+] (P2 [[r]])"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Renaming_Ext_dist)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures in_traces)
 apply (force)

(* <= *)
 apply (rule)
 apply (simp add: in_failures in_traces)
 apply (force)
done

(*********************
     |.-[+]-dist
 *********************)

lemma cspF_Depth_rest_Ext_dist: 
  "(P1 [+] P2) |. n =F[M,M]
   (P1 |. n) [+] (P2 |. n)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Depth_rest_Ext_dist)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures in_traces)
 apply (force)

(* <= *)
 apply (rule)
 apply (simp add: in_failures in_traces)
 apply (force)
done

lemmas cspF_Ext_dist = cspF_Renaming_Ext_dist cspF_Depth_rest_Ext_dist

(*---------------------------------------------------------*
 |                   complex distribution                  |
 *---------------------------------------------------------*)

(*********************
     !!-input-!set
 *********************)

lemma cspF_Rep_int_choice_sum_input_set:
  "(!! c:C .. (? :(Yf c) -> Rff c))
   =F[M,M]
   (!set Y : {(Yf c)|c. c: sumset C} .. 
      (? a : Y -> (!! c:{c:C. a : Yf c}s .. Rff c a)))"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_input_set)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_failures)
 apply (elim disjE conjE exE bexE)
 apply (simp_all)
 apply (force)
 apply (force)

(* <= *)
 apply (rule, simp add: in_failures)
 apply (elim disjE conjE exE)
 apply (simp_all)
apply (rule_tac x="c" in bexI)
apply (simp)
apply (simp)
apply (rule_tac x="ca" in bexI)
apply (simp)
apply (simp)
done

lemma cspF_Rep_int_choice_nat_input_set:
  "(!nat n:N .. (? :(Yf n) -> Rff n))
   =F[M,M]
   (!set Y : {(Yf n)|n. n:N} .. (? a : Y -> (!nat n:{n:N. a : Yf n} .. Rff n a)))"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspF_rw_left)
apply (rule cspF_Rep_int_choice_sum_input_set)
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspF_decompo)
apply (auto)
apply (rule_tac x="type2 n" in exI)
by (auto)

lemma cspF_Rep_int_choice_set_input_set:
  "(!set X:Xs .. (? :(Yf X) -> Rff X))
   =F[M,M]
   (!set Y : {(Yf X)|X. X:Xs} .. (? a : Y -> (!set X:{X:Xs. a : Yf X} .. Rff X a)))"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspF_rw_left)
apply (rule cspF_Rep_int_choice_sum_input_set)
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspF_decompo)
apply (auto)
apply (rule_tac x="type1 X" in exI)
by (auto)

lemmas cspF_Rep_int_choice_input_set =
       cspF_Rep_int_choice_sum_input_set
       cspF_Rep_int_choice_nat_input_set
       cspF_Rep_int_choice_set_input_set

(*-------------------------------*
          !!-[+]-Dist
 *-------------------------------*)

lemma cspF_Rep_int_choice_Ext_Dist_sum:
  "ALL c:sumset C. (Qf c = SKIP | Qf c = DIV) ==>
   (!! c:C .. (Pf c [+] Qf c)) =F[M,M]
   ((!! :C .. Pf) [+] (!! :C .. Qf))"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_Ext_Dist)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_failures in_traces)
 apply (elim conjE exE bexE disjE)

  apply (drule_tac x="c" in bspec, simp)
  apply (erule disjE)
  apply (simp add: in_failures)
  apply (rule disjI2)
  apply (rule disjI2)
  apply (rule_tac x="c" in bexI)
  apply (simp add: in_traces)
  apply (simp)

  apply (simp add: in_failures)
  apply (force)

  apply (drule_tac x="c" in bspec, simp)
  apply (erule disjE)
  apply (simp add: in_failures)
  apply (rule disjI2)
  apply (rule_tac x="c" in bexI)
  apply (simp add: in_failures)
  apply (simp)

  apply (simp add: in_failures)
  apply (force)

  apply (drule_tac x="c" in bspec, simp)
  apply (erule disjE)
  apply (simp add: in_failures)
  apply (rule disjI2)
  apply (rule disjI2)
  apply (rule_tac x="c" in bexI)
  apply (simp add: in_traces)
  apply (simp)

  apply (simp add: in_traces)

(* => *)
 apply (rule)
 apply (simp add: in_failures in_traces)
 apply (elim conjE exE bexE disjE)
 apply (simp_all)

  apply (case_tac "EX c: sumset C. Qf c = SKIP")
  apply (erule bexE)
  apply (rule_tac x="cb" in bexI)
  apply (simp add: in_failures in_traces)
   apply (case_tac "Qf ca = SKIP")
   apply (simp add: in_failures)
   apply (case_tac "Qf ca = DIV")
   apply (simp add: in_failures)
   apply (fast)
  apply (simp)

  apply (simp add: in_failures in_traces)

  apply (force)
  apply (force)
  apply (force)
  apply (force)
done

lemma cspF_Rep_int_choice_Ext_Dist_nat:
  "ALL n:N. (Qf n = SKIP | Qf n = DIV) ==>
   (!nat n:N .. (Pf n [+] Qf n)) =F[M,M]
   ((!nat :N .. Pf) [+] (!nat :N .. Qf))"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspF_Rep_int_choice_Ext_Dist_sum)
by (auto)

lemma cspF_Rep_int_choice_Ext_Dist_set:
  "ALL X:Xs. (Qf X = SKIP | Qf X = DIV) ==>
   (!set X:Xs .. (Pf X [+] Qf X)) =F[M,M]
   ((!set :Xs .. Pf) [+] (!set :Xs .. Qf))"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspF_Rep_int_choice_Ext_Dist_sum)
by (auto)

lemma cspF_Rep_int_choice_Ext_Dist_com:
  "ALL a:X. (Qf a = SKIP | Qf a = DIV) ==>
   (! a:X .. (Pf a [+] Qf a)) =F[M,M]
   ((! :X .. Pf) [+] (! :X .. Qf))"
apply (simp add: Rep_int_choice_com_def)
apply (rule cspF_Rep_int_choice_Ext_Dist_set)
by (auto)

lemma cspF_Rep_int_choice_Ext_Dist_f:
  "[| inj f ; ALL a:X. (Qf a = SKIP | Qf a = DIV) |] ==>
   (!<f> a:X .. (Pf a [+] Qf a)) =F[M,M]
   ((!<f> :X .. Pf) [+] (!<f> :X .. Qf))"
apply (simp add: Rep_int_choice_f_def)
apply (rule cspF_Rep_int_choice_Ext_Dist_com)
by (auto)

lemmas cspF_Rep_int_choice_Ext_Dist =
       cspF_Rep_int_choice_Ext_Dist_sum
       cspF_Rep_int_choice_Ext_Dist_nat
       cspF_Rep_int_choice_Ext_Dist_set
       cspF_Rep_int_choice_Ext_Dist_com
       cspF_Rep_int_choice_Ext_Dist_f

(*-------------------------------*
          !!-input-Dist
 *-------------------------------*)

(* SKIP *)

lemma cspF_Rep_int_choice_input_Dist_SKIP:
  "(!set X:Xs .. (? :X -> Pf)) [+] SKIP =F[M,M]
   (? :(Union Xs) -> Pf) [+] SKIP"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_input_Dist)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces in_failures)
 apply (elim conjE exE disjE bexE)
 apply (simp_all)
 apply (force)

(* <= *)
 apply (rule, simp add: in_traces in_failures)
 apply (elim conjE exE disjE bexE)
 apply (simp_all)
 apply (force)
done

(* DIV *)

lemma cspF_Rep_int_choice_input_Dist_DIV:
  "(!set X:Xs .. (? :X -> Pf)) [+] DIV =F[M,M] (? :(Union Xs) -> Pf) [+] DIV"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_input_Dist)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces in_failures)
 apply (elim conjE exE disjE bexE)
 apply (simp_all)
 apply (force)

(* <= *)
 apply (rule, simp add: in_traces in_failures)
 apply (elim conjE exE disjE bexE)
 apply (simp_all)
 apply (force)
done

(* SKIP or DIV *)

lemma cspF_Rep_int_choice_input_Dist:
  "Q = SKIP | Q = DIV ==>
   (!set X:Xs .. (? :X -> Pf)) [+] Q =F[M,M] (? :(Union Xs) -> Pf) [+] Q"
apply (erule disjE)
apply (simp add: cspF_Rep_int_choice_input_Dist_SKIP)
apply (simp add: cspF_Rep_int_choice_input_Dist_DIV)
done

(*-------------------------------*
          !!-Ext-choice-SKIP
 *-------------------------------*)

lemma cspF_Rep_int_choice_sum_Ext_choice:
  "Q = SKIP | Q = DIV ==>
  (!! c:C .. (? :(Xf c) -> Pf c)) [+] Q
    =F[M,M] (? x:Union {(Xf c)|c. c: sumset C} -> 
                (!! c:{c:C. x: Xf c}s  .. Pf c x)) [+] Q"
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_Rep_int_choice_input_set)
apply (rule cspF_reflex)

apply (rule cspF_rw_left)
apply (rule cspF_Rep_int_choice_input_Dist)
apply (simp)
apply (simp)
done

(*** nat ***)

lemma cspF_Rep_int_choice_nat_Ext_choice:
  "Q = SKIP | Q = DIV ==>
  (!nat n:N .. (? :(Xf n) -> Pf n)) [+] Q
    =F[M,M] (? x:Union {(Xf n)|n. n:N} -> (!nat n:{n:N. x: Xf n}  .. Pf n x)) [+] Q"
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_Rep_int_choice_input_set)
apply (rule cspF_reflex)

apply (rule cspF_rw_left)
apply (rule cspF_Rep_int_choice_input_Dist)
apply (simp)
apply (simp)
done

(*** set ***)

lemma cspF_Rep_int_choice_set_Ext_choice:
  "Q = SKIP | Q = DIV ==>
  (!set X:Xs .. (? :(Xf X) -> Pf X)) [+] Q
    =F[M,M] (? x:Union {(Xf X)|X. X:Xs} -> (!set X:{X:Xs. x: Xf X}  .. Pf X x)) [+] Q"
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_Rep_int_choice_input_set)
apply (rule cspF_reflex)

apply (rule cspF_rw_left)
apply (rule cspF_Rep_int_choice_input_Dist)
apply (simp)
apply (simp)
done

lemmas cspF_Rep_int_choice_Ext_choice =
       cspF_Rep_int_choice_sum_Ext_choice
       cspF_Rep_int_choice_nat_Ext_choice
       cspF_Rep_int_choice_set_Ext_choice


(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)

(* --------------------------------------------------- *
     distribution hiding over sequential composition
 * --------------------------------------------------- *)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Seq_compo_hide_dist: 
  "(P ;; Q) -- X =F[M,M] (P -- X) ;; (Q -- X)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Seq_compo_hide_dist)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim conjE exE disjE)
 apply (simp_all)

  (* 1 *)
 apply (rule disjI1)
 apply (rule_tac x="sa" in exI)
 apply (simp)

  (* 2 *)
 apply (rule disjI2)
 apply (rule_tac x="sb --tr X" in exI)
 apply (rule_tac x="t --tr X" in exI)
 apply (simp)
 apply (rule conjI)
  apply (simp add: in_traces)
  apply (rule_tac x="sb ^^^ <Tick>" in exI)
  apply (simp)
  apply (rule_tac x="t" in exI)
  apply (simp)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE exE)
  (* 1 *)
  apply (rule_tac x="sa" in exI)
  apply (simp)
  (* 2 *)
  apply (simp add: in_traces)
  apply (elim conjE exE)
  apply (insert trace_last_noTick_or_Tick)
  apply (drule_tac x="sc" in spec)
  apply (elim disjE conjE exE)

   apply (subgoal_tac "noTick(sc --tr X)")
   apply (rotate_tac 4)
   apply (drule sym)
   apply (simp del: hide_tr_noTick)
   apply (simp)

   apply (simp)
   apply (rule_tac x="sd ^^^ sb" in exI)
   apply (simp)
   apply (rule disjI2)
   apply (rule_tac x="sd" in exI)
   apply (rule_tac x="sb" in exI)
   apply (simp)
done

(* --------------------------------------------------- *
         distribution hiding over interleaving
 * --------------------------------------------------- *)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Interleave_hide_dist: 
  "(P ||| Q) -- X =F[M,M] (P -- X) ||| (Q -- X)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Interleave_hide_dist)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim conjE exE)
 apply (simp)

 apply (rule_tac x="(Ev ` X Un Y) Int Xa" in exI)
 apply (rule_tac x="(Ev ` X Un Z) Int Xa" in exI)
 apply (intro conjI)

 (* 1 *)
  apply (force)

 (* 2 *)
  apply (force)

 (* 3 *)
  apply (rule_tac x="sb --tr X" in exI)
  apply (rule_tac x="t --tr X" in exI)
  apply (simp add: interleave_of_hide_tr_ex)
  apply (intro conjI)

   apply (force)

   apply (rule_tac x="sb" in exI)
   apply (simp)
   apply (subgoal_tac "Ev ` X Un (Ev ` X Un Y) Int Xa <= Y")
   apply (rule memF_F2)
   apply (simp)
   apply (simp)
   apply (force)

   apply (rule_tac x="t" in exI)
   apply (simp)
   apply (subgoal_tac "Ev ` X Un (Ev ` X Un Z) Int Xa <= Z")
   apply (rule memF_F2)
   apply (simp)
   apply (simp)
   apply (force)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim conjE exE)
 apply (simp add: interleave_of_hide_tr_ex)
 apply (elim conjE exE)
 apply (simp)
 apply (rule_tac x="v" in exI)
 apply (simp)
 apply (rule_tac x="Ev ` X Un Y" in exI)
 apply (rule_tac x="Ev ` X Un Z" in exI)
 apply (intro conjI)
  apply (force)
  apply (force)
  apply (force)
done


(* --------------------------------------------------- *
    distribution renaming over sequential composition
 * --------------------------------------------------- *)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Seq_compo_renaming_dist: 
  "(P ;; Q) [[r]] =F[M,M] (P [[r]]) ;; (Q [[r]])"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Seq_compo_renaming_dist)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim conjE exE disjE)
 apply (simp_all)

  (* 1 *)
 apply (rule disjI1)
 apply (simp add: ren_tr_noTick_left)
 apply (rule_tac x="sa" in exI)
 apply (simp add: ren_inv_insert_Tick)

  (* 2 *)
 apply (rule disjI2)
 apply (simp add: ren_tr_appt_decompo_left)
 apply (elim conjE exE)
 apply (simp)
 apply (rule_tac x="t1" in exI)
 apply (rule_tac x="t2" in exI)
 apply (simp)
 apply (rule conjI)
  apply (simp add: in_traces)
  apply (rule_tac x="sb ^^^ <Tick>" in exI)
  apply (simp add: ren_tr_noTick_left)

  apply (simp add: ren_tr_noTick_left)
  apply (rule_tac x="t" in exI)
  apply (simp)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE exE)
  (* 1 *)
  apply (rule_tac x="sa" in exI)
  apply (simp add: ren_inv_insert_Tick)
  apply (simp add: ren_tr_noTick_right)

  (* 2 *)
  apply (simp add: in_traces)
  apply (elim conjE exE)
  apply (simp add: ren_tr_appt_decompo_right)
  apply (elim conjE exE)
  apply (simp)
  apply (rule_tac x="s1 ^^^ sb" in exI)
  apply (simp)

  apply (rule conjI)
   apply (rule_tac x="s1" in exI)
   apply (rule_tac x="sb" in exI)
   apply (simp)

   apply (rule disjI2)
   apply (rule_tac x="s1" in exI)
   apply (rule_tac x="sb" in exI)
   apply (simp)
done




(* --------------------------------------------------- *
         distribution renaming over interleaving
 * --------------------------------------------------- *)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Interleave_renaming_dist: 
  "(P ||| Q) [[r]] =F[M,M] (P [[r]]) ||| (Q [[r]])"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Interleave_renaming_dist)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim conjE exE disjE)
  apply (case_tac "Tick ~: Y & Tick ~: Z")

  apply (rule_tac x="X" in exI)
  apply (rule_tac x="X" in exI)
  apply (simp)
  apply (insert interleave_of_ren_tr_only_if_all)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="r" in spec)
  apply (drule_tac x="s" in spec)
  apply (drule_tac x="sb" in spec)
  apply (drule_tac x="t" in spec)
  apply (simp)
  apply (elim conjE exE)
  apply (rule_tac x="s'" in exI)
  apply (rule_tac x="t'" in exI)
  apply (force)

  apply (subgoal_tac "Tick : X")

  apply (rule_tac x="(X-{Tick}) Un (Y Int {Tick})" in exI)
  apply (rule_tac x="(X-{Tick}) Un (Z Int {Tick})" in exI)
  apply (intro conjI)

   apply (force)
   apply (force)

   apply (drule_tac x="sa" in spec)
   apply (drule_tac x="r" in spec)
   apply (drule_tac x="s" in spec)
   apply (drule_tac x="sb" in spec)
   apply (drule_tac x="t" in spec)
   apply (simp)
   apply (elim conjE exE)
   apply (rule_tac x="s'" in exI)
   apply (rule_tac x="t'" in exI)
   apply (simp)
   apply (intro conjI)

    apply (rule_tac x="sb" in exI)
    apply (simp)
    apply (rule memF_F2)
    apply (simp)
    apply (force)

    apply (rule_tac x="t" in exI)
    apply (simp)
    apply (rule memF_F2)
    apply (simp)
    apply (force)

  apply (simp add: ren_inv_def)
  apply (force)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE exE)
 apply (erule rem_asmE)
 apply (insert interleave_of_ren_tr_if_all)
  apply (drule_tac x="s" in spec)
  apply (drule_tac x="r" in spec)
  apply (drule_tac x="sb" in spec)
  apply (drule_tac x="sc" in spec)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="t" in spec)
  apply (simp)
  apply (elim conjE exE)

   apply (rule_tac x="u" in exI)
   apply (simp)
   apply (rule_tac x="[[r]]inv Y" in exI)
   apply (rule_tac x="[[r]]inv Z" in exI)

  apply (simp add: ren_inv_def)
  apply (auto)
done

(* --------------------------------------------------- *
     distribution internal choice over prefix
 * --------------------------------------------------- *)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Act_prefix_dist:
  "a -> (P |~| Q) =F[M,M] (a -> P) |~| (a -> Q)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Act_prefix_dist)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (erule disjE)
  apply (force)

  apply (elim conjE exE disjE bexE)
  apply (force)
  apply (force)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE bexE exE)
  apply (simp)
  apply (simp)
  apply (force)
  apply (force)
done

lemma cspF_Int_choice_Act_prefix_delay:
  "(a -> P) |~| (a -> Q) =F[M,M] a -> (P |~| Q)"
apply (rule cspF_sym)
apply (simp add: cspF_Act_prefix_dist)
done

lemma cspF_Int_choice_Act_prefix_delay_eq:
  "a = b ==> (a -> P) |~| (b -> Q) =F[M,M] a -> (P |~| Q)"
apply (simp add: cspF_Int_choice_Act_prefix_delay)
done


(* --------------------------------------------------- *
     distribution internal choice over prefix choice
 * --------------------------------------------------- *)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_Ext_pre_choice_dist:
  "? x:X -> (Pf x |~| Qf x) =F[M,M] (? x:X -> Pf x) |~| (? x:X -> Qf x)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Ext_pre_choice_dist)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (erule disjE)
  apply (force)

  apply (elim conjE exE disjE bexE)
  apply (force)
  apply (force)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE bexE exE)
  apply (simp)
  apply (simp)
  apply (force)
  apply (force)
done

lemma cspF_Int_choice_Ext_pre_choice_delay:
  "(? x:X -> Pf x) |~| (? x:X -> Qf x)  =F[M,M] ? x:X -> (Pf x |~| Qf x)"
apply (rule cspF_sym)
apply (simp add: cspF_Ext_pre_choice_dist)
done

lemma cspF_Int_choice_Ext_pre_choice_delay_eq:
  "X = Y ==> (? x:X -> Pf x) |~| (? x:Y -> Qf x)  =F[M,M] ? x:X -> (Pf x |~| Qf x)"
apply (simp add: cspF_Int_choice_Ext_pre_choice_delay)
done

(*  replicated internal choice *)

lemma cspF_Act_prefix_delay_sum:
  "!! c:C .. (a -> Pf c) =F[M,M] 
   IF (sumset C = {}) THEN DIV ELSE (a -> (!! c:C .. (Pf c)))"
apply (rule cspF_rw_right)
apply (rule cspF_IF_split)
apply (case_tac "sumset C = {}")
apply (simp add: cspF_Rep_int_choice_DIV)
apply (simp)
apply (rule cspF_sym)
apply (simp add: cspF_Act_prefix_Dist)
done

lemma cspF_Ext_pre_choice_delay_sum:
  "!! c:C .. (? :X -> (Pf c)) =F[M,M] 
   IF (sumset C = {}) THEN DIV ELSE (? x:X -> (!! c:C .. (Pf c) x))"
apply (rule cspF_rw_right)
apply (rule cspF_IF_split)
apply (case_tac "sumset C = {}")
apply (simp add: cspF_Rep_int_choice_DIV)
apply (simp)
apply (rule cspF_sym)
apply (simp add: cspF_Ext_pre_choice_Dist)
done

lemma cspF_Act_prefix_delay_nat:
  "!nat n:N .. (a -> Pf n) =F[M,M] 
   IF (N = {}) THEN DIV ELSE (a -> (!nat n:N .. (Pf n)))"
apply (rule cspF_rw_right)
apply (rule cspF_IF_split)
apply (case_tac "N = {}")
apply (simp add: cspF_Rep_int_choice_DIV)
apply (simp)
apply (rule cspF_sym)
apply (simp add: cspF_Act_prefix_Dist)
done

lemma cspF_Ext_pre_choice_delay_nat:
  "!nat n:N .. (? :X -> (Pf n)) =F[M,M] 
   IF (N = {}) THEN DIV ELSE (? x:X -> (!nat n:N .. (Pf n) x))"
apply (rule cspF_rw_right)
apply (rule cspF_IF_split)
apply (case_tac "N = {}")
apply (simp add: cspF_Rep_int_choice_DIV)
apply (simp)
apply (rule cspF_sym)
apply (simp add: cspF_Ext_pre_choice_Dist)
done

lemma cspF_Act_prefix_delay_set:
  "!set X:Xs .. (a -> Pf X) =F[M,M] 
   IF (Xs = {}) THEN DIV ELSE (a -> (!set X:Xs .. (Pf X)))"
apply (rule cspF_rw_right)
apply (rule cspF_IF_split)
apply (case_tac "Xs = {}")
apply (simp add: cspF_Rep_int_choice_DIV)
apply (simp)
apply (rule cspF_sym)
apply (simp add: cspF_Act_prefix_Dist)
done

lemma cspF_Ext_pre_choice_delay_set:
  "!set Y:Xs .. (? :X -> (Pf Y)) =F[M,M] 
   IF (Xs = {}) THEN DIV ELSE (? x:X -> (!set Y:Xs .. (Pf Y) x))"
apply (rule cspF_rw_right)
apply (rule cspF_IF_split)
apply (case_tac "Xs = {}")
apply (simp add: cspF_Rep_int_choice_DIV)
apply (simp)
apply (rule cspF_sym)
apply (simp add: cspF_Ext_pre_choice_Dist)
done

lemma cspF_Act_prefix_delay_com:
  "! x:X .. (a -> Pf x) =F[M,M] 
   IF (X = {}) THEN DIV ELSE (a -> (! :X .. Pf))"
apply (rule cspF_rw_right)
apply (rule cspF_IF_split)
apply (case_tac "X = {}")
apply (simp add: cspF_Rep_int_choice_DIV)
apply (simp)
apply (rule cspF_sym)
apply (simp add: cspF_Act_prefix_Dist)
done

lemma cspF_Ext_pre_choice_delay_com:
  "! y:Y .. (? :X -> (Pf y)) =F[M,M] 
   IF (Y = {}) THEN DIV ELSE (? x:X -> (! y:Y .. (Pf y) x))"
apply (rule cspF_rw_right)
apply (rule cspF_IF_split)
apply (case_tac "Y = {}")
apply (simp add: cspF_Rep_int_choice_DIV)
apply (simp)
apply (rule cspF_sym)
apply (simp add: cspF_Ext_pre_choice_Dist)
done

lemma cspF_Act_prefix_delay_f:
  "inj f ==> 
   !<f> x:X .. (a -> Pf x) =F[M,M] 
   IF (X = {}) THEN DIV ELSE (a -> (!<f> :X .. Pf))"
apply (rule cspF_rw_right)
apply (rule cspF_IF_split)
apply (case_tac "X = {}")
apply (simp add: cspF_Rep_int_choice_DIV)
apply (simp)
apply (rule cspF_sym)
apply (simp add: cspF_Act_prefix_Dist)
done

lemma cspF_Ext_pre_choice_delay_f:
  "inj f ==> 
   !<f> y:Y .. (? :X -> (Pf y)) =F[M,M] 
   IF (Y = {}) THEN DIV ELSE (? x:X -> (!<f> y:Y .. (Pf y) x))"
apply (rule cspF_rw_right)
apply (rule cspF_IF_split)
apply (case_tac "Y = {}")
apply (simp add: cspF_Rep_int_choice_DIV)
apply (simp)
apply (rule cspF_sym)
apply (simp add: cspF_Ext_pre_choice_Dist)
done

lemmas cspF_choice_delay =
       cspF_Int_choice_Act_prefix_delay
       cspF_Int_choice_Ext_pre_choice_delay
       cspF_Act_prefix_delay_sum
       cspF_Ext_pre_choice_delay_sum
       cspF_Act_prefix_delay_nat
       cspF_Ext_pre_choice_delay_nat
       cspF_Act_prefix_delay_set
       cspF_Ext_pre_choice_delay_set
       cspF_Act_prefix_delay_com
       cspF_Ext_pre_choice_delay_com
       cspF_Act_prefix_delay_f
       cspF_Ext_pre_choice_delay_f

lemmas cspF_choice_delay_eq =
       cspF_Int_choice_Act_prefix_delay_eq
       cspF_Int_choice_Ext_pre_choice_delay_eq

(*********************************************************
                       P |[X,Y]| Q
 *********************************************************)

(* ---------- *
    |~| left
 * ---------- *)

lemma cspF_Alpha_Parallel_dist_l: 
  "(P1 |~| P2) |[X,Y]| Q =F[M,M]
   (P1 |[X,Y]| Q) |~| (P2 |[X,Y]| Q)"
apply (simp add: Alpha_parallel_def)

apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_dist)
apply (rule cspF_reflex)
apply (rule cspF_rw_left)
apply (rule cspF_dist)
apply (simp)
done

(* ---------- *
    |~| right
 * ---------- *)
lemma cspF_Alpha_Parallel_dist_r: 
  "P |[X,Y]| (Q1 |~| Q2) =F[M,M]
   (P |[X,Y]| Q1) |~| (P |[X,Y]| Q2)"
apply (simp add: Alpha_parallel_def)

apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_reflex)
apply (rule cspF_dist)
apply (rule cspF_rw_left)
apply (rule cspF_dist)
apply (simp)
done

(* ---------- *
    !! left
 * ---------- *)

lemma cspF_Alpha_Parallel_Dist_sum_l_nonempty: 
  "sumset C ~= {} ==>
     (!! :C .. Pf) |[X,Y]| Q =F[M,M]
     !! c:C .. (Pf c |[X,Y]| Q)"
apply (simp add: Alpha_parallel_def)

apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_Parallel_Dist_sum_l_nonempty)
apply (simp)
apply (rule cspF_reflex)
apply (rule cspF_rw_left)
apply (rule cspF_Parallel_Dist_sum_l_nonempty)
apply (simp)
apply (simp)
done

lemma cspF_Alpha_Parallel_Dist_sum_l: 
  "(!! :C .. Pf) |[X,Y]| Q =F[M,M]
   IF (sumset C={}) THEN (DIV |[X,Y]| Q) ELSE (!! c:C .. (Pf c |[X,Y]| Q))"
apply (case_tac "sumset C={}")
apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (rule cspF_decompo_Alpha_parallel)
apply (simp)+
apply (simp add: cspF_Rep_int_choice_empty)
apply (simp)

apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (rule cspF_Alpha_Parallel_Dist_sum_l_nonempty)
apply (simp)
done

(* ---------- *
    !! right
 * ---------- *)

lemma cspF_Alpha_Parallel_Dist_sum_r_nonempty: 
  "sumset C ~= {} ==>
     P |[X,Y]| (!! :C .. Qf) =F[M,M]
     !! c:C .. (P |[X,Y]| Qf c)"
apply (rule cspF_rw_left)
apply (rule cspF_Alpha_parallel_commut)
apply (rule cspF_rw_left)
apply (rule cspF_Alpha_Parallel_Dist_sum_l_nonempty, simp)
apply (rule cspF_decompo, simp)
apply (rule cspF_Alpha_parallel_commut)
done

lemma cspF_Alpha_Parallel_Dist_sum_r: 
  "P |[X,Y]| (!! :C .. Qf) =F[M,M]
   IF (sumset C={}) THEN (P |[X,Y]| DIV) ELSE (!! c:C .. (P |[X,Y]| Qf c))"
apply (case_tac "sumset C={}")
apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (rule cspF_decompo_Alpha_parallel)
apply (simp)+
apply (simp add: cspF_Rep_int_choice_empty)
apply (simp)

apply (rule cspF_rw_right)
apply (rule cspF_IF)
apply (rule cspF_Alpha_Parallel_Dist_sum_r_nonempty)
apply (simp)
done

(* ---------- *
   !nat left
 * ---------- *)

lemma cspF_Alpha_Parallel_Dist_nat_l_nonempty: 
  "N ~= {} ==>
     (!nat :N .. Pf) |[X,Y]| Q =F[M,M]
     !nat n:N .. (Pf n |[X,Y]| Q)"
by (simp add: Rep_int_choice_ss_def cspF_Alpha_Parallel_Dist_sum_l_nonempty)

(*** Dist ***)

lemma cspF_Alpha_Parallel_Dist_nat_l: 
  "(!nat :N .. Pf) |[X,Y]| Q =F[M,M]
   IF (N={}) THEN (DIV |[X,Y]| Q) ELSE (!nat n:N .. (Pf n |[X,Y]| Q))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_rw_left, rule cspF_Alpha_Parallel_Dist_sum_l, simp)

(* ---------- *
   !nat right
 * ---------- *)

lemma cspF_Alpha_Parallel_Dist_nat_r_nonempty: 
  "N ~= {} ==>
     P |[X,Y]| (!nat :N .. Qf) =F[M,M]
     !nat n:N .. (P |[X,Y]| Qf n)"
by (simp add: Rep_int_choice_ss_def cspF_Alpha_Parallel_Dist_sum_r_nonempty)

(*** Dist ***)

lemma cspF_Alpha_Parallel_Dist_nat_r: 
  "P |[X,Y]| (!nat :N .. Qf) =F[M,M]
   IF (N={}) THEN (P |[X,Y]| DIV) ELSE (!nat n:N .. (P |[X,Y]| Qf n))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_rw_left, rule cspF_Alpha_Parallel_Dist_sum_r, simp)

(* ---------- *
   !set left
 * ---------- *)

lemma cspF_Alpha_Parallel_Dist_set_l_nonempty: 
  "Xs ~= {} ==>
     (!set :Xs .. Pf) |[Y,Z]| Q =F[M,M]
     !set X:Xs .. (Pf X |[Y,Z]| Q)"
by (simp add: Rep_int_choice_ss_def cspF_Alpha_Parallel_Dist_sum_l_nonempty)

(*** Dist ***)

lemma cspF_Alpha_Parallel_Dist_set_l: 
  "(!set :Xs .. Pf) |[Y,Z]| Q =F[M,M]
   IF (Xs={}) THEN (DIV |[Y,Z]| Q) ELSE (!set X:Xs .. (Pf X |[Y,Z]| Q))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_rw_left, rule cspF_Alpha_Parallel_Dist_sum_l, simp)

(* ---------- *
   !set right
 * ---------- *)

lemma cspF_Alpha_Parallel_Dist_set_r_nonempty: 
  "Xs ~= {} ==>
     P |[Y,Z]| (!set :Xs .. Qf) =F[M,M]
     !set X:Xs .. (P |[Y,Z]| Qf X)"
by (simp add: Rep_int_choice_ss_def cspF_Alpha_Parallel_Dist_sum_r_nonempty)

(*** Dist ***)

lemma cspF_Alpha_Parallel_Dist_set_r: 
  "P |[Y,Z]| (!set :Xs .. Qf) =F[M,M]
   IF (Xs={}) THEN (P |[Y,Z]| DIV) ELSE (!set X:Xs .. (P |[Y,Z]| Qf X))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspF_rw_left, rule cspF_Alpha_Parallel_Dist_sum_r, simp)

(* ---------- *
     ! left
 * ---------- *)

lemma cspF_Alpha_Parallel_Dist_com_l_nonempty: 
  "A ~= {}
   ==> (! :A .. Pf) |[X,Y]| Q =F[M,M] ! x:A .. (Pf x |[X,Y]| Q)"
by (simp add: Rep_int_choice_com_def cspF_Alpha_Parallel_Dist_set_l_nonempty)

lemma cspF_Alpha_Parallel_Dist_com_l: 
  "(! :A .. Pf) |[X,Y]| Q =F[M,M]
   IF (A ={}) THEN (DIV |[X,Y]| Q) ELSE (! x:A .. (Pf x |[X,Y]| Q))"
apply (simp add: Rep_int_choice_com_def)
by (rule cspF_rw_left, rule cspF_Alpha_Parallel_Dist_set_l, simp)

(* ---------- *
     ! right
 * ---------- *)

lemma cspF_Alpha_Parallel_Dist_com_r_nonempty: 
  "A ~= {}
   ==> P |[X,Y]| (! :A .. Qf) =F[M,M] ! x:A .. (P |[X,Y]| Qf x)"
by (simp add: Rep_int_choice_com_def cspF_Alpha_Parallel_Dist_set_r_nonempty)

lemma cspF_Alpha_Parallel_Dist_com_r: 
  "P |[X,Y]| (! :A .. Qf) =F[M,M] 
   IF (A ={}) THEN (P |[X,Y]| DIV) ELSE (! x:A .. (P |[X,Y]| Qf x))"
apply (simp add: Rep_int_choice_com_def)
by (rule cspF_rw_left, rule cspF_Alpha_Parallel_Dist_set_r, simp)

(* ---------- *
   !<f> left
 * ---------- *)

lemma cspF_Alpha_Parallel_Dist_f_l_nonempty: 
  "[| inj f ; A ~= {} |]
   ==> (!<f> :A .. Pf) |[X,Y]| Q =F[M,M] !<f> x:A .. (Pf x |[X,Y]| Q)"
by (simp add: Rep_int_choice_f_def cspF_Alpha_Parallel_Dist_com_l_nonempty)

lemma cspF_Alpha_Parallel_Dist_f_l: 
  "(!<f> :A .. Pf) |[X,Y]| Q =F[M,M]
   IF (A ={}) THEN (DIV |[X,Y]| Q) ELSE (!<f> x:A .. (Pf x |[X,Y]| Q))"
apply (simp add: Rep_int_choice_f_def)
by (rule cspF_rw_left, rule cspF_Alpha_Parallel_Dist_com_l, simp)

lemma cspF_Alpha_Parallel_Dist_f_r_nonempty: 
  "[| inj f ; A ~= {} |]
   ==> P |[X,Y]| (!<f> :A .. Qf) =F[M,M] !<f> x:A .. (P |[X,Y]| Qf x)"
by (simp add: Rep_int_choice_f_def cspF_Alpha_Parallel_Dist_com_r_nonempty)

lemma cspF_Alpha_Parallel_Dist_f_r: 
  "P |[X,Y]| (!<f> :A .. Qf) =F[M,M] 
   IF (A ={}) THEN (P |[X,Y]| DIV) ELSE (!<f> x:A .. (P |[X,Y]| Qf x))"
apply (simp add: Rep_int_choice_f_def)
by (rule cspF_rw_left, rule cspF_Alpha_Parallel_Dist_com_r, simp)

lemmas cspF_dist_Alpha_Parallel =
       cspF_Alpha_Parallel_dist_l
       cspF_Alpha_Parallel_dist_r 

lemmas cspF_Dist_Alpha_Parallel =
      cspF_Alpha_Parallel_Dist_sum_l 
      cspF_Alpha_Parallel_Dist_sum_r 
      cspF_Alpha_Parallel_Dist_nat_l 
      cspF_Alpha_Parallel_Dist_nat_r 
      cspF_Alpha_Parallel_Dist_set_l 
      cspF_Alpha_Parallel_Dist_set_r 
      cspF_Alpha_Parallel_Dist_com_l 
      cspF_Alpha_Parallel_Dist_com_r 
      cspF_Alpha_Parallel_Dist_f_l 
      cspF_Alpha_Parallel_Dist_f_r 

lemmas cspF_Dist_Alpha_Parallel_nonempty =
      cspF_Alpha_Parallel_Dist_sum_l_nonempty 
      cspF_Alpha_Parallel_Dist_sum_r_nonempty 
      cspF_Alpha_Parallel_Dist_nat_l_nonempty 
      cspF_Alpha_Parallel_Dist_nat_r_nonempty 
      cspF_Alpha_Parallel_Dist_set_l_nonempty 
      cspF_Alpha_Parallel_Dist_set_r_nonempty 
      cspF_Alpha_Parallel_Dist_com_l_nonempty
      cspF_Alpha_Parallel_Dist_com_r_nonempty 
      cspF_Alpha_Parallel_Dist_f_l_nonempty 
      cspF_Alpha_Parallel_Dist_f_r_nonempty 



(****************** to add them again ******************)

end
