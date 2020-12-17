           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005  (modified)   |
            |              September 2005  (modified)   |
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

theory CSP_T_law_dist
imports CSP_T_law_basic CSP_T_law_alpha_par
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

lemma cspT_Ext_choice_dist_l: 
  "(P1 |~| P2) [+] Q =T[M,M]
   (P1 [+] Q) |~| (P2 [+] Q)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces, fast)+
done

(*********************************************************
                dist law for Ext_choice (r)
 *********************************************************)

lemma cspT_Ext_choice_dist_r: 
  "P [+] (Q1 |~| Q2) =T[M,M]
   (P [+] Q1) |~| (P [+] Q2)"
apply (rule cspT_rw_left)
apply (rule cspT_commut)
apply (rule cspT_rw_left)
apply (rule cspT_Ext_choice_dist_l)
apply (rule cspT_decompo)
apply (rule cspT_commut)+
done

(*********************************************************
                dist law for Parallel (l)
 *********************************************************)

lemma cspT_Parallel_dist_l: 
  "(P1 |~| P2) |[X]| Q =T[M,M]
   (P1 |[X]| Q) |~| (P2 |[X]| Q)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces, fast)+
done

(*********************************************************
                dist law for Parallel (r)
 *********************************************************)

lemma cspT_Parallel_dist_r: 
  "P |[X]| (Q1 |~| Q2) =T[M,M]
   (P |[X]| Q1) |~| (P |[X]| Q2)"
apply (rule cspT_rw_left)
apply (rule cspT_commut)
apply (rule cspT_rw_left)
apply (rule cspT_Parallel_dist_l)
apply (rule cspT_decompo)
apply (rule cspT_commut)+
done

(*********************************************************
                dist law for Hiding
 *********************************************************)

lemma cspT_Hiding_dist: 
  "(P1 |~| P2) -- X =T[M,M]
   (P1 -- X) |~| (P2 -- X)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces, fast)+
done

(*********************************************************
               dist law for Renaming
 *********************************************************)

lemma cspT_Renaming_dist: 
  "(P1 |~| P2) [[r]] =T[M,M]
   (P1 [[r]]) |~| (P2 [[r]])"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces, fast)+
done

(*********************************************************
         dist law for Sequential composition
 *********************************************************)

lemma cspT_Seq_compo_dist: 
  "(P1 |~| P2) ;; Q =T[M,M]
   (P1 ;; Q) |~| (P2 ;; Q)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces, fast)+
done

(*********************************************************
               dist law for Depth_rest
 *********************************************************)

lemma cspT_Depth_rest_dist: 
  "(P1 |~| P2) |. n =T[M,M]
   (P1 |. n) |~| (P2 |. n)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces)
apply (rule, simp add: in_traces)
apply (force)
done

(*********************************************************
               dist law for Rep_int_choice
 *********************************************************)

lemma cspT_Rep_int_choice_sum_dist:
  "!! c:C .. (Pf c |~| Qf c) =T[M,M] (!! c:C .. Pf c) |~| (!! c:C .. Qf c)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces, fast)+
done

lemma cspT_Rep_int_choice_nat_dist:
  "!nat n:N .. (Pf n |~| Qf n) =T[M,M] (!nat n:N .. Pf n) |~| (!nat n:N .. Qf n)"
by (simp add: Rep_int_choice_ss_def cspT_Rep_int_choice_sum_dist)

lemma cspT_Rep_int_choice_set_dist:
  "!set X:Xs .. (Pf X |~| Qf X) =T[M,M] (!set X:Xs .. Pf X) |~| (!set X:Xs .. Qf X)"
by (simp add: Rep_int_choice_ss_def cspT_Rep_int_choice_sum_dist)

lemma cspT_Rep_int_choice_com_dist:
  "! a:X .. (Pf a |~| Qf a) =T[M,M] (! a:X .. Pf a) |~| (! a:X .. Qf a)"
by (simp add: Rep_int_choice_com_def cspT_Rep_int_choice_set_dist)

lemma cspT_Rep_int_choice_f_dist:
  "inj f ==>
   !<f> a:X .. (Pf a |~| Qf a) =T[M,M] (!<f> a:X .. Pf a) |~| (!<f> a:X .. Qf a)"
by (simp add: Rep_int_choice_f_def cspT_Rep_int_choice_com_dist)

lemmas cspT_Rep_int_choice_dist =
       cspT_Rep_int_choice_sum_dist
       cspT_Rep_int_choice_nat_dist
       cspT_Rep_int_choice_set_dist
       cspT_Rep_int_choice_com_dist
       cspT_Rep_int_choice_f_dist

(*********************************************************
                     dist laws
 *********************************************************)

lemmas cspT_dist = cspT_Ext_choice_dist_l cspT_Ext_choice_dist_r
                   cspT_Parallel_dist_l   cspT_Parallel_dist_r
                   cspT_Hiding_dist       cspT_Renaming_dist
                   cspT_Seq_compo_dist    cspT_Depth_rest_dist
                   cspT_Rep_int_choice_dist

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

lemma cspT_Ext_choice_Dist_sum_l_nonempty: 
  "sumset C ~= {} ==> (!! :C .. Pf) [+] Q =T[M,M]
                      !! c:C .. (Pf c [+] Q)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces, fast)+
done

(*** Dist ***)

lemma cspT_Ext_choice_Dist_sum_l: 
  "(!! :C .. Pf) [+] Q =T[M,M]
   IF (sumset C={}) THEN (DIV [+] Q) ELSE (!! c:C .. (Pf c [+] Q))"
apply (case_tac "sumset C={}")
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (rule cspT_decompo)
apply (rule cspT_Rep_int_choice_empty)
apply (simp_all)

apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (rule cspT_Ext_choice_Dist_sum_l_nonempty)
apply (simp)
done

(*********************************************************
                Dist_sum law for Ext_choice (r)
 *********************************************************)

lemma cspT_Ext_choice_Dist_sum_r_nonempty: 
  "sumset C ~= {} ==> P [+] (!! :C .. Qf) =T[M,M]
               !! c:C .. (P [+] Qf c)"
apply (rule cspT_rw_left)
apply (rule cspT_commut)
apply (rule cspT_rw_left)
apply (rule cspT_Ext_choice_Dist_sum_l_nonempty, simp)
apply (rule cspT_decompo, simp)
apply (rule cspT_commut)
done

(*** Dist ***)

lemma cspT_Ext_choice_Dist_sum_r: 
  "P [+] (!! :C .. Qf) =T[M,M]
   IF (sumset C={}) THEN (P [+] DIV) ELSE (!! c:C .. (P [+] Qf c))"
apply (case_tac "sumset C={}")
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (rule cspT_decompo)
apply (simp)
apply (simp add: cspT_Rep_int_choice_empty)

apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (rule cspT_Ext_choice_Dist_sum_r_nonempty)
apply (simp)
done

(*********************************************************
                Dist_sum law for Parallel (l)
 *********************************************************)

lemma cspT_Parallel_Dist_sum_l_nonempty: 
  "sumset C ~= {} ==>
     (!! :C .. Pf) |[X]| Q =T[M,M]
     !! c:C .. (Pf c |[X]| Q)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

 apply (rule, simp add: in_traces)
 apply (elim disjE conjE exE bexE)
  apply (subgoal_tac "EX c. c: sumset C")
  apply (elim exE)
  apply (rule disjI2)
  apply (rule_tac x="c" in bexI)
  apply (simp)
  apply (rule_tac x="<>" in exI)
  apply (rule_tac x="ta" in exI)
  apply (simp)
  apply (simp)
  apply (fast)
  (* *)
  apply (rule disjI2)
  apply (rule_tac x="c" in bexI)
  apply (fast)
  apply (simp)

 apply (rule, simp add: in_traces)
 apply (elim disjE conjE exE bexE)
  apply (rule_tac x="<>" in exI)
  apply (rule_tac x="<>" in exI)
  apply (simp)
  apply (fast)
done

(*** Dist ***)

lemma cspT_Parallel_Dist_sum_l: 
  "(!! :C .. Pf) |[X]| Q =T[M,M]
   IF (sumset C={}) THEN (DIV |[X]| Q) ELSE (!! c:C .. (Pf c |[X]| Q))"
apply (case_tac "sumset C={}")
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (rule cspT_decompo)
apply (simp)
apply (simp add: cspT_Rep_int_choice_empty)
apply (simp)

apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (rule cspT_Parallel_Dist_sum_l_nonempty)
apply (simp)
done

(*********************************************************
                Dist_sum law for Parallel (r)
 *********************************************************)

lemma cspT_Parallel_Dist_sum_r_nonempty: 
  "sumset C ~= {} ==>
     P |[X]| (!! :C .. Qf) =T[M,M]
     !! c:C .. (P |[X]| Qf c)"
apply (rule cspT_rw_left)
apply (rule cspT_commut)
apply (rule cspT_rw_left)
apply (rule cspT_Parallel_Dist_sum_l_nonempty, simp)
apply (rule cspT_decompo, simp)
apply (rule cspT_commut)
done

(*** Dist ***)

lemma cspT_Parallel_Dist_sum_r: 
  "P |[X]| (!! :C .. Qf) =T[M,M]
   IF (sumset C={}) THEN (P |[X]| DIV) ELSE (!! c:C .. (P |[X]| Qf c))"
apply (case_tac "sumset C={}")
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (rule cspT_decompo)
apply (simp)
apply (simp)
apply (simp add: cspT_Rep_int_choice_empty)

apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (rule cspT_Parallel_Dist_sum_r_nonempty)
apply (simp)
done

(*********************************************************
                Dist_sum law for Hiding
 *********************************************************)

lemma cspT_Hiding_Dist_sum: 
  "(!! :C .. Pf) -- X =T[M,M]
   !! c:C .. (Pf c -- X)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

 apply (rule, simp add: in_traces)
 apply (elim disjE conjE exE, simp, fast)

 apply (rule, simp add: in_traces)
 apply (elim disjE conjE exE bexE)
 apply (rule_tac x="<>" in exI, simp)
 apply (rule_tac x="s" in exI, fast)
done

(*********************************************************
                Dist_sum law for Renaming
 *********************************************************)

lemma cspT_Renaming_Dist_sum: 
  "(!! :C .. Pf) [[r]] =T[M,M]
   !! c:C .. (Pf c [[r]])"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

 apply (rule, simp add: in_traces)
 apply (elim disjE conjE exE, simp, fast)
 apply (rule, simp add: in_traces)
 apply (elim disjE conjE exE, simp, fast)
done

(*********************************************************
          Dist_sum law for Sequential composition
 *********************************************************)

lemma cspT_Seq_compo_Dist_sum: 
  "(!! :C .. Pf) ;; Q =T[M,M]
   !! c:C .. (Pf c ;; Q)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

 apply (rule, simp add: in_traces)
 apply (elim disjE conjE exE bexE)
 apply (simp)
 apply (fast)
 apply (force)
 apply (rule disjI2)
 apply (rule_tac x="c" in bexI)
 apply (force)
 apply (simp)

 apply (rule, simp add: in_traces)
 apply (elim disjE conjE exE bexE)
 apply (rule disjI1)
 apply (rule_tac x="<>" in exI, simp)
 apply (fast)
 apply (fast)
done

(*********************************************************
                Dist_sum law for Depth_rest
 *********************************************************)

lemma cspT_Depth_rest_Dist_sum: 
  "(!! :C .. Pf) |. m =T[M,M]
   !! c:C .. (Pf c |. m)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

 apply (rule, simp add: in_traces)
 apply (rule, simp add: in_traces)
 apply (force)
done

(*********************************************************
                     Dist_sum laws
 *********************************************************)

lemmas cspT_Dist_sum = cspT_Ext_choice_Dist_sum_l cspT_Ext_choice_Dist_sum_r
                        cspT_Parallel_Dist_sum_l   cspT_Parallel_Dist_sum_r
                        cspT_Hiding_Dist_sum       cspT_Renaming_Dist_sum
                        cspT_Seq_compo_Dist_sum    cspT_Depth_rest_Dist_sum

lemmas cspT_Dist_sum_nonempty = 
       cspT_Ext_choice_Dist_sum_l_nonempty cspT_Ext_choice_Dist_sum_r_nonempty
       cspT_Parallel_Dist_sum_l_nonempty   cspT_Parallel_Dist_sum_r_nonempty
       cspT_Hiding_Dist_sum       cspT_Renaming_Dist_sum
       cspT_Seq_compo_Dist_sum    cspT_Depth_rest_Dist_sum

(*****************************************************************

      distribution over replicated internal choice

         1. (!nat :C .. Pf) [+] Q
         2. Q [+] (!nat :C .. Pf)
         3. (!nat :C .. Pf) |[X]| Q
         4. Q |[X]| (!nat :C .. Pf)
         5. (!nat :C .. Pf) -- X
         6. (!nat :C .. Pf) [[r]]
         7. (!nat :C .. Pf) |. n

 *****************************************************************)

(*********************************************************
                Rep_dist law for Ext_choice (l)
 *********************************************************)

lemma cspT_Ext_choice_Dist_nat_l_nonempty: 
  "N ~= {} ==> (!nat :N .. Pf) [+] Q =T[M,M]
               !nat n:N .. (Pf n [+] Q)"
by (simp add: Rep_int_choice_ss_def cspT_Dist_sum_nonempty)

(*** Dist ***)

lemma cspT_Ext_choice_Dist_nat_l: 
  "(!nat :N .. Pf) [+] Q =T[M,M]
   IF (N={}) THEN (DIV [+] Q) ELSE (!nat n:N .. (Pf n [+] Q))"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Dist_sum)
apply (simp)
done

(*********************************************************
                Dist_nat law for Ext_choice (r)
 *********************************************************)

lemma cspT_Ext_choice_Dist_nat_r_nonempty: 
  "N ~= {} ==> P [+] (!nat :N .. Qf) =T[M,M]
               !nat n:N .. (P [+] Qf n)"
by (simp add: Rep_int_choice_ss_def cspT_Dist_sum_nonempty)

(*** Dist ***)

lemma cspT_Ext_choice_Dist_nat_r: 
  "P [+] (!nat :N .. Qf) =T[M,M]
   IF (N={}) THEN (P [+] DIV) ELSE (!nat n:N .. (P [+] Qf n))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_rw_left, rule cspT_Dist_sum, simp)

(*********************************************************
                Dist_nat law for Parallel (l)
 *********************************************************)

lemma cspT_Parallel_Dist_nat_l_nonempty: 
  "N ~= {} ==>
     (!nat :N .. Pf) |[X]| Q =T[M,M]
     !nat n:N .. (Pf n |[X]| Q)"
by (simp add: Rep_int_choice_ss_def cspT_Dist_sum_nonempty)

(*** Dist ***)

lemma cspT_Parallel_Dist_nat_l: 
  "(!nat :N .. Pf) |[X]| Q =T[M,M]
   IF (N={}) THEN (DIV |[X]| Q) ELSE (!nat n:N .. (Pf n |[X]| Q))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_rw_left, rule cspT_Dist_sum, simp)

(*********************************************************
                Dist_nat law for Parallel (r)
 *********************************************************)

lemma cspT_Parallel_Dist_nat_r_nonempty: 
  "N ~= {} ==>
     P |[X]| (!nat :N .. Qf) =T[M,M]
     !nat n:N .. (P |[X]| Qf n)"
by (simp add: Rep_int_choice_ss_def cspT_Dist_sum_nonempty)

(*** Dist ***)

lemma cspT_Parallel_Dist_nat_r: 
  "P |[X]| (!nat :N .. Qf) =T[M,M]
   IF (N={}) THEN (P |[X]| DIV) ELSE (!nat n:N .. (P |[X]| Qf n))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_rw_left, rule cspT_Dist_sum, simp)

(*********************************************************
                Dist_nat law for Hiding
 *********************************************************)

lemma cspT_Hiding_Dist_nat: 
  "(!nat :N .. Pf) -- X =T[M,M]
   !nat n:N .. (Pf n -- X)"
by (simp add: Rep_int_choice_ss_def cspT_Dist_sum)

(*********************************************************
                Dist_nat law for Renaming
 *********************************************************)

lemma cspT_Renaming_Dist_nat: 
  "(!nat :N .. Pf) [[r]] =T[M,M]
   !nat n:N .. (Pf n [[r]])"
by (simp add: Rep_int_choice_ss_def cspT_Dist_sum)

(*********************************************************
          Dist_nat law for Sequential composition
 *********************************************************)

lemma cspT_Seq_compo_Dist_nat: 
  "(!nat :N .. Pf) ;; Q =T[M,M]
   !nat n:N .. (Pf n ;; Q)"
by (simp add: Rep_int_choice_ss_def cspT_Dist_sum)

(*********************************************************
                Dist_nat law for Depth_rest
 *********************************************************)

lemma cspT_Depth_rest_Dist_nat: 
  "(!nat :N .. Pf) |. m =T[M,M]
   !nat n:N .. (Pf n |. m)"
by (simp add: Rep_int_choice_ss_def cspT_Dist_sum)

(*********************************************************
                     Dist_nat laws
 *********************************************************)

lemmas cspT_Dist_nat = cspT_Ext_choice_Dist_nat_l cspT_Ext_choice_Dist_nat_r
                        cspT_Parallel_Dist_nat_l   cspT_Parallel_Dist_nat_r
                        cspT_Hiding_Dist_nat       cspT_Renaming_Dist_nat
                        cspT_Seq_compo_Dist_nat    cspT_Depth_rest_Dist_nat

lemmas cspT_Dist_nat_nonempty = 
       cspT_Ext_choice_Dist_nat_l_nonempty cspT_Ext_choice_Dist_nat_r_nonempty
       cspT_Parallel_Dist_nat_l_nonempty   cspT_Parallel_Dist_nat_r_nonempty
       cspT_Hiding_Dist_nat       cspT_Renaming_Dist_nat
       cspT_Seq_compo_Dist_nat    cspT_Depth_rest_Dist_nat

(*****************************************************************

      distribution over replicated internal choice

         1. (!set :C .. Pf) [+] Q
         2. Q [+] (!set :C .. Pf)
         3. (!set :C .. Pf) |[X]| Q
         4. Q |[X]| (!set :C .. Pf)
         5. (!set :C .. Pf) -- X
         6. (!set :C .. Pf) [[r]]
         7. (!set :C .. Pf) |. n

 *****************************************************************)

(*********************************************************
                Rep_dist law for Ext_choice (l)
 *********************************************************)

lemma cspT_Ext_choice_Dist_set_l_nonempty: 
  "Xs ~= {} ==> (!set :Xs .. Pf) [+] Q =T[M,M]
               !set X:Xs .. (Pf X [+] Q)"
by (simp add: Rep_int_choice_ss_def cspT_Dist_sum_nonempty)

(*** Dist ***)

lemma cspT_Ext_choice_Dist_set_l: 
  "(!set :Xs .. Pf) [+] Q =T[M,M]
   IF (Xs={}) THEN (DIV [+] Q) ELSE (!set X:Xs .. (Pf X [+] Q))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_rw_left, rule cspT_Dist_sum, simp)

(*********************************************************
                Dist_set law for Ext_choice (r)
 *********************************************************)

lemma cspT_Ext_choice_Dist_set_r_nonempty: 
  "Xs ~= {} ==> P [+] (!set :Xs .. Qf) =T[M,M]
               !set X:Xs .. (P [+] Qf X)"
by (simp add: Rep_int_choice_ss_def cspT_Dist_sum_nonempty)

(*** Dist ***)

lemma cspT_Ext_choice_Dist_set_r: 
  "P [+] (!set :Xs .. Qf) =T[M,M]
   IF (Xs={}) THEN (P [+] DIV) ELSE (!set X:Xs .. (P [+] Qf X))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_rw_left, rule cspT_Dist_sum, simp)

(*********************************************************
                Dist_set law for Parallel (l)
 *********************************************************)

lemma cspT_Parallel_Dist_set_l_nonempty: 
  "Xs ~= {} ==>
     (!set :Xs .. Pf) |[Y]| Q =T[M,M]
     !set X:Xs .. (Pf X |[Y]| Q)"
by (simp add: Rep_int_choice_ss_def cspT_Dist_sum_nonempty)

(*** Dist ***)

lemma cspT_Parallel_Dist_set_l: 
  "(!set :Xs .. Pf) |[Y]| Q =T[M,M]
   IF (Xs={}) THEN (DIV |[Y]| Q) ELSE (!set X:Xs .. (Pf X |[Y]| Q))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_rw_left, rule cspT_Dist_sum, simp)

(*********************************************************
                Dist_set law for Parallel (r)
 *********************************************************)

lemma cspT_Parallel_Dist_set_r_nonempty: 
  "Xs ~= {} ==>
     P |[Y]| (!set :Xs .. Qf) =T[M,M]
     !set X:Xs .. (P |[Y]| Qf X)"
by (simp add: Rep_int_choice_ss_def cspT_Dist_sum_nonempty)

(*** Dist ***)

lemma cspT_Parallel_Dist_set_r: 
  "P |[Y]| (!set :Xs .. Qf) =T[M,M]
   IF (Xs={}) THEN (P |[Y]| DIV) ELSE (!set X:Xs .. (P |[Y]| Qf X))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_rw_left, rule cspT_Dist_sum, simp)

(*********************************************************
                Dist_set law for Hiding
 *********************************************************)

lemma cspT_Hiding_Dist_set: 
  "(!set :Xs .. Pf) -- Y =T[M,M]
   !set X:Xs .. (Pf X -- Y)"
by (simp add: Rep_int_choice_ss_def cspT_Dist_sum)

(*********************************************************
                Dist_set law for Renaming
 *********************************************************)

lemma cspT_Renaming_Dist_set: 
  "(!set :Xs .. Pf) [[r]] =T[M,M]
   !set X:Xs .. (Pf X [[r]])"
by (simp add: Rep_int_choice_ss_def cspT_Dist_sum)

(*********************************************************
          Dist_set law for Sequential composition
 *********************************************************)

lemma cspT_Seq_compo_Dist_set: 
  "(!set :Xs .. Pf) ;; Q =T[M,M]
   !set X:Xs .. (Pf X ;; Q)"
by (simp add: Rep_int_choice_ss_def cspT_Dist_sum)

(*********************************************************
                Dist_set law for Depth_rest
 *********************************************************)

lemma cspT_Depth_rest_Dist_set: 
  "(!set :Xs .. Pf) |. m =T[M,M]
   !set X:Xs .. (Pf X |. m)"
by (simp add: Rep_int_choice_ss_def cspT_Dist_sum)

(*********************************************************
                     Dist_set laws
 *********************************************************)

lemmas cspT_Dist_set = cspT_Ext_choice_Dist_set_l cspT_Ext_choice_Dist_set_r
                        cspT_Parallel_Dist_set_l   cspT_Parallel_Dist_set_r
                        cspT_Hiding_Dist_set       cspT_Renaming_Dist_set
                        cspT_Seq_compo_Dist_set    cspT_Depth_rest_Dist_set

lemmas cspT_Dist_set_nonempty = 
       cspT_Ext_choice_Dist_set_l_nonempty cspT_Ext_choice_Dist_set_r_nonempty
       cspT_Parallel_Dist_set_l_nonempty   cspT_Parallel_Dist_set_r_nonempty
       cspT_Hiding_Dist_set       cspT_Renaming_Dist_set
       cspT_Seq_compo_Dist_set    cspT_Depth_rest_Dist_set

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

lemma cspT_Ext_choice_Dist_com_l_nonempty: 
  "X ~= {}
   ==> (! :X .. Pf) [+] Q =T[M,M] ! x:X .. (Pf x [+] Q)"
by (simp add: Rep_int_choice_com_def cspT_Dist_set_nonempty)

lemma cspT_Ext_choice_Dist_com_r_nonempty: 
  "X ~= {}
   ==> P [+] (! :X .. Qf) =T[M,M] ! x:X .. (P [+] Qf x)"
by (simp add: Rep_int_choice_com_def cspT_Dist_set_nonempty)

lemma cspT_Parallel_Dist_com_l_nonempty: 
  "Y ~= {}
   ==> (! :Y .. Pf) |[X]| Q =T[M,M] ! x:Y .. (Pf x |[X]| Q)"
by (simp add: Rep_int_choice_com_def cspT_Dist_set_nonempty)

lemma cspT_Parallel_Dist_com_r_nonempty: 
  "Y ~= {}
   ==> P |[X]| (! :Y .. Qf) =T[M,M] ! x:Y .. (P |[X]| Qf x)"
by (simp add: Rep_int_choice_com_def cspT_Dist_set_nonempty)

lemma cspT_Ext_choice_Dist_com_l: 
  "(! :X .. Pf) [+] Q =T[M,M] 
   IF (X ={}) THEN (DIV [+] Q) ELSE (! x:X .. (Pf x [+] Q))"
apply (simp add: Rep_int_choice_com_def)
by (rule cspT_rw_left, rule cspT_Dist_set, simp)

lemma cspT_Ext_choice_Dist_com_r: 
  "P [+] (! :X .. Qf) =T[M,M]
   IF (X ={}) THEN (P [+] DIV) ELSE (! x:X .. (P [+] Qf x))"
apply (simp add: Rep_int_choice_com_def)
by (rule cspT_rw_left, rule cspT_Dist_set, simp)

lemma cspT_Parallel_Dist_com_l: 
  "(! :Y .. Pf) |[X]| Q =T[M,M]
   IF (Y ={}) THEN (DIV |[X]| Q) ELSE (! x:Y .. (Pf x |[X]| Q))"
apply (simp add: Rep_int_choice_com_def)
by (rule cspT_rw_left, rule cspT_Dist_set, simp)

lemma cspT_Parallel_Dist_com_r: 
  "P |[X]| (! :Y .. Qf) =T[M,M] 
   IF (Y ={}) THEN (P |[X]| DIV) ELSE (! x:Y .. (P |[X]| Qf x))"
apply (simp add: Rep_int_choice_com_def)
by (rule cspT_rw_left, rule cspT_Dist_set, simp)

lemma cspT_Hiding_Dist_com: 
  "(! :Y .. Pf) -- X =T[M,M] ! x:Y .. (Pf x -- X)"
by (simp add: Rep_int_choice_com_def cspT_Dist_set_nonempty)

lemma cspT_Renaming_Dist_com: 
  "(! :X .. Pf) [[r]] =T[M,M] ! x:X .. (Pf x [[r]])"
by (simp add: Rep_int_choice_com_def cspT_Dist_set_nonempty)

lemma cspT_Seq_compo_Dist_com:
  "(! :X .. Pf) ;; Q =T[M,M] ! x:X .. (Pf x ;; Q)"
by (simp add: Rep_int_choice_com_def cspT_Dist_set_nonempty)

lemma cspT_Depth_rest_Dist_com: 
  "(! :X .. Pf) |. n =T[M,M] ! x:X .. (Pf x |. n)"
by (simp add: Rep_int_choice_com_def cspT_Dist_set_nonempty)

(*********************************************************
                     Dist laws
 *********************************************************)

lemmas cspT_Dist_com = cspT_Ext_choice_Dist_com_l cspT_Ext_choice_Dist_com_r
                           cspT_Parallel_Dist_com_l   cspT_Parallel_Dist_com_r
                           cspT_Hiding_Dist_com       cspT_Renaming_Dist_com
                           cspT_Seq_compo_Dist_com    cspT_Depth_rest_Dist_com

lemmas cspT_Dist_com_nonempty = 
       cspT_Ext_choice_Dist_com_l_nonempty cspT_Ext_choice_Dist_com_r_nonempty
       cspT_Parallel_Dist_com_l_nonempty   cspT_Parallel_Dist_com_r_nonempty
       cspT_Hiding_Dist_com       cspT_Renaming_Dist_com
       cspT_Seq_compo_Dist_com    cspT_Depth_rest_Dist_com

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

lemma cspT_Ext_choice_Dist_f_l_nonempty: 
  "[| inj f ; X ~= {} |]
   ==> (!<f> :X .. Pf) [+] Q =T[M,M] !<f> x:X .. (Pf x [+] Q)"
by (simp add: Rep_int_choice_f_def cspT_Dist_com_nonempty)

lemma cspT_Ext_choice_Dist_f_r_nonempty: 
  "[| inj f ; X ~= {} |]
   ==> P [+] (!<f> :X .. Qf) =T[M,M] !<f> x:X .. (P [+] Qf x)"
by (simp add: Rep_int_choice_f_def cspT_Dist_com_nonempty)

lemma cspT_Parallel_Dist_f_l_nonempty: 
  "[| inj f ; Y ~= {} |]
   ==> (!<f> :Y .. Pf) |[X]| Q =T[M,M] !<f> x:Y .. (Pf x |[X]| Q)"
by (simp add: Rep_int_choice_f_def cspT_Dist_com_nonempty)

lemma cspT_Parallel_Dist_f_r_nonempty: 
  "[| inj f ; Y ~= {} |]
   ==> P |[X]| (!<f> :Y .. Qf) =T[M,M] !<f> x:Y .. (P |[X]| Qf x)"
by (simp add: Rep_int_choice_f_def cspT_Dist_com_nonempty)

lemma cspT_Ext_choice_Dist_f_l: 
  "(!<f> :X .. Pf) [+] Q =T[M,M] 
   IF (X ={}) THEN (DIV [+] Q) ELSE (!<f> x:X .. (Pf x [+] Q))"
apply (simp add: Rep_int_choice_f_def)
by (rule cspT_rw_left, rule cspT_Dist_com, simp)

lemma cspT_Ext_choice_Dist_f_r: 
  "P [+] (!<f> :X .. Qf) =T[M,M]
   IF (X ={}) THEN (P [+] DIV) ELSE (!<f> x:X .. (P [+] Qf x))"
apply (simp add: Rep_int_choice_f_def)
by (rule cspT_rw_left, rule cspT_Dist_com, simp)

lemma cspT_Parallel_Dist_f_l: 
  "(!<f> :Y .. Pf) |[X]| Q =T[M,M]
   IF (Y ={}) THEN (DIV |[X]| Q) ELSE (!<f> x:Y .. (Pf x |[X]| Q))"
apply (simp add: Rep_int_choice_f_def)
by (rule cspT_rw_left, rule cspT_Dist_com, simp)

lemma cspT_Parallel_Dist_f_r: 
  "P |[X]| (!<f> :Y .. Qf) =T[M,M] 
   IF (Y ={}) THEN (P |[X]| DIV) ELSE (!<f> x:Y .. (P |[X]| Qf x))"
apply (simp add: Rep_int_choice_f_def)
by (rule cspT_rw_left, rule cspT_Dist_com, simp)

lemma cspT_Hiding_Dist_f: 
  "(!<f> :Y .. Pf) -- X =T[M,M] !<f> x:Y .. (Pf x -- X)"
by (simp add: Rep_int_choice_f_def cspT_Dist_com)

lemma cspT_Renaming_Dist_f: 
  "(!<f> :X .. Pf) [[r]] =T[M,M] !<f> x:X .. (Pf x [[r]])"
by (simp add: Rep_int_choice_f_def cspT_Dist_com)

lemma cspT_Seq_compo_Dist_f:
  "(!<f> :X .. Pf) ;; Q =T[M,M] !<f> x:X .. (Pf x ;; Q)"
by (simp add: Rep_int_choice_f_def cspT_Dist_com)

lemma cspT_Depth_rest_Dist_f: 
  "(!<f> :X .. Pf) |. n =T[M,M] !<f> x:X .. (Pf x |. n)"
by (simp add: Rep_int_choice_f_def cspT_Dist_com)

(*********************************************************
                     Dist laws
 *********************************************************)

lemmas cspT_Dist_f = cspT_Ext_choice_Dist_f_l cspT_Ext_choice_Dist_f_r
                           cspT_Parallel_Dist_f_l   cspT_Parallel_Dist_f_r
                           cspT_Hiding_Dist_f       cspT_Renaming_Dist_f
                           cspT_Seq_compo_Dist_f    cspT_Depth_rest_Dist_f

lemmas cspT_Dist_f_nonempty = 
       cspT_Ext_choice_Dist_f_l_nonempty cspT_Ext_choice_Dist_f_r_nonempty
       cspT_Parallel_Dist_f_l_nonempty   cspT_Parallel_Dist_f_r_nonempty
       cspT_Hiding_Dist_f       cspT_Renaming_Dist_f
       cspT_Seq_compo_Dist_f    cspT_Depth_rest_Dist_f

(*** all rules ***)

lemmas cspT_Dist = cspT_Dist_sum
                   cspT_Dist_nat cspT_Dist_set cspT_Dist_com cspT_Dist_f

lemmas cspT_Dist_nonempty = cspT_Dist_sum_nonempty
                            cspT_Dist_nat_nonempty
                            cspT_Dist_set_nonempty
                            cspT_Dist_com_nonempty
                            cspT_Dist_f_nonempty

(*****************************************************************

      additional distribution over replicated internal choice

         1. (!! :X .. (a -> P))
         2. (!! :Y .. (? :X -> P))

 *****************************************************************)

(*********************************************************
              Dist law for Act_prefix
 *********************************************************)

lemma cspT_Act_prefix_Dist_sum:
  "sumset C ~= {} ==> 
   a -> (!! :C .. Pf) =T[M,M] !! c:C .. (a -> Pf c)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE bexE)
 apply (simp_all)
 apply (force)
 apply (force)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE bexE)
 apply (simp_all)
 apply (force)
done

(*********************************************************
              Dist_nat law for Ext_pre_choice
 *********************************************************)

lemma cspT_Ext_pre_choice_Dist_sum:
  "sumset C ~= {} ==> 
   ? x:X -> (!! c:C .. (Pf c) x) =T[M,M] !! c:C .. (? :X -> (Pf c))"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE bexE)
 apply (simp_all)
 apply (force)
 apply (force)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE bexE)
 apply (simp_all)
 apply (force)
done

(*****************************************************************
                     for convenienve
 *****************************************************************)

(* nat *)

lemma cspT_Act_prefix_Dist_nat:
  "N ~= {} ==> 
   a -> (!nat :N .. Pf) =T[M,M] !nat n:N .. (a -> Pf n)"
by (simp add: Rep_int_choice_ss_def cspT_Act_prefix_Dist_sum)

lemma cspT_Ext_pre_choice_Dist_nat:
  "N ~= {} ==> 
   ? x:X -> (!nat n:N .. (Pf n) x) =T[M,M] !nat n:N .. (? :X -> (Pf n))"
by (simp add: Rep_int_choice_ss_def cspT_Ext_pre_choice_Dist_sum)

(* set *)

lemma cspT_Act_prefix_Dist_set:
  "Xs ~= {} ==> 
   a -> (!set :Xs .. Pf) =T[M,M] !set X:Xs .. (a -> Pf X)"
by (simp add: Rep_int_choice_ss_def cspT_Act_prefix_Dist_sum)

lemma cspT_Ext_pre_choice_Dist_set:
  "Ys ~= {} ==> 
   ? x:X -> (!set Y:Ys .. (Pf Y) x) =T[M,M] !set Y:Ys .. (? :X -> (Pf Y))"
by (simp add: Rep_int_choice_ss_def cspT_Ext_pre_choice_Dist_sum)

(* com *)

lemma cspT_Act_prefix_Dist_com:
  "X ~= {} ==> 
   a -> (! :X .. Pf) =T[M,M] ! x:X .. (a -> Pf x)"
by (simp add: Rep_int_choice_com_def cspT_Act_prefix_Dist_set)

lemma cspT_Ext_pre_choice_Dist_com:
  "Y ~= {} ==> 
   ? x:X -> (! y:Y .. (Pf y) x) =T[M,M] ! y:Y .. (? :X -> (Pf y))"
by (simp add: Rep_int_choice_com_def cspT_Ext_pre_choice_Dist_set)

(* f *)

lemma cspT_Act_prefix_Dist_f:
  "X ~= {} ==> 
   a -> (!<f> :X .. Pf) =T[M,M] !<f> x:X .. (a -> Pf x)"
by (simp add: Rep_int_choice_f_def cspT_Act_prefix_Dist_com)

lemma cspT_Ext_pre_choice_Dist_f:
  "Y ~= {} ==> 
   ? x:X -> (!<f> y:Y .. (Pf y) x) =T[M,M] !<f> y:Y .. (? :X -> (Pf y))"
by (simp add: Rep_int_choice_f_def cspT_Ext_pre_choice_Dist_com)

(*** arias ***)

lemmas cspT_Act_prefix_Dist 
     = cspT_Act_prefix_Dist_sum
       cspT_Act_prefix_Dist_nat
       cspT_Act_prefix_Dist_set
       cspT_Act_prefix_Dist_com
       cspT_Act_prefix_Dist_f

lemmas cspT_Ext_pre_choice_Dist
     = cspT_Ext_pre_choice_Dist_sum
       cspT_Ext_pre_choice_Dist_nat
       cspT_Ext_pre_choice_Dist_set
       cspT_Ext_pre_choice_Dist_com
       cspT_Ext_pre_choice_Dist_f

(*****************************************************************
      distribution over external choice
         1. (P1 [+] P2) [[r]]
         2. (P1 [+] P2) |. n
 *****************************************************************)

(*********************
     [[r]]-[+]-dist
 *********************)

lemma cspT_Renaming_Ext_dist:
  "(P1 [+] P2) [[r]] =T[M,M]
   (P1 [[r]]) [+] (P2 [[r]])"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (force)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (force)
done

(*********************
     |.-[+]-dist
 *********************)

lemma cspT_Depth_rest_Ext_dist: 
  "(P1 [+] P2) |. n =T[M,M]
   (P1 |. n) [+] (P2 |. n)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (force)
done

lemmas cspT_Ext_dist = cspT_Renaming_Ext_dist cspT_Depth_rest_Ext_dist

(*---------------------------------------------------------*
 |                   complex distribution                  |
 *---------------------------------------------------------*)

(*********************
     !!-input-!set
 *********************)

lemma cspT_Rep_int_choice_sum_input_set:
  "(!! c:C .. (? :(Yf c) -> Rff c))
   =T[M,M]
   (!set Y : {(Yf c)|c. c: sumset C} .. 
      (? a : Y -> (!! c:{c:C. a : Yf c}s .. Rff c a)))"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces)
 apply (elim disjE conjE exE bexE)
 apply (simp_all)
  apply (force)

(* <= *)
 apply (rule, simp add: in_traces)
 apply (elim disjE conjE exE)
 apply (simp_all)
 apply (fast)
 apply (force)
done

lemma cspT_Rep_int_choice_nat_input_set:
  "(!nat n:N .. (? :(Yf n) -> Rff n))
   =T[M,M]
   (!set Y : {(Yf n)|n. n:N} .. (? a : Y -> (!nat n:{n:N. a : Yf n} .. Rff n a)))"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Rep_int_choice_sum_input_set)
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_decompo)
apply (auto)
apply (rule_tac x="type2 n" in exI)
by (auto)

lemma cspT_Rep_int_choice_set_input_set:
  "(!set X:Xs .. (? :(Yf X) -> Rff X))
   =T[M,M]
   (!set Y : {(Yf X)|X. X:Xs} .. (? a : Y -> (!set X:{X:Xs. a : Yf X} .. Rff X a)))"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Rep_int_choice_sum_input_set)
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_decompo)
apply (auto)
apply (rule_tac x="type1 X" in exI)
by (auto)

lemmas cspT_Rep_int_choice_input_set =
       cspT_Rep_int_choice_sum_input_set
       cspT_Rep_int_choice_nat_input_set
       cspT_Rep_int_choice_set_input_set

(*-------------------------------*
          !!-[+]-Dist
 *-------------------------------*)

lemma cspT_Rep_int_choice_Ext_Dist_sum:
  "ALL c:sumset C. (Qf c = SKIP | Qf c = DIV) ==>
   (!! c:C .. (Pf c [+] Qf c)) =T[M,M]
   ((!! :C .. Pf) [+] (!! :C .. Qf))"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE bexE disjE)
 apply (simp_all)
 apply (force)
 apply (drule_tac x="c" in bspec)
 apply (simp)
 apply (erule disjE)
 apply (simp_all add: in_traces)
 apply (erule disjE)
 apply (simp_all)
 apply (rule disjI2)
 apply (rule_tac x="c" in bexI)
 apply (simp_all add: in_traces)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE bexE disjE)
 apply (simp_all)
 apply (fast)
 apply (fast)
done

lemma cspT_Rep_int_choice_Ext_Dist_nat:
  "ALL n:N. (Qf n = SKIP | Qf n = DIV) ==>
   (!nat n:N .. (Pf n [+] Qf n)) =T[M,M]
   ((!nat :N .. Pf) [+] (!nat :N .. Qf))"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_Rep_int_choice_Ext_Dist_sum)
by (auto)

lemma cspT_Rep_int_choice_Ext_Dist_set:
  "ALL X:Xs. (Qf X = SKIP | Qf X = DIV) ==>
   (!set X:Xs .. (Pf X [+] Qf X)) =T[M,M]
   ((!set :Xs .. Pf) [+] (!set :Xs .. Qf))"
apply (simp add: Rep_int_choice_ss_def)
apply (rule cspT_Rep_int_choice_Ext_Dist_sum)
by (auto)

lemma cspT_Rep_int_choice_Ext_Dist_com:
  "ALL a:X. (Qf a = SKIP | Qf a = DIV) ==>
   (! a:X .. (Pf a [+] Qf a)) =T[M,M]
   ((! :X .. Pf) [+] (! :X .. Qf))"
apply (simp add: Rep_int_choice_com_def)
apply (rule cspT_Rep_int_choice_Ext_Dist_set)
by (auto)

lemma cspT_Rep_int_choice_Ext_Dist_f:
  "[| inj f ; ALL a:X. (Qf a = SKIP | Qf a = DIV) |] ==>
   (!<f> a:X .. (Pf a [+] Qf a)) =T[M,M]
   ((!<f> :X .. Pf) [+] (!<f> :X .. Qf))"
apply (simp add: Rep_int_choice_f_def)
apply (rule cspT_Rep_int_choice_Ext_Dist_com)
by (auto)

lemmas cspT_Rep_int_choice_Ext_Dist =
       cspT_Rep_int_choice_Ext_Dist_sum
       cspT_Rep_int_choice_Ext_Dist_nat
       cspT_Rep_int_choice_Ext_Dist_set
       cspT_Rep_int_choice_Ext_Dist_com
       cspT_Rep_int_choice_Ext_Dist_f

(*-------------------------------*
          !!-input-Dist
 *-------------------------------*)

lemma cspT_Rep_int_choice_input:
  "!set X:Xs .. (? :X -> Pf) =T[M,M] (? :(Union Xs) -> Pf)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces)
 apply (force)

(* <= *)
 apply (rule, simp add: in_traces)
 apply (force)
done

lemma cspT_Rep_int_choice_input_Dist:
  "(!set X:Xs .. (? :X -> Pf)) [+] Q =T[M,M] (? :(Union Xs) -> Pf) [+] Q"
apply (rule cspT_decompo)
apply (rule cspT_Rep_int_choice_input)
apply (rule cspT_reflex)
done

(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)

(* --------------------------------------------------- *
     distribution hiding over sequential composition
 * --------------------------------------------------- *)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Seq_compo_hide_dist: 
  "(P ;; Q) -- X =T[M,M] (P -- X) ;; (Q -- X)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)

  (* 1 *)
 apply (rule disjI1)
 apply (rule_tac x="sa --tr X" in exI)
 apply (simp add: rmTick_hide)
 apply (rule_tac x="sa" in exI)
 apply (simp)

  (* 2 *)
 apply (rule disjI2)
 apply (rule_tac x="sa --tr X" in exI)
 apply (rule_tac x="ta --tr X" in exI)
 apply (simp)
 apply (rule conjI)
  apply (rule_tac x="sa ^^^ <Tick>" in exI)
  apply (simp)
  apply (rule_tac x="ta" in exI)
  apply (simp)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE)
  (* 1 *)
  apply (insert trace_last_noTick_or_Tick)
  apply (drule_tac x="sa" in spec)
  apply (elim disjE conjE exE)
   apply (simp)
   apply (rule_tac x="sa" in exI)
   apply (simp)
   apply (rule disjI1)
   apply (rule_tac x="sa" in exI)
   apply (simp)

   apply (simp)
   apply (rule_tac x="sb" in exI)
   apply (simp)
   apply (rule disjI1)
   apply (rule_tac x="sb ^^^ <Tick>" in exI)
   apply (simp)

 (* 2 *)
  apply (drule_tac x="sa" in spec)
  apply (elim disjE conjE exE)
   apply (simp)
   apply (subgoal_tac "noTick(sa --tr X)")
   apply (rotate_tac 2)
   apply (drule sym)
   apply (simp del: hide_tr_noTick)
   apply (simp)

   apply (simp)
   apply (rule_tac x="sc ^^^ sb" in exI)
   apply (simp)
   apply (rule disjI2)
   apply (rule_tac x="sc" in exI)
   apply (rule_tac x="sb" in exI)
   apply (simp)
done


(* --------------------------------------------------- *
         distribution hiding over interleaving
 * --------------------------------------------------- *)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Interleave_hide_dist: 
  "(P ||| Q) -- X =T[M,M] (P -- X) ||| (Q -- X)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)
 apply (rule_tac x="sa --tr X" in exI)
 apply (rule_tac x="ta --tr X" in exI)
 apply (simp add: interleave_of_hide_tr_ex)
 apply (force)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE)

 apply (simp add: interleave_of_hide_tr_ex)
 apply (elim conjE exE)
 apply (simp)
 apply (rule_tac x="v" in exI)
 apply (simp)
 apply (force)
done

(* --------------------------------------------------- *
    distribution renaming over sequential composition
 * --------------------------------------------------- *)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Seq_compo_renaming_dist: 
  "(P ;; Q) [[r]] =T[M,M] (P [[r]]) ;; (Q [[r]])"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE disjE)
 apply (simp_all)

  (* 1 *)
  apply (rule disjI1)
  apply (rule_tac x="t" in exI)
  apply (subgoal_tac "noTick t")
  apply (simp)
  apply (rule_tac x="rmTick sa" in exI)
  apply (simp)
  apply (rule memT_prefix_closed)
  apply (simp)
  apply (simp)
  apply (rule ren_tr_noTick_left)
  apply (simp)
  apply (simp)

  (* 2 *)
  apply (rule disjI2)
  apply (simp add: ren_tr_appt_decompo_left)
  apply (elim conjE exE)

  apply (simp)
  apply (rule_tac x="t1" in exI)
  apply (rule_tac x="t2" in exI)
  apply (simp)
  apply (rule conjI)

   apply (rule_tac x="sa ^^^ <Tick>" in exI)
   apply (simp add: ren_tr_noTick_left)

   apply (simp add: ren_tr_noTick_left)
   apply (rule_tac x="ta" in exI)
   apply (simp)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE)
  (* 1 *)
  apply (insert trace_last_noTick_or_Tick)
  apply (drule_tac x="s" in spec)
  apply (elim disjE conjE exE)
   apply (simp)
   apply (rule_tac x="sa" in exI)
   apply (simp)
   apply (rule disjI1)
   apply (rule_tac x="sa" in exI)
   apply (simp)
   apply (simp add: ren_tr_noTick_right)

   apply (simp)
   apply (simp add: ren_tr_appt_decompo_right)
   apply (elim conjE exE)
   apply (simp)
   apply (rule_tac x="s1" in exI)
   apply (simp)
   apply (rule disjI1)
   apply (rule_tac x="s1 ^^^ <Tick>" in exI)
   apply (simp)

 (* 2 *)
  apply (simp)
  apply (simp add: ren_tr_appt_decompo_right)
  apply (elim conjE exE)
  apply (simp)
  apply (rule_tac x="s1 ^^^ sb" in exI)
  apply (rule conjI)

   apply (force)
   apply (force)
done


(* --------------------------------------------------- *
         distribution renaming over interleaving
 * --------------------------------------------------- *)
(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Interleave_renaming_dist: 
  "(P ||| Q) [[r]] =T[M,M] (P [[r]]) ||| (Q [[r]])"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE disjE)
 apply (insert interleave_of_ren_tr_only_if_all)
 apply (drule_tac x="s" in spec)
 apply (drule_tac x="r" in spec)
 apply (drule_tac x="t" in spec)
 apply (drule_tac x="sa" in spec)
 apply (drule_tac x="ta" in spec)
 apply (force)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE disjE)
 apply (erule rem_asmE)
 apply (insert interleave_of_ren_tr_if_all)
 apply (drule_tac x="t" in spec)
 apply (drule_tac x="r" in spec)
 apply (drule_tac x="sa" in spec)
 apply (drule_tac x="sb" in spec)
 apply (drule_tac x="s" in spec)
 apply (drule_tac x="ta" in spec)
 apply (force)
done

(* --------------------------------------------------- *
     distribution internal choice over prefix
 * --------------------------------------------------- *)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Act_prefix_dist:
  "a -> (P |~| Q) =T[M,M] (a -> P) |~| (a -> Q)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE bexE)
 apply (simp_all)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE bexE)
 apply (simp_all)
done


lemma cspT_Int_choice_Act_prefix_delay:
  "(a -> P) |~| (a -> Q) =T[M,M] a -> (P |~| Q)"
apply (rule cspT_sym)
apply (simp add: cspT_Act_prefix_dist)
done

lemma cspT_Int_choice_Act_prefix_delay_eq:
  "a = b ==> (a -> P) |~| (b -> Q) =T[M,M] a -> (P |~| Q)"
apply (simp add: cspT_Int_choice_Act_prefix_delay)
done


(* --------------------------------------------------- *
     distribution internal choice over prefix choice
 * --------------------------------------------------- *)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspT_Ext_pre_choice_dist:
  "? x:X -> (Pf x |~| Qf x) =T[M,M] (? x:X -> Pf x) |~| (? x:X -> Qf x)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE bexE)
 apply (simp_all)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE bexE)
 apply (simp_all)
done


lemma cspT_Int_choice_Ext_pre_choice_delay:
  "(? x:X -> Pf x) |~| (? x:X -> Qf x)  =T[M,M] ? x:X -> (Pf x |~| Qf x)"
apply (rule cspT_sym)
apply (simp add: cspT_Ext_pre_choice_dist)
done

lemma cspT_Int_choice_Ext_pre_choice_delay_eq:
  "X = Y ==>
  (? x:X -> Pf x) |~| (? x:Y -> Qf x)
  =T[M,M] ? x:X -> (Pf x |~| Qf x)"
apply (simp add: cspT_Int_choice_Ext_pre_choice_delay)
done


(*  replicated internal choice *)

lemma cspT_Act_prefix_delay_sum:
  "!! c:C .. (a -> Pf c) =T[M,M] 
   IF (sumset C = {}) THEN DIV ELSE (a -> (!! c:C .. (Pf c)))"
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (case_tac "sumset C = {}")
apply (simp add: cspT_Rep_int_choice_DIV)
apply (simp)
apply (rule cspT_sym)
apply (simp add: cspT_Act_prefix_Dist)
done

lemma cspT_Ext_pre_choice_delay_sum:
  "!! c:C .. (? :X -> (Pf c)) =T[M,M] 
   IF (sumset C = {}) THEN DIV ELSE (? x:X -> (!! c:C .. (Pf c) x))"
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (case_tac "sumset C = {}")
apply (simp add: cspT_Rep_int_choice_DIV)
apply (simp)
apply (rule cspT_sym)
apply (simp add: cspT_Ext_pre_choice_Dist)
done

lemma cspT_Act_prefix_delay_nat:
  "!nat n:N .. (a -> Pf n) =T[M,M] 
   IF (N = {}) THEN DIV ELSE (a -> (!nat n:N .. (Pf n)))"
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (case_tac "N = {}")
apply (simp add: cspT_Rep_int_choice_DIV)
apply (simp)
apply (rule cspT_sym)
apply (simp add: cspT_Act_prefix_Dist)
done

lemma cspT_Ext_pre_choice_delay_nat:
  "!nat n:N .. (? :X -> (Pf n)) =T[M,M] 
   IF (N = {}) THEN DIV ELSE (? x:X -> (!nat n:N .. (Pf n) x))"
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (case_tac "N = {}")
apply (simp add: cspT_Rep_int_choice_DIV)
apply (simp)
apply (rule cspT_sym)
apply (simp add: cspT_Ext_pre_choice_Dist)
done

lemma cspT_Act_prefix_delay_set:
  "!set X:Xs .. (a -> Pf X) =T[M,M] 
   IF (Xs = {}) THEN DIV ELSE (a -> (!set X:Xs .. (Pf X)))"
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (case_tac "Xs = {}")
apply (simp add: cspT_Rep_int_choice_DIV)
apply (simp)
apply (rule cspT_sym)
apply (simp add: cspT_Act_prefix_Dist)
done

lemma cspT_Ext_pre_choice_delay_set:
  "!set Y:Xs .. (? :X -> (Pf Y)) =T[M,M] 
   IF (Xs = {}) THEN DIV ELSE (? x:X -> (!set Y:Xs .. (Pf Y) x))"
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (case_tac "Xs = {}")
apply (simp add: cspT_Rep_int_choice_DIV)
apply (simp)
apply (rule cspT_sym)
apply (simp add: cspT_Ext_pre_choice_Dist)
done

lemma cspT_Act_prefix_delay_com:
  "! x:X .. (a -> Pf x) =T[M,M] 
   IF (X = {}) THEN DIV ELSE (a -> (! :X .. Pf))"
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (case_tac "X = {}")
apply (simp add: cspT_Rep_int_choice_DIV)
apply (simp)
apply (rule cspT_sym)
apply (simp add: cspT_Act_prefix_Dist)
done

lemma cspT_Ext_pre_choice_delay_com:
  "! y:Y .. (? :X -> (Pf y)) =T[M,M] 
   IF (Y = {}) THEN DIV ELSE (? x:X -> (! y:Y .. (Pf y) x))"
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (case_tac "Y = {}")
apply (simp add: cspT_Rep_int_choice_DIV)
apply (simp)
apply (rule cspT_sym)
apply (simp add: cspT_Ext_pre_choice_Dist)
done

lemma cspT_Act_prefix_delay_f:
  "inj f ==> 
   !<f> x:X .. (a -> Pf x) =T[M,M] 
   IF (X = {}) THEN DIV ELSE (a -> (!<f> :X .. Pf))"
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (case_tac "X = {}")
apply (simp add: cspT_Rep_int_choice_DIV)
apply (simp)
apply (rule cspT_sym)
apply (simp add: cspT_Act_prefix_Dist)
done

lemma cspT_Ext_pre_choice_delay_f:
  "inj f ==> 
   !<f> y:Y .. (? :X -> (Pf y)) =T[M,M] 
   IF (Y = {}) THEN DIV ELSE (? x:X -> (!<f> y:Y .. (Pf y) x))"
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (case_tac "Y = {}")
apply (simp add: cspT_Rep_int_choice_DIV)
apply (simp)
apply (rule cspT_sym)
apply (simp add: cspT_Ext_pre_choice_Dist)
done

lemmas cspT_choice_delay =
       cspT_Int_choice_Act_prefix_delay
       cspT_Int_choice_Ext_pre_choice_delay
       cspT_Act_prefix_delay_sum
       cspT_Ext_pre_choice_delay_sum
       cspT_Act_prefix_delay_nat
       cspT_Ext_pre_choice_delay_nat
       cspT_Act_prefix_delay_set
       cspT_Ext_pre_choice_delay_set
       cspT_Act_prefix_delay_com
       cspT_Ext_pre_choice_delay_com
       cspT_Act_prefix_delay_f
       cspT_Ext_pre_choice_delay_f

lemmas cspT_choice_delay_eq =
       cspT_Int_choice_Act_prefix_delay_eq
       cspT_Int_choice_Ext_pre_choice_delay_eq


(*********************************************************
                       P |[X,Y]| Q
 *********************************************************)

(* ---------- *
    |~| left
 * ---------- *)

lemma cspT_Alpha_Parallel_dist_l: 
  "(P1 |~| P2) |[X,Y]| Q =T[M,M]
   (P1 |[X,Y]| Q) |~| (P2 |[X,Y]| Q)"
apply (simp add: Alpha_parallel_def)

apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_dist)
apply (rule cspT_reflex)
apply (rule cspT_rw_left)
apply (rule cspT_dist)
apply (simp)
done

(* ---------- *
    |~| right
 * ---------- *)
lemma cspT_Alpha_Parallel_dist_r: 
  "P |[X,Y]| (Q1 |~| Q2) =T[M,M]
   (P |[X,Y]| Q1) |~| (P |[X,Y]| Q2)"
apply (simp add: Alpha_parallel_def)

apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_reflex)
apply (rule cspT_dist)
apply (rule cspT_rw_left)
apply (rule cspT_dist)
apply (simp)
done

(* ---------- *
    !! left
 * ---------- *)

lemma cspT_Alpha_Parallel_Dist_sum_l_nonempty: 
  "sumset C ~= {} ==>
     (!! :C .. Pf) |[X,Y]| Q =T[M,M]
     !! c:C .. (Pf c |[X,Y]| Q)"
apply (simp add: Alpha_parallel_def)

apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_Parallel_Dist_sum_l_nonempty)
apply (simp)
apply (rule cspT_reflex)
apply (rule cspT_rw_left)
apply (rule cspT_Parallel_Dist_sum_l_nonempty)
apply (simp)
apply (simp)
done

lemma cspT_Alpha_Parallel_Dist_sum_l: 
  "(!! :C .. Pf) |[X,Y]| Q =T[M,M]
   IF (sumset C={}) THEN (DIV |[X,Y]| Q) ELSE (!! c:C .. (Pf c |[X,Y]| Q))"
apply (case_tac "sumset C={}")
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (rule cspT_decompo_Alpha_parallel)
apply (simp)+
apply (simp add: cspT_Rep_int_choice_empty)
apply (simp)

apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (rule cspT_Alpha_Parallel_Dist_sum_l_nonempty)
apply (simp)
done

(* ---------- *
    !! right
 * ---------- *)

lemma cspT_Alpha_Parallel_Dist_sum_r_nonempty: 
  "sumset C ~= {} ==>
     P |[X,Y]| (!! :C .. Qf) =T[M,M]
     !! c:C .. (P |[X,Y]| Qf c)"
apply (rule cspT_rw_left)
apply (rule cspT_Alpha_parallel_commut)
apply (rule cspT_rw_left)
apply (rule cspT_Alpha_Parallel_Dist_sum_l_nonempty, simp)
apply (rule cspT_decompo, simp)
apply (rule cspT_Alpha_parallel_commut)
done

lemma cspT_Alpha_Parallel_Dist_sum_r: 
  "P |[X,Y]| (!! :C .. Qf) =T[M,M]
   IF (sumset C={}) THEN (P |[X,Y]| DIV) ELSE (!! c:C .. (P |[X,Y]| Qf c))"
apply (case_tac "sumset C={}")
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (rule cspT_decompo_Alpha_parallel)
apply (simp)+
apply (simp add: cspT_Rep_int_choice_empty)
apply (simp)

apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (rule cspT_Alpha_Parallel_Dist_sum_r_nonempty)
apply (simp)
done

(* ---------- *
   !nat left
 * ---------- *)

lemma cspT_Alpha_Parallel_Dist_nat_l_nonempty: 
  "N ~= {} ==>
     (!nat :N .. Pf) |[X,Y]| Q =T[M,M]
     !nat n:N .. (Pf n |[X,Y]| Q)"
by (simp add: Rep_int_choice_ss_def cspT_Alpha_Parallel_Dist_sum_l_nonempty)

(*** Dist ***)

lemma cspT_Alpha_Parallel_Dist_nat_l: 
  "(!nat :N .. Pf) |[X,Y]| Q =T[M,M]
   IF (N={}) THEN (DIV |[X,Y]| Q) ELSE (!nat n:N .. (Pf n |[X,Y]| Q))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_rw_left, rule cspT_Alpha_Parallel_Dist_sum_l, simp)

(* ---------- *
   !nat right
 * ---------- *)

lemma cspT_Alpha_Parallel_Dist_nat_r_nonempty: 
  "N ~= {} ==>
     P |[X,Y]| (!nat :N .. Qf) =T[M,M]
     !nat n:N .. (P |[X,Y]| Qf n)"
by (simp add: Rep_int_choice_ss_def cspT_Alpha_Parallel_Dist_sum_r_nonempty)

(*** Dist ***)

lemma cspT_Alpha_Parallel_Dist_nat_r: 
  "P |[X,Y]| (!nat :N .. Qf) =T[M,M]
   IF (N={}) THEN (P |[X,Y]| DIV) ELSE (!nat n:N .. (P |[X,Y]| Qf n))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_rw_left, rule cspT_Alpha_Parallel_Dist_sum_r, simp)

(* ---------- *
   !set left
 * ---------- *)

lemma cspT_Alpha_Parallel_Dist_set_l_nonempty: 
  "Xs ~= {} ==>
     (!set :Xs .. Pf) |[Y,Z]| Q =T[M,M]
     !set X:Xs .. (Pf X |[Y,Z]| Q)"
by (simp add: Rep_int_choice_ss_def cspT_Alpha_Parallel_Dist_sum_l_nonempty)

(*** Dist ***)

lemma cspT_Alpha_Parallel_Dist_set_l: 
  "(!set :Xs .. Pf) |[Y,Z]| Q =T[M,M]
   IF (Xs={}) THEN (DIV |[Y,Z]| Q) ELSE (!set X:Xs .. (Pf X |[Y,Z]| Q))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_rw_left, rule cspT_Alpha_Parallel_Dist_sum_l, simp)

(* ---------- *
   !set right
 * ---------- *)

lemma cspT_Alpha_Parallel_Dist_set_r_nonempty: 
  "Xs ~= {} ==>
     P |[Y,Z]| (!set :Xs .. Qf) =T[M,M]
     !set X:Xs .. (P |[Y,Z]| Qf X)"
by (simp add: Rep_int_choice_ss_def cspT_Alpha_Parallel_Dist_sum_r_nonempty)

(*** Dist ***)

lemma cspT_Alpha_Parallel_Dist_set_r: 
  "P |[Y,Z]| (!set :Xs .. Qf) =T[M,M]
   IF (Xs={}) THEN (P |[Y,Z]| DIV) ELSE (!set X:Xs .. (P |[Y,Z]| Qf X))"
apply (simp add: Rep_int_choice_ss_def)
by (rule cspT_rw_left, rule cspT_Alpha_Parallel_Dist_sum_r, simp)

(* ---------- *
     ! left
 * ---------- *)

lemma cspT_Alpha_Parallel_Dist_com_l_nonempty: 
  "A ~= {}
   ==> (! :A .. Pf) |[X,Y]| Q =T[M,M] ! x:A .. (Pf x |[X,Y]| Q)"
by (simp add: Rep_int_choice_com_def cspT_Alpha_Parallel_Dist_set_l_nonempty)

lemma cspT_Alpha_Parallel_Dist_com_l: 
  "(! :A .. Pf) |[X,Y]| Q =T[M,M]
   IF (A ={}) THEN (DIV |[X,Y]| Q) ELSE (! x:A .. (Pf x |[X,Y]| Q))"
apply (simp add: Rep_int_choice_com_def)
by (rule cspT_rw_left, rule cspT_Alpha_Parallel_Dist_set_l, simp)

(* ---------- *
     ! right
 * ---------- *)

lemma cspT_Alpha_Parallel_Dist_com_r_nonempty: 
  "A ~= {}
   ==> P |[X,Y]| (! :A .. Qf) =T[M,M] ! x:A .. (P |[X,Y]| Qf x)"
by (simp add: Rep_int_choice_com_def cspT_Alpha_Parallel_Dist_set_r_nonempty)

lemma cspT_Alpha_Parallel_Dist_com_r: 
  "P |[X,Y]| (! :A .. Qf) =T[M,M] 
   IF (A ={}) THEN (P |[X,Y]| DIV) ELSE (! x:A .. (P |[X,Y]| Qf x))"
apply (simp add: Rep_int_choice_com_def)
by (rule cspT_rw_left, rule cspT_Alpha_Parallel_Dist_set_r, simp)

(* ---------- *
   !<f> left
 * ---------- *)

lemma cspT_Alpha_Parallel_Dist_f_l_nonempty: 
  "[| inj f ; A ~= {} |]
   ==> (!<f> :A .. Pf) |[X,Y]| Q =T[M,M] !<f> x:A .. (Pf x |[X,Y]| Q)"
by (simp add: Rep_int_choice_f_def cspT_Alpha_Parallel_Dist_com_l_nonempty)

lemma cspT_Alpha_Parallel_Dist_f_l: 
  "(!<f> :A .. Pf) |[X,Y]| Q =T[M,M]
   IF (A ={}) THEN (DIV |[X,Y]| Q) ELSE (!<f> x:A .. (Pf x |[X,Y]| Q))"
apply (simp add: Rep_int_choice_f_def)
by (rule cspT_rw_left, rule cspT_Alpha_Parallel_Dist_com_l, simp)

lemma cspT_Alpha_Parallel_Dist_f_r_nonempty: 
  "[| inj f ; A ~= {} |]
   ==> P |[X,Y]| (!<f> :A .. Qf) =T[M,M] !<f> x:A .. (P |[X,Y]| Qf x)"
by (simp add: Rep_int_choice_f_def cspT_Alpha_Parallel_Dist_com_r_nonempty)

lemma cspT_Alpha_Parallel_Dist_f_r: 
  "P |[X,Y]| (!<f> :A .. Qf) =T[M,M] 
   IF (A ={}) THEN (P |[X,Y]| DIV) ELSE (!<f> x:A .. (P |[X,Y]| Qf x))"
apply (simp add: Rep_int_choice_f_def)
by (rule cspT_rw_left, rule cspT_Alpha_Parallel_Dist_com_r, simp)

lemmas cspT_dist_Alpha_Parallel =
       cspT_Alpha_Parallel_dist_l
       cspT_Alpha_Parallel_dist_r 

lemmas cspT_Dist_Alpha_Parallel =
      cspT_Alpha_Parallel_Dist_sum_l 
      cspT_Alpha_Parallel_Dist_sum_r 
      cspT_Alpha_Parallel_Dist_nat_l 
      cspT_Alpha_Parallel_Dist_nat_r 
      cspT_Alpha_Parallel_Dist_set_l 
      cspT_Alpha_Parallel_Dist_set_r 
      cspT_Alpha_Parallel_Dist_com_l 
      cspT_Alpha_Parallel_Dist_com_r 
      cspT_Alpha_Parallel_Dist_f_l 
      cspT_Alpha_Parallel_Dist_f_r 

lemmas cspT_Dist_Alpha_Parallel_nonempty =
      cspT_Alpha_Parallel_Dist_sum_l_nonempty 
      cspT_Alpha_Parallel_Dist_sum_r_nonempty 
      cspT_Alpha_Parallel_Dist_nat_l_nonempty 
      cspT_Alpha_Parallel_Dist_nat_r_nonempty 
      cspT_Alpha_Parallel_Dist_set_l_nonempty 
      cspT_Alpha_Parallel_Dist_set_r_nonempty 
      cspT_Alpha_Parallel_Dist_com_l_nonempty
      cspT_Alpha_Parallel_Dist_com_r_nonempty 
      cspT_Alpha_Parallel_Dist_f_l_nonempty 
      cspT_Alpha_Parallel_Dist_f_r_nonempty 

(****************** to add them again ******************)

end
