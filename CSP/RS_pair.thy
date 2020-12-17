           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009-2       |
            |                October 2010  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2020         |
            |                  April 2020  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory RS_pair
imports RS
begin

(*****************************************************************

         1. Pairs of RS are also RS.
         2. 
         3. 
         4. 

 *****************************************************************)

(********************************************************** 
              def: pair of restriction space
 **********************************************************)


instantiation prod :: (rs, rs) rs0
begin

definition
  pair_restriction_def : 
    "(xc::('a::rs * 'b::rs)) .|. n 
        == (((fst xc) .|. n) , ((snd xc) .|. n))"

  instance proof qed

end

definition
  pair_Limit :: "(('a::ms_rs * 'b::ms_rs) infinite_seq) => ('a::ms_rs * 'b::ms_rs)"
(*  pair_Limit :: "(('a::ms_rs * 'b::ms_rs) infinite_seq) => ('a::ms_rs * 'b::ms_rs)" *)
  where
  pair_Limit_def :
     "pair_Limit xcs == (Limit (fst o xcs) , Limit (snd o xcs))"

(************************************************************
                         Basics
 ************************************************************)

lemma rest_to_pair_rest:
    "[| (fst xc) .|. n = (fst yc) .|. n ;
        (snd xc) .|. n = (snd yc) .|. n |]
     ==> (xc::('a::rs * 'b::rs)) .|. n = yc .|. n"
by (simp add: pair_restriction_def)

(************************************************************
                   Pair RS ==> RS 
 ************************************************************)

(*** pair_zero_eq_rs ***)

lemma pair_zero_eq_rs:
  "(xc::('a::rs * 'b::rs)) .|. 0 = yc .|. 0"
by (simp add: pair_restriction_def)

(*** pair_min_rs ***)

lemma pair_min_rs: 
  "((xc::('a::rs * 'b::rs)) .|. m) .|. n = xc .|. (min m n)"
apply (simp add: pair_restriction_def)
by (simp add: min_rs)

(*** contra_pair_diff_rs ***)

lemma contra_pair_diff_rs:
  "(ALL n. (xc::('a::rs * 'b::rs)) .|. n = yc .|. n) ==> (xc = yc)"
apply (simp add: pair_restriction_def)

apply (insert contra_diff_rs[of "fst xc" "fst yc"])
apply (insert contra_diff_rs[of "snd xc" "snd yc"])
apply (simp add: prod_eq_iff)

done
(*** pair_diff_rs ***)

lemma pair_diff_rs: 
  "((xc::('a::rs * 'b::rs)) ~= yc) ==> (EX n. xc .|. n ~= yc .|. n)"
apply (erule contrapos_pp)
apply (insert contra_pair_diff_rs[of xc yc])
by (simp)

(*****************************************
              Pair RS => RS
 *****************************************)

instance prod :: (rs,rs) rs
apply (intro_classes)
apply (simp add: pair_zero_eq_rs)
apply (simp add: pair_min_rs)
apply (simp add: pair_diff_rs)
done

(************************************************************
                     Pair RS ==> MS 
 ************************************************************)

instantiation prod :: (rs,rs) ms0
begin

(*
fun pair_distance_def :: "(('a::rs * 'b::rs) * ('a::rs * 'b::rs)) => real"
where "distance xy = distance_rs xy"
*)

definition
  pair_distance_def: "distance (xy::('a::rs * 'b::rs) * ('a::rs * 'b::rs)) = distance_rs xy"

  instance proof qed
end

instance prod :: (rs,rs) ms
apply (intro_classes)
apply (simp_all add: pair_distance_def)
apply (simp add: diagonal_rs)
apply (simp add: pair_distance_def symmetry_rs)
apply (simp add: pair_distance_def triangle_inequality_rs)
done

(* isabelle 2009-1
instance * :: (rs,rs) ms
apply (intro_classes)
apply (simp)
apply (simp add: diagonal_rs)
apply (simp add: symmetry_rs)
apply (simp add: triangle_inequality_rs)
done
*)

(************************************************************
             i.e.  Pair RS ==> MS & RS 
 ************************************************************)

instance prod :: (rs,rs) ms_rs
apply (intro_classes)
apply (simp add: pair_distance_def)
done

(************************************************************
                     Lemmas (distance)
 ************************************************************)

(* distance_nat *)

lemma pair_distance_nat_le_fst:
      "fst xc ~= fst yc
       ==> distance_nat ((xc::('a::rs * 'b::rs)), yc)
        <= distance_nat (fst xc, fst yc)"
apply (case_tac "xc = yc", simp)
apply (simp add: distance_nat_le_1[THEN sym])

apply (insert distance_nat_is[of xc yc], simp)
apply (simp add: isMAX_def)
apply (simp add: distance_nat_set_def)
by (simp add: pair_restriction_def)

lemma pair_distance_nat_le_snd:
      "snd xc ~= snd yc
       ==> distance_nat ((xc::('a::rs * 'b::rs)), yc)
        <= distance_nat (snd xc, snd yc)"
apply (case_tac "xc = yc", simp)
apply (simp add: distance_nat_le_1[THEN sym])

apply (insert distance_nat_is[of xc yc], simp)
apply (simp add: isMAX_def)
apply (simp add: distance_nat_set_def)
by (simp add: pair_restriction_def)

lemmas pair_distance_nat_le = pair_distance_nat_le_fst
                              pair_distance_nat_le_snd

(* distance *)

lemma pair_distance_def_le_fst:
   "distance (fst xc, fst yc) <= distance ((xc::('a::ms0_rs * 'b::ms0_rs)), yc)"
apply (case_tac "fst xc = fst yc", simp)
apply (case_tac "xc = yc", simp)
apply (simp_all add: to_distance_rs)
apply (case_tac "xc = yc", simp)
apply (simp add: distance_iff)
apply (simp add: pair_distance_nat_le_fst)  (* modified for Isabelle2020 *)
done

lemma pair_distance_def_le_fst_compo:
   "distance (a1, a2) <= distance ((a1::'a::ms0_rs, b1::'b::ms0_rs), (a2, b2))"
apply (insert pair_distance_def_le_fst[of "(a1,b1)" "(a2,b2)"])
by (simp)

lemma pair_distance_def_le_snd:
   "distance (snd xc, snd yc) <= distance ((xc::('a::ms0_rs * 'b::ms0_rs)), yc)"
apply (case_tac "snd xc = snd yc", simp)
apply (case_tac "xc = yc", simp)
apply (simp_all add: to_distance_rs)
apply (case_tac "xc = yc", simp)
apply (simp add: distance_iff)
(* apply (rule power_decreasing, simp_all)   modified for Isabelle2020 *)
by (simp add: pair_distance_nat_le_snd)

lemma pair_distance_def_le_snd_compo:
   "distance (b1, b2) <= distance ((a1::'a::ms0_rs, b1::'b::ms0_rs), (a2, b2))"
apply (insert pair_distance_def_le_snd[of "(a1,b1)" "(a2,b2)"])
by (simp)

lemmas pair_distance_def_le = 
       pair_distance_def_le_fst pair_distance_def_le_snd

lemmas pair_distance_def_le_compo = 
       pair_distance_def_le_fst_compo pair_distance_def_le_snd_compo

(*** pair_distance (max) ***)

lemma pair_distance_max: 
  "distance ((xc::('a::ms_rs * 'b::ms_rs)), yc)
  = max (distance (fst xc, fst yc)) (distance (snd xc, snd yc))"
apply (case_tac "distance (fst xc, fst yc) <= distance (snd xc, snd yc)")
apply (simp add: max_is)
apply (rule order_antisym)
apply (simp_all add: pair_distance_def_le)

apply (case_tac "xc = yc", simp)
apply (case_tac "snd xc = snd yc", simp)
apply (case_tac "fst xc = fst yc", simp)
apply (simp add: pair_neq_decompo)
apply (erule contrapos_pp)
apply (simp add: linorder_not_le diff_pnt_pos_if)

 (* xc ~= yc; snd xc ~= snd yc *)
apply (simp add: to_distance_rs)
 apply (simp add: distance_iff)
 (* apply (rule power_decreasing, simp_all)  for 2020 *)
 apply (simp add: distance_nat_le_1[THEN sym])
 apply (simp add: pair_restriction_def)
 apply (simp add: distance_nat_rest)

 apply (case_tac "fst xc = fst yc", simp)
 apply (simp add: distance_iff)
 apply (rule rest_equal_preserve)
 apply (rule distance_nat_rest)
 apply (simp_all)
 (* apply (rule rev_power_decreasing, simp_all)     deleted for Isabelle2020 *)

      (* ~ distance (fst xc, fst yc) <= distance (snd xc, snd yc) *)

apply (simp add: max_is)
apply (rule order_antisym)
apply (simp_all add: pair_distance_def_le)

apply (case_tac "xc = yc", simp)
apply (case_tac "fst xc = fst yc", simp)

 (* xc ~= yc; fst xc ~= fst yc *)
 apply (simp add: to_distance_rs)
 apply (simp add: distance_iff)
 (* apply (rule power_decreasing, simp_all)     deleted for Isabelle2020 *)
 apply (simp add: distance_nat_le_1[THEN sym])
 apply (simp add: pair_restriction_def)
 apply (simp add: distance_nat_rest)

 apply (case_tac "snd xc = snd yc", simp)
 apply (simp add: distance_iff)
 apply (rule rest_equal_preserve)
 apply (rule distance_nat_rest)
 apply (simp_all)

apply (simp add: linorder_not_le)
(* apply (insert rev_power_decreasing[of "1/2"])    removed for Isabelle 2020 *)
done

lemma pair_distance_max_compo: 
  "distance ((a1::('a::ms_rs), b1::('b::ms_rs)), (a2, b2))
  = max (distance (a1, a2)) (distance (b1, b2))"
apply (insert pair_distance_max[of "(a1, b1)" "(a2, b2)"])
by (simp)

lemma ALL_pair_distance_max: 
  "ALL xc yc. distance ((xc::('a::ms_rs * 'b::ms_rs)), yc)
       = max (distance (fst xc, fst yc)) (distance (snd xc, snd yc))"
by (simp add: pair_distance_max)

(*****************************************
               pair maps
 *****************************************)

(*** fst ***)

lemma fst_non_expand: "non_expanding (fst::('a::ms_rs * 'b::ms_rs)=>'a)"
apply (simp add: non_expanding_def)
apply (simp add: map_alpha_def)
apply (simp add: pair_distance_def_le_compo)
done

(*** snd ***)

lemma snd_non_expand: "non_expanding (snd::('a::ms_rs * 'b::ms_rs)=>'b)"
apply (simp add: non_expanding_def)
apply (simp add: map_alpha_def)
apply (simp add: pair_distance_def_le_compo)
done

(*---------------------*
 |      map_alpha      |
 *---------------------*)

(* only_if *)

lemma pair_map_alpha_only_if:
  "map_alpha (fc::('a::ms_rs => ('b::ms_rs * 'c::ms_rs))) alpha
   ==> (map_alpha (fst o fc) alpha & 
        map_alpha (snd o fc) alpha)"
by (simp add: compo_non_expand_map_alpha fst_non_expand snd_non_expand)

(* if *)

lemma pair_map_alpha_if:
  "[| map_alpha (fst o fc) alpha ; map_alpha (snd o fc) alpha |]
   ==> map_alpha (fc::('a::ms_rs => ('b::ms_rs * 'c::ms_rs))) alpha"
apply (simp add: map_alpha_def)
apply (intro allI)
apply (insert ALL_pair_distance_max)
apply (rotate_tac -1, drule_tac x="fc x" in spec)
apply (rotate_tac -1, drule_tac x="fc y" in spec)
by (simp)

(* iff *)

lemma pair_map_alpha:
  "map_alpha (fc::('a::ms_rs => ('b::ms_rs * 'c::ms_rs))) alpha
   = (map_alpha (fst o fc) alpha & map_alpha (snd o fc) alpha)"
apply (rule iffI)
apply (simp add: pair_map_alpha_only_if)
apply (simp add: pair_map_alpha_if)
done

lemma pair_map_alpha_compo:
  "map_alpha (f ** g) alpha
   = (map_alpha (f::('a::ms_rs => 'b::ms_rs)) alpha &
      map_alpha (g::('a::ms_rs => 'c::ms_rs)) alpha)"
apply (insert pair_map_alpha[of "f ** g"])
by (simp)

(*---------------------*
 |    non_expanding    |
 *---------------------*)

lemma pair_non_expand:
  "non_expanding (fc::('a::ms_rs => ('b::ms_rs * 'c::ms_rs)))
   = (non_expanding (fst o fc) & non_expanding (snd o fc))"
apply (simp add: non_expanding_def)
by (simp add: pair_map_alpha)

lemma pair_non_expand_compo:
  "non_expanding (f ** g) 
   = (non_expanding (f::('a::ms_rs => 'b::ms_rs)) &
      non_expanding (g::('a::ms_rs => 'c::ms_rs)))"
apply (simp add: non_expanding_def)
by (simp add: pair_map_alpha_compo)

(*---------------------*
 |  alpha_contraction  |
 *---------------------*)

lemma pair_contra_alpha:
  "contraction_alpha (fc::('a::ms_rs => ('b::ms_rs * 'c::ms_rs))) alpha
   = (contraction_alpha (fst o fc) alpha & contraction_alpha (snd o fc) alpha)"
apply (simp add: contraction_alpha_def)
by (auto simp add: pair_map_alpha)

lemma pair_contra_alpha_compo:
  "contraction_alpha (f ** g) alpha
   = (contraction_alpha (f::('a::ms_rs => 'b::ms_rs)) alpha &
      contraction_alpha (g::('a::ms_rs => 'c::ms_rs)) alpha)"
apply (simp add: contraction_alpha_def)
by (auto simp add: pair_map_alpha_compo)

(************************************************************
                       Lemmas (Limit)
 ************************************************************)

(*****************************************
                  cauchy
 *****************************************)

lemma pair_cauchy_seq_fst:
  "cauchy (xcs::('a::ms_rs * 'b::ms_rs) infinite_seq)
   ==> cauchy (fst o xcs)"
apply (simp add: cauchy_def)
apply (intro allI impI)

apply (drule_tac x="delta" in spec)
apply (simp)
apply (erule exE)
apply (rule_tac x="n" in exI)
apply (intro allI impI)
apply (rename_tac delta N n m)
apply (drule_tac x="n" in spec)
apply (drule_tac x="m" in spec)
apply (simp add: pair_distance_max)
done

lemma pair_cauchy_seq_snd:
  "cauchy (xcs::('a::ms_rs * 'b::ms_rs) infinite_seq)
   ==> cauchy (snd o xcs)"
apply (simp add: cauchy_def)
apply (intro allI impI)

apply (drule_tac x="delta" in spec)
apply (simp)
apply (erule exE)
apply (rule_tac x="n" in exI)
apply (intro allI impI)
apply (rename_tac delta N n m)
apply (drule_tac x="n" in spec)
apply (drule_tac x="m" in spec)
apply (simp add: pair_distance_max)
done

lemmas pair_cauchy_seq = pair_cauchy_seq_fst pair_cauchy_seq_snd

lemma pair_cauchy_seq_fst_compo:
  "cauchy ((xc::'a::ms_rs infinite_seq) ** (yc::'a::ms_rs infinite_seq))
   ==> cauchy xc"
apply (insert pair_cauchy_seq_fst[of "xc ** yc"])
by (simp)

lemma pair_cauchy_seq_snd_compo:
  "cauchy ((xc::'a::ms_rs infinite_seq) ** (yc::'a::ms_rs infinite_seq))
   ==> cauchy yc"
apply (insert pair_cauchy_seq_snd[of "xc ** yc"])
by (simp)

lemmas pair_cauchy_seq_compo = pair_cauchy_seq_fst_compo pair_cauchy_seq_snd_compo

(*** normal ***)

lemma pair_normal_seq_fst:
  "normal (xcs::('a::ms_rs * 'b::ms_rs) infinite_seq)
   ==> normal (fst o xcs)"
apply (simp add: normal_def)
apply (intro allI)
apply (drule_tac x="n" in spec)
apply (drule_tac x="m" in spec)
by (simp add: pair_distance_max)

lemma pair_normal_seq_snd:
  "normal (xcs::('a::ms_rs * 'b::ms_rs) infinite_seq)
   ==> normal (snd o xcs)"
apply (simp add: normal_def)
apply (intro allI)
apply (drule_tac x="n" in spec)
apply (drule_tac x="m" in spec)
by (simp add: pair_distance_max)

lemmas pair_normal_seq = pair_normal_seq_fst pair_normal_seq_snd

lemma pair_normal_seq_fst_compo:
  "normal ((xc::'a::ms_rs infinite_seq) ** (yc::'a::ms_rs infinite_seq))
   ==> normal xc"
apply (insert pair_normal_seq_fst[of "xc ** yc"])
by (simp)

lemma pair_normal_seq_snd_compo:
  "normal ((xc::'a::ms_rs infinite_seq) ** (yc::'a::ms_rs infinite_seq))
   ==> normal yc"
apply (insert pair_normal_seq_snd[of "xc ** yc"])
by (simp)

lemmas pair_normal_seq_compo = pair_normal_seq_fst_compo pair_normal_seq_snd_compo

lemma pair_normal_seq_compo_only_if:
  "[| normal xc ; normal yc |] ==>
   normal ((xc::'a::ms_rs infinite_seq) ** (yc::'b::ms_rs infinite_seq))"
apply (simp add: normal_def)
apply (intro allI)
apply (drule_tac x="n" in spec)
apply (drule_tac x="n" in spec)
apply (drule_tac x="m" in spec)
apply (drule_tac x="m" in spec)
apply (simp add: pair_distance_max)
apply (simp add: pair_fun_def)
done

(* iff *)

lemma pair_normal_seq_compo_iff:
  "normal (xcs::('a::ms_rs * 'b::ms_rs) infinite_seq)
   = (normal (fst o xcs) & normal (snd o xcs))"
apply (rule)
apply (simp add: pair_normal_seq)
apply (insert pair_normal_seq_compo_only_if[of "(fst o xcs)" "(snd o xcs)"])
apply (simp add: pair_fun_def)
done

(*-----------------------*
 |     pairof Limits     |
 *-----------------------*)

(*** Limit (single <-- pair) ***)

lemma pair_convergeTo_fst_only_if:
  "(xcs::(('a::ms_rs * 'b::ms_rs) infinite_seq)) convergeTo yc
   ==> (fst o xcs) convergeTo (fst yc)"
apply (simp add: convergeTo_def)
apply (intro allI impI)

apply (drule_tac x="eps" in spec)
apply (simp)
apply (erule exE)
apply (rule_tac x="n" in exI)
apply (intro allI impI)
apply (rename_tac eps N n)
apply (drule_tac x="n" in spec)
apply (simp add: pair_distance_max)
done

lemma pair_convergeTo_snd_only_if:
  "(xcs::(('a::ms_rs * 'b::ms_rs) infinite_seq)) convergeTo yc
   ==> (snd o xcs) convergeTo (snd yc)"
apply (simp add: convergeTo_def)
apply (intro allI impI)

apply (drule_tac x="eps" in spec)
apply (simp)
apply (erule exE)
apply (rule_tac x="n" in exI)
apply (intro allI impI)
apply (rename_tac eps N n)
apply (drule_tac x="n" in spec)
apply (simp add: pair_distance_max)
done

(*** Limit (single --> pair) (note: ms_rs) ***)

lemma pair_convergeTo_if:
  "[| (fst o xcs) convergeTo (fst yc) ; (snd o xcs) convergeTo (snd yc) |]
   ==> (xcs::(('a::ms_rs * 'b::ms_rs) infinite_seq)) convergeTo yc"
apply (simp add: convergeTo_def)
apply (intro allI impI)

apply (drule_tac x="eps" in spec)
apply (drule_tac x="eps" in spec)
apply (simp)
apply (erule exE)+
apply (rename_tac eps N2 N1)

apply (rule_tac x="max N1 N2" in exI)
apply (simp add: pair_distance_max)
done

(*** iff ***)

lemma pair_convergeTo:
  "(xcs::(('a::ms_rs * 'b::ms_rs) infinite_seq)) convergeTo yc
   = ((fst o xcs) convergeTo (fst yc) & (snd o xcs) convergeTo (snd yc))"
apply (rule iffI)
apply (simp add: pair_convergeTo_fst_only_if pair_convergeTo_snd_only_if)
apply (simp add: pair_convergeTo_if)
done

lemma pair_convergeTo_compo:
  "((xs::('a::ms_rs infinite_seq)) ** (ys::('b::ms_rs infinite_seq)))
   convergeTo (x, y)
   = (xs convergeTo x & ys convergeTo y)"
apply (insert pair_convergeTo[of "xs ** ys" "(x,y)"])
by (simp)

(*****************************************
     Limit (cms and cauchy --> Limit) 
 *****************************************)

lemma pair_cms_cauchy_Limit:
  "cauchy (xcs::(('a::cms_rs * 'b::cms_rs) infinite_seq)) 
   ==> xcs convergeTo (pair_Limit xcs)"
apply (simp add: pair_convergeTo)
by (simp add: pair_Limit_def pair_cauchy_seq Limit_is)

(*****************************************
     Pair Complete Metric Space (RS)
 *****************************************)

lemma pair_cms_rs:
  "cauchy (xcs::(('a::cms_rs * 'b::cms_rs) infinite_seq)) 
   ==> EX yc. xcs convergeTo yc"
apply (rule_tac x="pair_Limit xcs" in exI)
by (simp add: pair_cms_cauchy_Limit)

(************************************************************
                   Pair RS ==> CMS and RS
 ************************************************************)

instance prod :: (cms_rs,cms_rs) cms_rs
apply (intro_classes)
apply (intro allI impI)
by (rule pair_cms_rs, simp)

(*----------------------------------------------------------*
 |                                                          |
 |                Continuity on Metric space                |
 |                                                          |
 *----------------------------------------------------------*)

declare disj_not1 [simp del]

lemma pair_continuous_rs: 
   "[| continuous_rs R1 ; continuous_rs R2 |]
     ==> continuous_rs (%xc. (R1 (fst xc) & R2 (snd xc)))"
apply (simp add: continuous_rs_def)
apply (intro allI)
apply (rule conjI)

apply (intro impI)
apply (drule_tac x="a" in spec)
apply (simp)
apply (erule exE)
apply (rule_tac x="n" in exI)
apply (intro allI impI)
apply (rotate_tac -1)
apply (drule_tac x="b" in spec)
apply (simp add: pair_restriction_def)

apply (intro impI)
apply (rotate_tac -1)
apply (drule_tac x="b" in spec)
apply (simp)
apply (erule exE)
apply (rule_tac x="n" in exI)
apply (intro allI impI)
apply (rotate_tac -2)
apply (drule_tac x="ba" in spec)
apply (simp add: pair_restriction_def)
done

(*----------------------------------------------------------*
 |                                                          |
 |      !!!     order and restriction space     !!!         |
 |                                                          |
 *----------------------------------------------------------*)

instance prod :: (ms_rs_order,ms_rs_order) ms_rs_order0
by (intro_classes)

instance prod :: (ms_rs_order,ms_rs_order) ms_rs_order
apply (intro_classes)
apply (simp add: order_pair_def pair_restriction_def)
apply (intro allI)
apply (rule iffI)
apply (rule conjI)
apply (insert rs_order_iff)
apply (drule_tac x="a" in spec)
apply (drule_tac x="aa" in spec)
apply (fast)
apply (drule_tac x="b" in spec)
apply (drule_tac x="ba" in spec)
apply (fast)

apply (intro allI)
apply (rule conjI)
apply (drule_tac x="a" in spec)
apply (drule_tac x="aa" in spec)
apply (fast)
apply (insert rs_order_iff)
apply (drule_tac x="b" in spec)
apply (drule_tac x="ba" in spec)
apply (fast)
done

(*** cms rs order ***)

instance prod :: (cms_rs_order,cms_rs_order) cms_rs_order
by (intro_classes)

(****************** to add it again ******************)

declare disj_not1 [simp]

end
