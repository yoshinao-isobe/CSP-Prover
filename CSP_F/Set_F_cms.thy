           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                 August 2005  (modified)   |
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
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Set_F_cms
imports Set_F CSP.RS
begin

(*****************************************************************

         1. 
         2. 
         3. 
         4. 

 *****************************************************************)

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  Union (B ` A) = (UN x:A. B x)                      *)
(*                  Inter (B ` A) = (INT x:A. B x)                     *)
(*
declare Union_image_eq [simp del]
declare Inter_image_eq [simp del]
*)
(* no simp rules in Isabelle 2017 
declare Sup_image_eq [simp del]
declare Inf_image_eq [simp del]
*)

(*********************************************************
                 Restriction in Set_F
 *********************************************************)

(* Isabelle 2009-1
instance setF :: (type) ms0
by (intro_classes)
*)

definition
  restF      :: "'a setF => nat => 'a failure set" ("_ restF _" [84,900] 84)
  where
 restF_def : 
   "F restF n == {(s, X) |s X. (s, X) :f F &
                  (lengtht s < n |
                   lengtht s = n & (EX s'. s = s' ^^^ <Tick> & noTick s'))}"

definition                   
  LimitF     :: "'a setF infinite_seq => 'a failure set"
  where
  LimitF_def : 
   "LimitF Fs == {(s, X) |s X. 
           ((s, X) :f Fs (Suc (lengtht s)) |
            (s, X) :f Fs (lengtht s) & (EX s'. s = s' ^^^ <Tick> & noTick s'))}"
  
definition
  Limit_setF :: "'a setF infinite_seq => 'a setF"
  where
  Limit_setF_def :
   "Limit_setF Fs == Abs_setF (LimitF Fs)"

(* isabelle 2009-2 *)

instantiation setF :: (type) rs0
begin

definition
  rest_setF_def : "F .|. n == Abs_setF (F restF n)"

  instance ..

end

(* isabelle 2009-1
defs (overloaded)
  rest_setF_def : "F .|. n == Abs_setF (F restF n)"
*)

(*--------------------------------------------------------*
 |  The reason why restF deals specially with [Tick]      |
 |  can be found in the proof of lemma "restFpair_T3_F4"  |
 |  in Domain_F_cms.thy.                                  |
 *--------------------------------------------------------*)

(*********************************************************
              Lemmas (Restriction in Set_F)
 *********************************************************)

(*** restF_def in setF ***)

lemma restF_in[simp] : "F restF n : setF"
apply (simp add: restF_def)
apply (simp add: setF_def HC_F2_def)
apply (intro allI impI)
apply (elim conjE)
apply (rule memF_F2)
by (simp_all)

(*********************************************************
                     .|. on setF
 *********************************************************)

lemma rest_setF_iff: "F .|. n = 
                  {f. EX s X. f = (s, X) & (s, X) :f F &
                  (lengtht s < n |
                   lengtht s = n & (EX s'. s = s' ^^^ <Tick> & noTick s'))}f"
apply (simp add: rest_setF_def)
apply (subgoal_tac
    "{(s, X).
     (s, X) :f F &
     (lengtht s < n |
      lengtht s = n & (EX s'. s = s' ^^^ <Tick> & noTick s'))} : setF")
apply (simp add: Abs_setF_inject)
apply (simp add: restF_def)
apply (insert restF_in[simplified restF_def])
apply (auto)
done

lemma in_rest_setF: "(s, X) :f F .|. n = 
                 ((s, X) :f F &
                (lengtht s < n |
                 lengtht s = n & (EX s'. s = s' ^^^ <Tick> & noTick s')))"
apply (simp add: memF_def rest_setF_def)
apply (simp add: Abs_setF_inverse)
apply (simp add: memF_def restF_def)
done

lemma rest_setF_eq_iff:
   "(F .|. n = E .|. m) =
    (ALL s X. 
         ((s, X) :f F &
          (lengtht s < n |
           lengtht s = n & (EX s'. s = s' ^^^ <Tick> & noTick s')))
       = ((s, X) :f E &
          (lengtht s < m |
           lengtht s = m & (EX s'. s = s' ^^^ <Tick> & noTick s'))))"
apply (simp add: rest_setF_def Abs_setF_inject)
apply (simp add: restF_def)
by (auto)

(*** F .|. = E .|. --> F = E ***)

lemma rest_setF_eq: 
  "[| (s, X) :f F ; F restF Suc (lengtht s) = 
                    E restF Suc (lengtht s) |]
   ==> (s, X) :f E"
by (auto simp add: restF_def)

(*********************************************************
                     SetF --> RS
 *********************************************************)

(*******************************
        zero_eq_rs_setF
 *******************************)

(*** (contra) restF 0 ***)

lemma contra_zero_setF: "(F::'a setF) restF n ~= {} ==> 0 < n"
apply (simp add: restF_def)
apply (elim conjE exE)
apply (erule disjE)
apply (simp)

apply (elim conjE exE)
by (simp)

(*** restF 0 ***)

lemma zero_setF: "(F::'a setF) restF 0 = {}"
apply (insert contra_zero_setF[of F 0])
apply (case_tac "F restF 0 = {}")
by (simp_all)

(*** zero_eq_rs_setF ***)

lemma zero_rs_setF: "(F::'a setF) .|. 0 = {}f"
apply (simp add: rest_setF_def empF_def Abs_setF_inject)
apply (simp add: zero_setF)
done

lemma zero_eq_rs_setF: "(F::'a setF) .|. 0 = E .|. 0"
by (simp add: zero_rs_setF)

(*******************************
         min_rs_setF
 *******************************)

lemma min_rs_setF:
  "((F::'a setF) .|. m) .|. n = F .|. (min m n)"
apply (simp add: rest_setF_eq_iff)
apply (simp add: in_rest_setF)
apply (intro allI)
apply (rule iffI)

apply (elim conjE exE disjE)
apply (simp_all add: min_is)
apply (rule_tac x="s'" in exI, simp)+

apply (elim conjE exE disjE)
apply (simp_all)

apply (case_tac "m < n")
apply (simp add: min_is)
apply (rule_tac x="s'" in exI, simp)

apply (case_tac "m = n")
apply (simp add: min_is)
apply (rule_tac x="s'" in exI, simp)

apply (case_tac "n < m")
apply (simp add: min_is)
apply (rule_tac x="s'" in exI, simp)

by (force)

(*******************************
        diff_rs_setF
 *******************************)

(*** contra <= ***)

lemma contra_diff_rs_setF_left: 
  "(ALL n. (F::'a setF) .|. n = E .|. n) ==> F <= E"
apply (simp add: rest_setF_eq_iff)
apply (rule subsetFI)
apply (drule_tac x="Suc (lengtht s)" in spec)
apply (drule_tac x="s" in spec)
apply (drule_tac x="X" in spec)
by (simp)

(*** contra = ***)

lemma contra_diff_rs_setF: 
  "(ALL n. (F::'a setF) .|. n = E .|. n) ==> F = E"
apply (rule order_antisym)
by (simp_all add: contra_diff_rs_setF_left)

(*** diff_rs_setF ***)

lemma diff_rs_setF: 
  "(F::'a setF) ~= E ==> (EX (n::nat). F .|. n ~= E .|. n)"
apply (erule contrapos_np)
apply (rule contra_diff_rs_setF)
by (simp)

(***************************************************************
                        setF ==> RS
 ***************************************************************)

instance setF :: (type) rs
apply (intro_classes)
apply (simp add: zero_eq_rs_setF)
apply (simp add: min_rs_setF)
apply (simp add: diff_rs_setF)
done

(************************************************************
                        setF ==> MS
 ************************************************************)


instantiation setF :: (type) ms0
begin

definition
  setF_distance_def:
     "distance (FF::('a setF * 'a setF)) = distance_rs FF"
  instance ..
end

instance setF :: (type) ms
apply (intro_classes)
apply (simp_all add: setF_distance_def)
apply (simp add: diagonal_rs)
apply (simp add: symmetry_rs)
apply (simp add: triangle_inequality_rs)
done

(************************************************************
                 i.e.  setF ==> MS & RS 
 ************************************************************)

instance setF :: (type) ms_rs
apply (intro_classes)
apply (simp add: setF_distance_def)
done

(***********************************************************
                      lemmas (Limit)
 ***********************************************************)

(*** normal_seq lemma ***)

lemma normal_seq_setF_less:
  "[| normal (Fs::'a setF infinite_seq) ; lengtht s < n |]
   ==> ((s,X) :f Fs (Suc (lengtht s))) = ((s,X) :f Fs n)"
apply (simp add: normal_def)
apply (drule_tac x="Suc (lengtht s)" in spec)
apply (drule_tac x="n" in spec)
apply (simp add: to_distance_rs)
apply (simp add: distance_rs_le_1[THEN sym])
apply (simp add: min_is)

apply (simp add: rest_setF_eq_iff)
apply (drule_tac x="s" in spec)
apply (drule_tac x="X" in spec)
by (simp)

lemma normal_seq_setF_less_only_if:
  "[| normal (Fs::'a setF infinite_seq) ; lengtht s < n ;
      (s,X) :f Fs (Suc (lengtht s)) |]
   ==> ((s,X) :f Fs n)"
by (simp add: normal_seq_setF_less)

(*** normal_seq lemma (Tick)***)

lemma normal_seq_setF_Tick:
  "[| normal (Fs::'a setF infinite_seq) ; lengtht (s' ^^^ <Tick>) <= n ;
      noTick s' |]
   ==> ((s' ^^^ <Tick>,X) :f Fs (lengtht (s' ^^^ <Tick>))) = 
       ((s' ^^^ <Tick>,X) :f Fs n)"
apply (simp add: normal_def)
apply (drule_tac x="lengtht (s' ^^^ <Tick>)" in spec)
apply (drule_tac x="n" in spec)
apply (simp add: to_distance_rs)
apply (simp add: distance_rs_le_1[THEN sym])
apply (simp add: min_is)

apply (simp add: rest_setF_eq_iff)
apply (drule_tac x="s' ^^^ <Tick>" in spec)
apply (drule_tac x="X" in spec)
apply (simp)

apply (rule)
 apply (erule iffE)
 apply (drule mp)
 apply (rule conjI)
 apply (simp)
 apply (simp)
 apply (rule_tac x="s'" in exI)
 apply (simp)
 apply (simp)

 apply (erule iffE)
 apply (rotate_tac -1)
 apply (drule mp)
 apply (rule conjI)
 apply (simp)
 apply (simp)
 apply (rule_tac x="s'" in exI)
 apply (simp)
 apply (simp)
done

lemma normal_seq_setF_Tick_only_if:
  "[| normal (Fs::'a setF infinite_seq) ; lengtht (s' ^^^ <Tick>) <= n ;
      (s' ^^^ <Tick>,X) :f Fs (lengtht (s' ^^^ <Tick>)) ; noTick s' |]
   ==> ((s' ^^^ <Tick>,X) :f Fs n)"
by (simp only: normal_seq_setF_Tick)

lemma normal_seq_setF_Tick_only_ifE:
  "[| (s' ^^^ <Tick>,X) :f Fs n ; 
      normal (Fs::'a setF infinite_seq) ; lengtht (s' ^^^ <Tick>) <= n ; noTick s' ;
      (s' ^^^ <Tick>,X) :f Fs (lengtht (s' ^^^ <Tick>)) ==> R |]
   ==> R"
by (simp only: normal_seq_setF_Tick)

(*** LimitF_def in setF ***)

lemma LimitF_in[simp]:
  "LimitF (Fs::'a setF infinite_seq) : setF"
apply (simp add: LimitF_def)
apply (simp add: setF_def HC_F2_def)
apply (intro allI impI)
apply (erule conjE)
apply (erule disjE)

apply (rule disjI1)
apply (rule memF_F2)
apply (simp_all)

apply (elim conjE exE)
apply (rule disjI2)
apply (rule memF_F2)
apply (simp_all)
done

(*** Limit_setF_memF ***)

lemma Limit_setF_memF: 
  "((s, X) :f Limit_setF Fs) = 
   ((s, X) :f Fs (Suc (lengtht s)) |
    (s, X) :f Fs (lengtht s) & (EX s'. s = s' ^^^ <Tick> & noTick s'))"
apply (simp add: Limit_setF_def memF_def)
apply (simp add: Abs_setF_inverse)
apply (simp add: LimitF_def memF_def)
done

(*** Limit_setF lemma ***)

lemma Limit_setF_Limit_lm:
  "normal (Fs::'a setF infinite_seq)
   ==> (ALL n. (Limit_setF Fs) .|. n = (Fs n) .|. n)"
apply (simp add: rest_setF_eq_iff)
apply (intro allI)
apply (simp add: Limit_setF_memF)
apply (rule iffI)

(* => *)
apply (elim conjE disjE)
apply (simp_all add: normal_seq_setF_less)

apply (elim conjE exE)
apply (simp)
apply (erule normal_seq_setF_Tick_only_ifE)
apply (simp_all)

apply (elim conjE exE)
apply (simp)
apply (rule normal_seq_setF_Tick_only_if)
apply (simp_all)

(* <= *)
apply (elim conjE disjE)
apply (simp add: normal_seq_setF_less)
apply (simp)
done

(*** (normal) Fs converges to (Limit_setF Fs) ***)

lemma Limit_setF_Limit:
  "normal (Fs::'a setF infinite_seq) ==> Fs convergeTo (Limit_setF Fs)"
by (simp add: to_distance_rs Limit_setF_Limit_lm rest_Limit)

(*** (cauchy) Fs converges to (Limit_setF NF Fs) ***)

lemma cauchy_Limit_setF_Limit:
  "cauchy (Fs::'a setF infinite_seq) ==> Fs convergeTo (Limit_setF (NF Fs))"
apply (simp add: normal_form_seq_same_Limit)
apply (simp add: Limit_setF_Limit normal_form_seq_normal)
done

(************************************
    SetF --> Complete Metric Space
 ************************************)

lemma setF_cms:
  "cauchy (Fs::'a setF infinite_seq) ==> (EX F. Fs convergeTo F)"
apply (rule_tac x="Limit_setF (NF Fs)" in exI)
by (simp add: cauchy_Limit_setF_Limit)

(************************************************************
                   setF ==> CMS and RS
 ************************************************************)

instance setF :: (type) cms
apply (intro_classes)
by (simp add: setF_cms)

instance setF :: (type) cms_rs
by (intro_classes)

(*** (normal) Limit Fs = Limit_setF Fs ***)

lemma Limit_setF_Limit_eq:
  "normal (Fs::'a setF infinite_seq) ==> Limit Fs = Limit_setF Fs"
apply (insert unique_convergence[of Fs "Limit Fs" "Limit_setF Fs"])
by (simp add:  Limit_setF_Limit Limit_is normal_cauchy)

(*----------------------------------------------------------*
 |                                                          |
 |                       cms rs order                       |
 |                                                          |
 *----------------------------------------------------------*)

instance setF :: (type) ms_rs_order0
apply (intro_classes)
done

instance setF :: (type) ms_rs_order
apply (intro_classes)
apply (intro allI)
apply (rule iffI)
apply (simp add: rest_setF_def)
apply (simp add: subsetF_def)
apply (simp add: Abs_setF_inverse)
apply (fold subsetF_def)
apply (rule)
apply (drule_tac x="Suc (lengtht s)" in spec)
apply (simp add: restF_def)
apply (erule subsetE)
apply (simp)

apply (intro allI)
apply (simp add: rest_setF_def)
apply (simp add: subsetF_def)
apply (simp add: Abs_setF_inverse)
apply (fold subsetF_def)
apply (rule)
apply (simp add: restF_def)
apply (force)
done

instance setF :: (type) cms_rs_order
by (intro_classes)

(*----------------------------------------------------------*
 |                                                          |
 |  i.e. lemma "continuous_rs (Ref_fun (S::'a setF))"       |
 |       by (simp add: continuous_rs_Ref_fun)               |
 |                                                          |
 |  see RS.thy                                              |
 |                                                          |
 *----------------------------------------------------------*)

(****************** to add them again ******************)
(*
declare Union_image_eq [simp]
declare Inter_image_eq [simp]
*)
(*
declare Sup_image_eq [simp]
declare Inf_image_eq [simp]
*)
end
