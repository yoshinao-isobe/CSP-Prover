           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                January 2006               |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory Infra_HOL
imports Infra_common
begin


(*--------------------------*
 |  exchange order in EX    |
 *--------------------------*)

lemma ex_comm3 : "(EX a b c . P a b c) = (EX c a b. P a b c)"
by (auto)

lemma ex_comm4: "(EX a b c d . P a b c d) = (EX d a b c. P a b c d)"
  by (auto)

lemma ex_comm5: "(EX a b c d e . P a b c d e) = (EX e a b c d . P a b c d e)"
  by (force)

lemma ex_comm6: "(EX a b c d e f . P a b c d e f) = (EX f a b c d e . P a b c d e f)"
  by (force)

lemma ex_comm7: "(EX a b c d e f g . P a b c d e f g) = (EX g a b c d e f. P a b c d e f g)"
  by (force)

lemma ex_comm8: "(EX a b c d e f g h . P a b c d e f g h) = (EX h a b c d e f g . P a b c d e f g h)"
  by (force)

lemma ex_rot_r: "(EX x y z. P x y z) = (EX z x y. P x y z)"
  by (auto)


(*--------------------------*
 |  exchange order in ALL   |
 *--------------------------*)

lemma exchange_forall_orderE:
  "[| ALL x y. P x y ; ALL y x. P x y ==> R |] ==> R"
by (simp)

lemma exchange_forall_order3E:
  "[| ALL x y z. P x y z ; ALL y z x. P x y z ==> R |] ==> R"
by (simp)

lemma exchange_ALL_BALL:
   "(ALL x:X. ALL y. P x y) = (ALL y. ALL x:X. P x y)"
apply (auto)
done

lemma ALL_BALL_fun:
   "(ALL y. ALL x:X. P x y) = (ALL f. ALL x:X. P x (f x))"
apply (auto)
done

lemma ALL_BALL_funE:
   "[| ALL y. ALL x:X. P x y ; (ALL f. ALL x:X. P x (f x)) ==> S |] ==> S"
apply (auto)
done

(*-------------------------------*
 |  distribution of ALL on conj  |
 *-------------------------------*)

lemma dist_ALL_conjI:
  "ALL x. (P x & Q x) ==> (ALL x. P x) & (ALL x. Q x)"
by (simp)

lemma dist_ALL_conjE:
  "[| ALL x. (P x & Q x) ; [| ALL x. P x ; ALL x. Q x |] ==> R |] ==> R"
by (simp)

lemma dist_ALL_conj: "(ALL x. P x & Q x) = ((ALL x. P x) & (ALL x. Q x)) "
by (auto)

lemma dist_ALL_conj2I:
  "ALL x y. (P x y & Q x y) ==> (ALL x y. P x y) & (ALL x y. Q x y)"
by (simp)

lemma dist_ALL_conj2E:
  "[| ALL x y. (P x y & Q x y) ; [| ALL x y. P x y ; ALL x y. Q x y |] ==> R |] ==> R"
by (simp)

lemma dist_ALL_conj2: "(ALL x y. P x y & Q x y) = ((ALL x y. P x y) & (ALL x y. Q x y)) "
by (auto)

(* BALL *)

lemma dist_BALL_conjI:
  "ALL x:X. (P x & Q x) ==> (ALL x:X. P x) & (ALL x:X. Q x)"
by (simp)

lemma dist_BALL_conjE:
  "[| ALL x:X. (P x & Q x) ;
      [| ALL x:X. P x ; ALL x:X. Q x |] ==> S
   |] ==> S"
by (simp)

lemma dist_BALL_conj2I:
  "ALL x:X. ALL y:(Y x). (P x y & Q x y) ==> 
   (ALL x:X. ALL y:(Y x). P x y) &
   (ALL x:X. ALL y:(Y x). Q x y)"
by (simp)

lemma dist_BALL_conj2E:
  "[| ALL x:X. ALL y:(Y x). (P x y & Q x y) ;
      [| ALL x:X. ALL y:(Y x). P x y ;
         ALL x:X. ALL y:(Y x). Q x y |] ==> S
   |] ==> S"
by (simp)

lemma dist_ALL_imply_conjE:
  "(ALL x. (b x) --> (P x & Q x))
   = ((ALL x. (b x) --> P x) & (ALL x. (b x) --> Q x))"
apply (auto)
done

(*****************************************************
                   ALL EX --> EX ALL
 *****************************************************)

(*** ALL ***)

lemma choice_ALL_EX_only_if:
  "ALL P. (ALL x. EX y. P x y) --> (EX f. ALL x. P x (f x))"
apply (intro allI impI)
apply (rule_tac x="(%x. SOME y. P x y)" in exI)
apply (rule allI)
apply (drule_tac x="x" in spec)
apply (erule exE)
apply (rule someI2)
apply (simp)
apply (simp)
done

lemma choice_ALL_EX:
  "(ALL x. EX y. P x y) = (EX f. ALL x. P x (f x))"
apply (rule)
apply (simp add: choice_ALL_EX_only_if)
apply (elim exE)
apply (rule allI)
apply (drule_tac x="x" in spec)
apply (rule_tac x="f x" in exI)
apply (simp)
done

(*** imply ***)

lemma choice_ALL_imply_EX_only_if:
  "ALL b P. (ALL x. (b x) --> (EX y. P x y)) --> (EX f. ALL x. (b x) --> P x (f x))"
apply (intro allI impI)
apply (rule_tac x="(%x. if (b x) then (SOME y. P x y) else (SOME y. True))" in exI)
apply (rule allI)
apply (drule_tac x="x" in spec)
apply (intro impI)
apply (simp)
apply (erule exE)
apply (rule someI2)
apply (simp)
apply (simp)
done

lemma choice_ALL_imply_EX:
  "(ALL x. (b x) --> (EX y. P x y)) = (EX f. ALL x. (b x) --> P x (f x))"
apply (rule)
apply (simp add: choice_ALL_imply_EX_only_if)
apply (elim exE)
apply (rule allI)
apply (drule_tac x="x" in spec)
apply (intro impI)
apply (rule_tac x="f x" in exI)
apply (simp)
done

(*** BALL ***)

lemma choice_BALL_EX:
  "(ALL x:X. EX y. P x y) = (EX f. ALL x:X. P x (f x))"
apply (simp add: Ball_def)
apply (simp add: choice_ALL_imply_EX)
done

(*****************************************************
                        EX!
 *****************************************************)

lemma ex1_implies_exE:
  "[| EX! x. P x ; EX x. P x ==> S |] ==> S"
by (auto)

(*** 1 ***)

lemma EX1_1I:
    "((EX X1. P X1 & (ALL Y1. P Y1 --> (Y1 = X1))))
 ==> (EX! X1. P X1)"
apply (simp add: Ex1_def)
done

(*** 2 ***)

lemma EX1_2I:
   "(EX X1 X2. P X1 X2 & (ALL Y1 Y2. P Y1 Y2 --> ((Y1 = X1) & (Y2 = X2))))
    ==> (EX! X1. EX! X2. P X1 X2)"
(* modified syntax for Isabelle 2017 *)
apply (simp add: Ex1_def)
apply (auto)
done

(*** 3 ***)

lemma EX1_3I:
   "(EX X1 X2 X3. P X1 X2 X3 & 
   (ALL Y1 Y2 Y3. P Y1 Y2 Y3 --> ((Y1 = X1) & (Y2 = X2) & (Y3 = X3))))
    ==> (EX! X1. EX! X2. EX! X3. P X1 X2 X3)"
apply (rule EX1_2I)
apply (elim conjE exE)
apply (rule_tac x="X1" in exI)
apply (rule_tac x="X2" in exI)
apply (rule conjI)
apply (rule EX1_1I)
apply (rule_tac x="X3" in exI)

apply (rule conjI)
apply (assumption)
apply (intro allI impI)
apply (drule_tac x="X1" in spec)
apply (drule_tac x="X2" in spec)
apply (drule_tac x="Y1" in spec)
apply (simp)

apply (intro allI impI)
apply (erule ex1E)
apply (drule_tac x="Y1" in spec)
apply (drule_tac x="Y2" in spec)
apply (drule_tac x="X3a" in spec)
apply (drule_tac x="X3a" in spec)
apply (simp)
done

(*** 4 ***)

lemma EX1_4I:
   "(EX X1 X2 X3 X4. P X1 X2 X3 X4 & 
   (ALL Y1 Y2 Y3 Y4. P Y1 Y2 Y3 Y4 
    --> ((Y1 = X1) & (Y2 = X2) & (Y3 = X3) & (Y4 = X4))))
    ==> (EX! X1. EX! X2. EX! X3. EX! X4. P X1 X2 X3 X4)"
apply (rule EX1_3I)
apply (elim conjE exE)
apply (rule_tac x="X1" in exI)
apply (rule_tac x="X2" in exI)
apply (rule_tac x="X3" in exI)
apply (rule conjI)
apply (rule EX1_1I)
apply (rule_tac x="X4" in exI)

apply (rule conjI)
apply (assumption)
apply (intro allI impI)
apply (drule_tac x="X1" in spec)
apply (drule_tac x="X2" in spec)
apply (drule_tac x="X3" in spec)
apply (drule_tac x="Y1" in spec)
apply (simp)

apply (intro allI impI)
apply (erule ex1E)
apply (drule_tac x="Y1" in spec)
apply (drule_tac x="Y2" in spec)
apply (drule_tac x="Y3" in spec)
apply (drule_tac x="X4a" in spec)
apply (drule_tac x="X4a" in spec)
apply (simp)
done

(*** 5 ***)

lemma EX1_5I:
   "(EX X1 X2 X3 X4 X5. P X1 X2 X3 X4 X5 & 
   (ALL Y1 Y2 Y3 Y4 Y5. P Y1 Y2 Y3 Y4 Y5
    --> ((Y1 = X1) & (Y2 = X2) & (Y3 = X3) & (Y4 = X4) & (Y5 = X5))))
    ==> (EX! X1. EX! X2. EX! X3. EX! X4. EX! X5. P X1 X2 X3 X4 X5)"
apply (rule EX1_4I)
apply (elim conjE exE)
apply (rule_tac x="X1" in exI)
apply (rule_tac x="X2" in exI)
apply (rule_tac x="X3" in exI)
apply (rule_tac x="X4" in exI)
apply (rule conjI)
apply (rule EX1_1I)
apply (rule_tac x="X5" in exI)

apply (rule conjI)
apply (assumption)
apply (intro allI impI)
apply (drule_tac x="X1" in spec)
apply (drule_tac x="X2" in spec)
apply (drule_tac x="X3" in spec)
apply (drule_tac x="X4" in spec)
apply (drule_tac x="Y1" in spec)
apply (simp)

apply (intro allI impI)
apply (erule ex1E)
apply (drule_tac x="Y1" in spec)
apply (drule_tac x="Y2" in spec)
apply (drule_tac x="Y3" in spec)
apply (drule_tac x="Y4" in spec)
apply (drule_tac x="X5a" in spec)
apply (drule_tac x="X5a" in spec)
apply (simp)
done

(*** 6 ***)

lemma EX1_6I:
   "(EX X1 X2 X3 X4 X5 X6. P X1 X2 X3 X4 X5 X6 & 
   (ALL Y1 Y2 Y3 Y4 Y5 Y6. P Y1 Y2 Y3 Y4 Y5 Y6
    --> ((Y1 = X1) & (Y2 = X2) & (Y3 = X3) & 
         (Y4 = X4) & (Y5 = X5) & (Y6 = X6))))
    ==> (EX! X1. EX! X2. EX! X3. EX! X4. EX! X5. EX! X6. 
         P X1 X2 X3 X4 X5 X6)"
apply (rule EX1_5I)
apply (elim conjE exE)
apply (rule_tac x="X1" in exI)
apply (rule_tac x="X2" in exI)
apply (rule_tac x="X3" in exI)
apply (rule_tac x="X4" in exI)
apply (rule_tac x="X5" in exI)
apply (rule conjI)
apply (rule EX1_1I)
apply (rule_tac x="X6" in exI)

apply (rule conjI)
apply (assumption)
apply (intro allI impI)
apply (drule_tac x="X1" in spec)
apply (drule_tac x="X2" in spec)
apply (drule_tac x="X3" in spec)
apply (drule_tac x="X4" in spec)
apply (drule_tac x="X5" in spec)
apply (drule_tac x="Y1" in spec)
apply (simp)

apply (intro allI impI)
apply (erule ex1E)
apply (drule_tac x="Y1" in spec)
apply (drule_tac x="Y2" in spec)
apply (drule_tac x="Y3" in spec)
apply (drule_tac x="Y4" in spec)
apply (drule_tac x="Y5" in spec)
apply (drule_tac x="X6a" in spec)
apply (drule_tac x="X6a" in spec)
apply (simp)
done


(* =================================================== *
 |             addition for CSP-Prover 6               |
 * =================================================== *)

abbreviation disjoint_range where
  "disjoint_range f g == ALL x y. f x ~= g y"

lemma not_disjoint_rangeI :
  "range f = range g \<Longrightarrow> \<not> disjoint_range f g"
  by (simp add: image_def, force)

lemma disjoint_range_iff_not_equal :
    "disjoint_range f g \<longleftrightarrow> range f \<inter> range g = {}"
  by (simp add: disjoint_iff_not_equal)

lemma disjoint_range_iff :
    "disjoint_range f g \<longleftrightarrow> (\<forall>x. x\<in>(range f) \<longrightarrow> x \<notin> (range g))"
  by (simp only: disjoint_range_iff_not_equal disjoint_iff)

lemma disjoint_range_eq_subset_Compl :
    "disjoint_range f g \<longleftrightarrow> (range f \<subseteq> - range g)"
  by (simp only: disjoint_range_iff_not_equal disjoint_eq_subset_Compl)

lemma disjoint_rangeI :
    "range f Int range g = {} ==> (disjoint_range f g)"
  by (simp only: disjoint_range_iff_not_equal)


lemma disjoint_range_commute :
    "disjoint_range f g \<longleftrightarrow> disjoint_range g f"
  by (simp only: disjoint_range_iff_not_equal Int_commute)

lemma disjoint_range_only_if :
    "disjoint_range f g \<Longrightarrow> range f Int range g = {}"
  by (simp only: disjoint_range_iff_not_equal)

lemma disjoint_range_only_if_commute :
    "disjoint_range f g \<Longrightarrow> disjoint_range g f"
  by (simp add: not_sym)


(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)

(* -----------
      no eq
 * ----------- *)

lemma add_not_eq_sym_funE: 
  "[| disjoint_range f g ; 
      [| (disjoint_range f g) & (disjoint_range g f) |] ==> R |] 
   ==> R"
apply (auto)
apply (subgoal_tac "(disjoint_range f g) = (disjoint_range g f)")
apply (auto)
apply (rotate_tac -1)
apply (drule sym)
apply (simp)
done

lemma add_not_eq_sym_cons_funE: 
  "[| ALL x. a ~= f x ; 
      [| (ALL x. a ~= f x) & (ALL x. f x ~= a) |] ==> R |] 
   ==> R"
by (auto)

lemma add_not_eq_sym_consE: 
  "[| a ~= b ; 
      [| a ~= b & b ~= a |] ==> R |] 
   ==> R"
by (auto)

lemmas add_not_eq_symE =
       add_not_eq_sym_funE
       add_not_eq_sym_cons_funE
       add_not_eq_sym_consE


end
