           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   June 2005  (modified)   |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2007         |
            |                January 2008  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                  April 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory Infra_fun
imports Infra_order
        Infra_HOL
begin

(*****************************************************
            Small lemmas for functions
 *****************************************************)
(*
consts
  inv_on :: "'a set => ('a => 'b) => 'b => 'a"
defs
  inv_on_def : "inv_on A f y == (SOME x. x:A & f x = y)"
*)

definition
  inv_on :: "'a set => ('a => 'b) => 'b => 'a"
  where
  inv_on_def : "inv_on A f y == (SOME x. x:A & f x = y)"

lemma inv_f_f_on: "[| inj_on f A ; x : A |] ==> inv_on A f (f x) = x"
apply (simp add: inj_on_def)
apply (simp add: inv_on_def)
apply (rule someI2)
apply (rule conjI)
apply (simp)
apply (simp)

apply (drule_tac x="x" in bspec, simp)
apply (drule_tac x="xa" in bspec, simp)
apply (simp)
done

(*****************************************************
                      fun (Product)
 *****************************************************)

(*******************************
        <= in fun
 *******************************)

(* instance fun :: (type, order) ord        <--- Isabelle 2005 *)
instance "fun" :: (type, order) ord      (* <--- Isabelle 2007 *)
by (intro_classes)

(*  Isabelle 2005

defs (overloaded)
  order_prod_def:
     "xp <= yp  ==  ALL x. (xp x <= yp x)"
  order_less_prod_def:
     "xp < yp  ==  (ALL x. (xp x <= yp x)) &
                   (EX  x. (xp x ~= yp x))"

order_prod_def --> le_fun_def
order_less_prod_def --> less_fun_def (in Isabelle 2007)
*)

lemmas order_prod_def = le_fun_def
lemmas order_less_prod_def = less_fun_def

lemma fold_order_prod_def: "(ALL x. (xp x <= yp x)) = (xp <= yp)"
by (simp add: le_fun_def)

(*** order in prod ***)

(* In Isabelle 2007   (Fun.tht)

instance "fun" :: (type, order) order
  by default
    (auto simp add: le_fun_def less_fun_def expand_fun_eq
       intro: order_trans order_antisym)
*)

(*
instance fun :: (type,order) order
apply (intro_classes)
apply (unfold order_prod_def order_less_prod_def)
apply (simp)
apply (blast intro: order_trans)

apply (simp add: expand_fun_eq)
apply (blast intro: order_antisym)

apply (auto simp add: expand_fun_eq)
done
*)

lemma order_prod_inv: "[| ALL x. f x <= g x |] ==> f <= g"
by (simp add: le_fun_def)

(*****************************************************
                   fun (Projection)
 *****************************************************)
(* isabelle 2013
consts
 proj_fun :: "'i => ('i => 'x) => 'x"

defs
 proj_fun_def : "proj_fun i == (%x. x i)"
*)

definition
 proj_fun :: "'i => ('i => 'x) => 'x"
 where
 proj_fun_def : "proj_fun i == (%x. x i)"

 
 (*** lub for projection ***)

(*** only if ***)

lemma prod_LUB_decompo_only_if:
  "x isLUB X ==> ALL i. (proj_fun i) x isLUB (proj_fun i) ` X"
apply (simp add: proj_fun_def)
apply (simp add: isLUB_def)
apply (auto)

 (*** upper ***)

apply (simp add: isUB_def)
apply (auto)
apply (drule_tac x="xa" in spec)
apply (simp add: le_fun_def)

 (*** least ***)

apply (drule_tac x="(%j. if (i=j) then y else (x j))" in spec)
apply (drule mp)

 apply (simp add: isUB_def)
 apply (intro allI impI)
 apply (simp add: le_fun_def)

 apply (simp add: le_fun_def)
 apply (drule_tac x="i" in spec)
 apply (simp)
done

(*** if ***)

lemma prod_LUB_decompo_if: 
  "ALL i. (proj_fun i) x isLUB (proj_fun i) ` X ==> x isLUB X"
apply (simp add: isLUB_def)
apply (rule conjI)

 (*** upper ***)

apply (simp add: isUB_def)
apply (auto)
apply (simp add: le_fun_def)
apply (intro allI)
apply (rename_tac y i)
apply (drule_tac x="i" in spec)

apply (erule conjE)
apply (drule_tac x="y i" in spec)
apply (simp add: proj_fun_def)

 (*** least ***)

apply (simp add: le_fun_def)
apply (intro allI)
apply (rename_tac y i)
apply (drule_tac x="i" in spec)

apply (erule conjE)
apply (drule_tac x="y i" in spec)
apply (simp add: proj_fun_def)
apply (drule mp)

 apply (simp add: isUB_def)
 apply (intro allI impI)
 apply (simp add: image_def)
 apply (erule bexE)
 apply (drule_tac x="xa" in spec)
 apply (simp add: le_fun_def)
 apply (simp)
done

(*** iff ***)

lemma prod_LUB_decompo: 
  "x isLUB X = (ALL i. (proj_fun i) x isLUB (proj_fun i) ` X)"
apply (rule iffI)
apply (simp add: prod_LUB_decompo_only_if)
apply (simp add: prod_LUB_decompo_if)
done

(*****************************************************
                       mono
 *****************************************************)

lemma prod_mono_only_if: 
  "mono f ==> mono ((proj_fun i) o f)"
apply (simp add: proj_fun_def)
apply (simp add: mono_def)
apply (simp add: le_fun_def)
done

lemma prod_mono_if: 
  "(ALL i. mono ((proj_fun i) o f)) ==> mono f"
apply (simp add: mono_def)
apply (simp add: proj_fun_def)
apply (simp add: le_fun_def)
done

lemma prod_mono: 
  "mono f = (ALL i. mono ((proj_fun i) o f))"
apply (rule iffI)
apply (simp add: prod_mono_only_if)
apply (simp add: prod_mono_if)
done

(********************************************************** 
         some preparation for fixed point induction
 **********************************************************)
(* Isabelle 2016
consts
  inductivefun :: "('a => bool) => ('a => 'a) => bool"

  Ref_fun :: "'a::order => 'a => bool"
  Rev_fun :: "'a::order => 'a => bool"

defs
 inductivefun_def :
     "inductivefun R f == (ALL x. R x --> R (f x))"

  Ref_fun_def : "Ref_fun X == (%Y. (X <= Y))"
  Rev_fun_def : "Rev_fun X == (%Y. (Y <= X))"
*)

definition
  inductivefun :: "('a => bool) => ('a => 'a) => bool"
  where
  "inductivefun R f == (ALL x. R x --> R (f x))"
  
definition  
  Ref_fun :: "'a::order => 'a => bool"
  where
  "Ref_fun X == (%Y. (X <= Y))"
  
definition  
  Rev_fun :: "'a::order => 'a => bool"
  where
  "Rev_fun X == (%Y. (Y <= X))"

lemma inductivefun_all_n:
(*  "[| inductivefun R f ; R x |] ==> (ALL n. R ((f ^ n) x))"   Isabelle2009 *)
  "[| inductivefun R f ; R x |] ==> (ALL n. R ((f ^^ n) x))"
apply (intro allI)
apply (induct_tac n)
apply (simp)
apply (simp add: inductivefun_def)
done

(*----------------------------------------------------------*
              simplify inverse functions
 *----------------------------------------------------------*)

lemma Pr1_inv_inj[simp]:
  "inj f ==> (ALL x. Pr (inv f x)) = (ALL y. Pr y)"
apply (auto)
apply (drule_tac x="f y" in spec)
by (simp)

lemma Pr2_inv_inj[simp]:
  "inj f ==> (ALL x. Pr1 (Pr2 (inv f x))) = (ALL y. Pr1 (Pr2 y))"
apply (auto)
apply (drule_tac x="f y" in spec)
by (simp)

lemma Pr3_inv_inj[simp]:
  "inj f ==> (ALL x. Pr1 (Pr2 (Pr3 (inv f x)))) = (ALL y. Pr1 (Pr2 (Pr3 y)))"
apply (auto)
apply (drule_tac x="f y" in spec)
by (simp)




(* =================================================== *
 |             addition for CSP-Prover 6               |
 * =================================================== *)


section \<open> Range lemmas \<close>

lemma range_nonempty [simp]:
   "(range f) \<noteq> {}"
  by (simp add: image_def, auto)

lemma range_Un_nonempty [simp]:
   "(range f) \<union> (range g) \<noteq> {}"
  by (simp add: image_def, auto)

lemma range_Un_commute :
    "(range f \<union> range g) = (range g \<union> range f)"
  by (auto)


subsection \<open> Range and Set Minus \<close>

lemma singleton_minus_range [simp]:
    "{f x} - (range f) = {}"
  by (simp add: image_def, auto)

lemma range_minus_self [simp]:
    "(range f) - (range f) = {}"
  by (simp add: image_def)

lemma range_minus_range_Un_self_l [simp]:
    "((range f) - (range f \<union> range g)) = {}"
  by (auto)

lemma range_minus_range_Un_self_r [simp]:
    "((range f) - (range g \<union> range f)) = {}"
  by (auto)


subsection \<open> Disjoint Range and Set Minus \<close>

lemma disjoint_singleton_minus_range [simp]:
    "disjoint_range f g \<Longrightarrow> {f x} - (range g) = {f x}"
  by (simp add: image_def, auto)

lemma disjoint_range_singleton_minus_range_Un [simp]:
    "disjoint_range g f \<Longrightarrow> disjoint_range g h \<Longrightarrow> {g x} - (range f \<union> range h) = {g x}"
  by (simp add: image_def, auto)

lemma disjoint_range_range_minus [simp]:
    "disjoint_range f g \<Longrightarrow> (range f) - (range g) = (range f)"
  by (auto)

lemma disjoint_range_range_minus_range_Un [simp]:
    "disjoint_range f g \<Longrightarrow> disjoint_range f h \<Longrightarrow> ((range f) - (range g \<union> range h)) = (range f)"
  by (auto)

lemma disjoint_range_range_Un_minus_range_Un [simp]:
    "disjoint_range g f \<Longrightarrow> disjoint_range g h \<Longrightarrow> (range f \<union> range g) - (range f \<union> range h) = (range g)"
  by (auto)


subsection \<open> Range and Membership \<close>

(* lemmas singleton_in_range = rangeI *)


subsection \<open> Disjoint Range and Membership \<close>

lemma disjoint_range_singleton_notin_range [simp]:
    "disjoint_range f g \<Longrightarrow> f x \<notin> (range g)"
  by (simp add: image_def)

lemma not_in_two_disjoint_ranges [simp]:
    "disjoint_range f g \<Longrightarrow> \<not> (x \<in> (range f) \<and> x \<in> (range g))"
  by (auto)


subsection \<open> Range and Intersection \<close>

lemma insert_range_Int_self [simp]:
    "e \<notin> (range f) \<Longrightarrow> insert e (range f) \<inter> (range f) = (range f)"
  by (auto)

lemma singleton_inter_range_self [simp]: "{f x} \<inter> (range f) = {f x}"
  by (simp add: image_def, auto)

lemma range_inter_self_singleton [simp]: "(range f) \<inter> {f x} = {f x}"
  by (simp add: image_def, auto)


subsection \<open> Disjoint Range and Intersection \<close>

(*lemma disjoint_range_range_inter_singleton [simp]:
   "disjoint_range f g \<Longrightarrow> (range g) \<inter> {f x} = {}"
  by (auto)*)

lemma disjoint_range_range_Un_inter_range_Un [simp]:
    "disjoint_range g h \<Longrightarrow> (range f \<union> range g) \<inter> (range f \<union> range h) = (range f)"
  by (auto)

lemma range_Un_inter_range_l [simp]: "(range f \<union> range g) \<inter> (range f) = (range f)"
  by (auto)

lemma range_Un_inter_range_r [simp]: "(range f \<union> range g) \<inter> (range g) = (range g)"
  by (auto)

lemma disjoint_range_range_Un_inter_range [simp]:
    "disjoint_range h g \<Longrightarrow> disjoint_range h f \<Longrightarrow> (range f \<union> range g) \<inter> (range h) = {}"
  by (auto)



end
