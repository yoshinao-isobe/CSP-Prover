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
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Infra_fun
imports Infra_order
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

end
