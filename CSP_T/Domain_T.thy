           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Domain_T
imports CSP.Prefix
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

(* for Isabelle 2013
declare Union_image_eq [simp del]
declare Inter_image_eq [simp del]
*)
(* no simp rules in Isabelle 2017 
declare Sup_image_eq [simp del]
declare Inf_image_eq [simp del]
*)

(***********************************************************
                 type def (Trace Part)
 ***********************************************************)

definition
  HC_T1    :: "'a trace set => bool"
  where
  HC_T1_def : "HC_T1 T == (T ~= {} & prefix_closed T)"

definition "domT  = {T::('a trace set). HC_T1(T)}"
typedef 'a domT = "domT :: 'a trace set set"
(* typedef 'a domT = "{T::('a trace set). HC_T1(T)}" *)
apply (rule_tac x ="{<>}" in exI)
apply (simp add: domT_def)
by (simp add: HC_T1_def prefix_closed_def)

declare Rep_domT         [simp]

(***********************************************************
                   operators on domT
 ***********************************************************)

definition
  memT     :: "'a trace => 'a domT => bool"  ("(_/ :t _)" [50, 51] 50)
  where
  memT_def     : "x :t T     == x : (Rep_domT T)"
  
definition  
  CollectT :: "('a trace => bool) => 'a domT"("CollectT")
  where
  CollectT_def : "CollectT P == Abs_domT (Collect P)"
  
definition  
  UnionT   :: "'a domT set => 'a domT"       ("UnionT _" [90] 90)
  where
  UnionT_def   : "UnionT Ts  == Abs_domT (Union (Rep_domT ` Ts))"
  
definition  
  InterT   :: "'a domT set => 'a domT"       ("InterT _" [90] 90)
  where
  InterT_def   : "InterT Ts  == Abs_domT (Inter (Rep_domT ` Ts))"

definition  
  empT     :: "'a domT"                      ("{}t")
  where
  empT_def     : "{}t        == Abs_domT {}"
  
definition  
  UNIVT    :: "'a domT"                      ("UNIVt")
  where
  UNIVT_def    : "UNIVt      == Abs_domT UNIV"

(******** X-symbols ********)
(*
notation (xsymbols) memT ("(_/ \<in>t _)" [50, 51] 50)
notation (xsymbols) UnionT ("\<Union>t _" [90] 90)
notation (xsymbols) InterT ("\<Inter>t _" [90] 90)
*)
(******** syntactic sugar ********)

abbreviation
 nonmemT :: "'a trace => 'a domT => bool"   ("(_/ ~:t _)" [50, 51] 50)
 where "x ~:t T == ~ x :t T"

abbreviation
 UnT :: "'a domT => 'a domT => 'a domT" ("_ UnT _" [65,66] 65)
 where "T UnT S == UnionT {T,S}"

abbreviation
 IntT :: "'a domT => 'a domT => 'a domT" ("_ IntT _" [70,71] 70)
 where "T IntT S == InterT {T,S}"


syntax
  "@CollT"    :: "pttrn => bool => 'a domT"      ("(1{_./ _}t)" [1000,10] 1000)
  "@FindomT"  :: "args => 'a domT"               ("{(_)}t" [1000] 1000)

translations
  "{x. P}t"    == "CONST Abs_domT {x. P}"  (* "CONST" for isabelle2009-2 *)
  "{X}t"       == "CONST Abs_domT {X}"     (* "CONST" for isabelle2009-2 *)

(******** X-symbols ********)
(*
notation (xsymbols) nonmemT ("(_/ \<notin>t _)" [50, 51] 50)
notation (xsymbols) UnT  ("_ \<union>t _" [65,66] 65)
notation (xsymbols) IntT ("_ \<inter>t _" [70,71] 70)
*)
(*********************************************************
          The relation (<=) is defined over domT
 *********************************************************)

instantiation domT :: (type) ord 
begin
definition
  subdomT_def:
     "T <= S  ==  (Rep_domT T) <= (Rep_domT S)"
definition
  psubdomT_def:
     "T < S  ==  (Rep_domT T) < (Rep_domT S)"

instance ..

end

(*********************************************************
          The relation (<=) is a partial order
 *********************************************************)

instance domT :: (type) order
apply (intro_classes)
apply (unfold subdomT_def psubdomT_def)
(*apply (simp add: less_fun_def)                (* isabelle 2009-2011 !! *)*)

apply (simp only: order_less_le Rep_domT_inject)
apply (auto simp add: Rep_domT_inject)
done

(***********************************************************
                          lemmas
 ***********************************************************)

(*******************************
             basic
 *******************************)

lemma domT_is_non_empty: "T:domT ==> T ~= {}"
by (simp add: domT_def HC_T1_def)

lemma domT_is_prefix_closed: 
  "T:domT ==> prefix_closed T"
by (simp add: domT_def HC_T1_def)

lemma domT_is_prefix_closed_unfold: 
  "[| T:domT ; t : T ; prefix s t |] ==> s : T"
apply (simp add: domT_def HC_T1_def)
apply (rule prefix_closed_iff)
by (simp_all)

lemma Rep_domT_is_prefix_closed_unfold:
    "[| t : Rep_domT T ; prefix s t |] ==> s : Rep_domT T"
by (rule domT_is_prefix_closed_unfold, simp_all)

(*** {<>} in domT ***)

lemma nilt_set_in[simp]: "{<>} : domT"
by (simp add: domT_def HC_T1_def prefix_closed_def)

(*** {<>, <a>} in domT ***)

lemma one_t_set_in[simp]: "{<>,  <a>} : domT"
apply (simp add: domT_def HC_T1_def)
apply (simp add: prefix_closed_def)
apply (intro allI impI)
apply (erule exE)
apply (erule conjE)
apply (erule disjE)
by (simp_all)

(* <> is contained in all domT *)

lemma nilt_in_all_dom: "T : domT ==> <> : T"
apply (simp add: domT_def HC_T1_def)
apply (erule conjE)
apply (subgoal_tac "EX t. t : T")
apply (erule exE)
apply (rule prefix_closed_iff)
by (auto)

(*******************************
        check in domT 
 *******************************)

lemma empty_notin_domT [simp]: "{} ~: domT"        
by (simp add: domT_def HC_T1_def)

lemma UNIV_in_domT [simp]: "UNIV : domT"
by (simp add: domT_def HC_T1_def prefix_closed_def)

(*** Union ***)

lemma domT_Union_in_domT:
  "Ts ~= {} ==> (Union (Rep_domT ` Ts)) : domT"
apply (simp add: domT_def HC_T1_def)
apply (simp add: prefix_closed_def)
apply (rule conjI)

apply (subgoal_tac "EX T. T : Ts")
apply (erule exE)
apply (rule_tac x="T" in bexI)
apply (simp add: domT_is_non_empty)
apply (simp)
apply (force)

apply (intro allI impI)
apply (elim conjE exE bexE)
apply (rule_tac x="x" in bexI)

apply (rule prefix_closed_iff, simp_all)
apply (rule domT_is_prefix_closed)
apply (simp)
done

(*** Un ***)

lemma domT_Un_in_domT:
  "(Rep_domT T Un Rep_domT S) : domT"
apply (insert domT_Union_in_domT[of "{T,S}"])
by (simp)

(*** Inter ***)

lemma domT_Inter_in_domT: 
  "(Inter (Rep_domT ` Ts)) : domT"
apply (simp add: domT_def HC_T1_def)
apply (rule conjI)
apply (subgoal_tac "<> : Inter (Rep_domT ` Ts)", force)
(* apply (simp add: Inter_def)  Isabelle 2012 *)
apply (simp add: nilt_in_all_dom)

apply (simp add: prefix_closed_def)
apply (intro allI impI ballI)
apply (elim conjE exE)
apply (drule_tac x="x" in bspec, simp)

apply (rule prefix_closed_iff, simp_all)
apply (simp add: domT_is_prefix_closed)
done

(*** Int ***)

lemma domT_Int_in_domT:
  "(Rep_domT T Int Rep_domT S) : domT"
apply (insert domT_Inter_in_domT[of "{T,S}"])
by (simp)

lemmas in_domT = domT_Union_in_domT domT_Un_in_domT
                 domT_Inter_in_domT domT_Int_in_domT

(*******************************
    domT type --> set type
 *******************************)

(*** UnionT ***)

(* declare [[simp_trace]] *)

lemma domT_UnionT_Rep:
  "Ts ~= {} ==> Rep_domT (UnionT Ts) = Union (Rep_domT ` Ts)"
apply (simp add: UnionT_def)
apply (simp add: Abs_domT_inverse in_domT)
done

(*** UnT ***)

lemma domT_UnT_Rep:
  "Rep_domT (T UnT S) = (Rep_domT T) Un (Rep_domT S)"
by (simp add: domT_UnionT_Rep)

(*** InterT ***)

lemma domT_InterT_Rep:
  "Rep_domT (InterT Ts) = Inter (Rep_domT ` Ts)"
by (simp add: InterT_def Abs_domT_inverse in_domT)

(*** IntT ***)

lemma domT_IntT_Rep:
  "Rep_domT (T IntT S) = (Rep_domT T) Int (Rep_domT S)"
by (simp add: domT_InterT_Rep)

(*********************************************************
                       memT
 *********************************************************)

(* prefix closed *)

lemma memT_prefix_closed:
  "[| t :t T ; prefix s t |] ==> s :t T"
apply (simp add: memT_def)
apply (rule domT_is_prefix_closed_unfold)
by (simp_all)

(* <> *)

lemma nilt_in_T[simp]: "<> :t T"
by (simp add: memT_def nilt_in_all_dom)

(* UnionT *)

lemma memT_UnionT_only_if:
  "[| Ts ~= {} ; t :t UnionT Ts |] ==> EX T:Ts. t :t T"
by (simp add: memT_def domT_UnionT_Rep)

lemma memT_UnionT_if:
  "[| T:Ts ; t :t T |] ==> t :t UnionT Ts"
apply (subgoal_tac "Ts ~= {}")
apply (simp add: memT_def domT_UnionT_Rep)
apply (rule_tac x="T" in bexI)
by (auto)

lemma memT_UnionT[simp]:
  "Ts ~= {} ==> t :t UnionT Ts = (EX T:Ts. t :t T)"
apply (rule iffI)
apply (simp add: memT_UnionT_only_if)
by (auto simp add: memT_UnionT_if)

(* InterT *)

lemma memT_InterT_only_if:
  "t :t InterT Ts ==> ALL T:Ts. t :t T"
by (simp add: memT_def domT_InterT_Rep)

lemma memT_InterT_if:
  "ALL T:Ts. t :t T ==> t :t InterT Ts"
by (simp add: memT_def domT_InterT_Rep)

lemma memT_InterT[simp]:
  "t :t InterT Ts = (ALL T:Ts. t :t T)"
apply (rule iffI)
apply (rule memT_InterT_only_if, simp_all)
by (simp add: memT_InterT_if)

(* <> *)

lemma memT_nilt[simp]: "t :t {<>}t = (t = <>)"
by (simp add: memT_def Abs_domT_inverse)

(* [e]t, <> *)

lemma memT_nilt_one[simp]: "t :t {<>, <a>}t = (t = <> | t = <a>)"
by (simp add: memT_def Abs_domT_inverse)

(*********************************************************
                       subdomT
 *********************************************************)

lemma subdomTI [intro!]: "(!! t. t :t S ==> t :t T) ==> S <= T"
by (auto simp add: subdomT_def memT_def)

lemma subdomTE [elim!]: "[| S <= T ; (!!t. t :t S ==> t :t T) ==> R |] ==> R"
by (auto simp add: subdomT_def memT_def)

lemma subdomTE_ALL: "[| S <= T ; (ALL t. t :t S --> t :t T) ==> R |] ==> R"
by (auto simp add: subdomT_def memT_def)

lemma subdomT_iff: "((S::'a domT) <= T) = (ALL t. t :t S --> t :t T)"
by (auto)

(*** {<>}t is bottom ***)

lemma BOT_is_bottom_domT[simp]: "{<>}t <= T"
by (simp add: subdomT_iff)

lemma memT_subdomT: "[| t :t S ; S <= T |] ==> t :t T"
by (simp add: subdomT_iff)

(*********************************************************
                         UnT
 *********************************************************)

lemma UnT_commut: "S UnT T = T UnT S"
apply (rule order_antisym)
by (simp_all add: subdomT_iff)

lemma UnT_assoc: "(S UnT T) UnT R = S UnT (T UnT R)"
apply (rule order_antisym)
by (simp_all add: subdomT_iff)

lemma UnT_left_commut: "S UnT (T UnT R) = T UnT (S UnT R)"
apply (rule order_antisym)
by (simp_all add: subdomT_iff)

lemmas UnT_rules = UnT_commut UnT_assoc UnT_left_commut

lemma UnT_nilt_left[simp]: "{<>}t UnT T = T"
apply (rule order_antisym)
by (auto)

lemma UnT_nilt_right[simp]: "T UnT {<>}t = T"
apply (rule order_antisym)
by (auto)

lemma S_UnT_T :
    "S UnT T = {u. u :t S \<or> u :t T}t"
by (simp add: UnionT_def CollectT_def Un_def memT_def)

(*********************************************************
                         IntT
 *********************************************************)

lemma IntT_commut: "S IntT T = T IntT S"
apply (rule order_antisym)
by (simp_all add: subdomT_iff)

lemma IntT_assoc: "(S IntT T) IntT R = S IntT (T IntT R)"
apply (rule order_antisym)
by (simp_all add: subdomT_iff)

lemma IntT_left_commut: "S IntT (T IntT R) = T IntT (S IntT R)"
apply (rule order_antisym)
by (simp_all add: subdomT_iff)

lemmas IntT_rules = IntT_commut IntT_assoc IntT_left_commut

(*********************************************************
                         CollectT
 *********************************************************)

(*** open ***)

lemma CollectT_open[simp]: "{u. u :t T}t = T"
apply (subgoal_tac "{u. u :t T} : domT")
apply (auto simp add: memT_def Abs_domT_inverse)
by (simp add: Rep_domT_inverse)

lemma CollectT_open_memT: "{t. P t} : domT ==> t :t {t. P t}t = P t"
by (simp add: memT_def Abs_domT_inverse)

(*** implies {  }t ***)

lemma set_CollectT_eq: 
  "{t. Pr1 t} = {t. Pr2 t} ==> {t. Pr1 t}t = {t. Pr2 t}t"
by (simp)

lemma CollectT_eq: 
  "[| !! t. Pr1 t = Pr2 t |] ==> {t. Pr1 t}t = {t. Pr2 t}t"
by (simp)

lemma set_CollectT_commute_left :
    "{u. Q u \<or> u :t S \<or> P u}t
     = {u. u :t S \<or> Q u \<or> P u}t"
by (rule set_CollectT_eq, force)


lemma nilt_one_CollectT : "{t. t = <> | t = <a> }t = {<>, <a>}t"
  apply (subst Abs_domT_inject)
  apply (simp add: domT_def HC_T1_def prefix_closed_def, force)
  by (simp only: one_t_set_in, force)


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
