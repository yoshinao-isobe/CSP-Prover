           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                 August 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2012         |
            |               November 2012  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2013         |
            |                   June 2013  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Set_F
imports CSP.Trace
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

(***********************************************************
                 type def (Failure Part)
 ***********************************************************)

(* types 'a failure = "'a trace * 'a event set"       (* synonym *)   Isabelle 2011 *)
type_synonym 'a failure = "'a trace * 'a event set"       (* synonym *)

definition
  HC_F2    :: "'a failure set => bool"
  where
  HC_F2_def : "HC_F2 F == (ALL s X Y. ((s,X) : F & Y <= X) --> (s,Y) : F)"

definition "setF  = {F::('a failure set). HC_F2(F)}"
typedef 'a setF = "setF :: 'a failure set set"
apply (rule_tac x ="{}" in exI)
apply (simp add: setF_def)
by (simp add: HC_F2_def)

declare Rep_setF         [simp]

(***********************************************************
                   operators on setF
 ***********************************************************)

definition
  memF     :: "'a failure => 'a setF => bool"  ("(_/ :f _)" [50, 51] 50)
  where
  memF_def     : "x :f F     == x : (Rep_setF F)"
  
definition  
  CollectF :: "('a failure => bool) => 'a setF"("CollectF")
  where
  CollectF_def : "CollectF P == Abs_setF (Collect P)"

definition
  UnionF   :: "'a setF set => 'a setF"         ("UnionF _" [90] 90)
  where
  UnionF_def   : "UnionF Fs  == Abs_setF (Union (Rep_setF ` Fs))"

definition  
  InterF   :: "'a setF set => 'a setF"         ("InterF _" [90] 90)
  where
  InterF_def   : "InterF Fs  == Abs_setF (Inter (Rep_setF ` Fs))"
  
definition
  empF     :: "'a setF"                        ("{}f")
  where
  empF_def     : "{}f        == Abs_setF {}"
  
definition  
  UNIVF    :: "'a setF"                        ("UNIVf")
  where
  UNIVF_def    : "UNIVf      == Abs_setF UNIV"

(******** X-symbols ********)
(*
notation (xsymbols) memF ("(_/ \<in>f _)" [50, 51] 50)
notation (xsymbols) UnionF ("\<Union>f _" [90] 90)
notation (xsymbols) InterF ("\<Inter>f _" [90] 90)
*)

(******** syntactic sugar ********)

abbreviation
 nonmemF :: "'a failure => 'a setF => bool"   ("(_/ ~:f _)" [50, 51] 50)
 where "x ~:f F == ~ x :f F"

abbreviation
 UnF :: "'a setF => 'a setF => 'a setF"   ("_ UnF _" [65,66] 65)
 where "F UnF E == UnionF {F,E}"

abbreviation
 IntF :: "'a setF => 'a setF => 'a setF"   ("_ IntF _" [70,71] 70)
 where "F IntF E == InterF {F,E}"

syntax
  "@CollF"    :: "pttrn => bool => 'a setF"        ("(1{_./ _}f)" [1000,10] 1000)
  "@FinsetF"  :: "args => 'a setF"                 ("{(_)}f" [1000] 1000)

translations
  "{x. P}f"    == "CONST Abs_setF {x. P}" (* "CONST" for isabelle2009-2 *)
  "{X}f"       == "CONST Abs_setF {X}"    (* "CONST" for isabelle2009-2 *)

(******** X-symbols ********)
(*
notation (xsymbols) nonmemF  ("(_/ \<notin>f _)" [50, 51] 50)
notation (xsymbols) UnF      ("_ \<union>f _" [65,66] 65)
notation (xsymbols) IntF     ("_ \<inter>f _" [70,71] 70)
*)
(*********************************************************
          The relation (<=) is defined over setF
 *********************************************************)

instantiation setF :: (type) ord 
begin
definition
  subsetF_def:
    "F <= E  ==  (Rep_setF F) <= (Rep_setF E)"
definition
  psubsetF_def:
    "F <  E  ==  (Rep_setF F) <  (Rep_setF E)"

instance
by (intro_classes)
end

(*********************************************************
          The relation (<=) is a partial order
 *********************************************************)

instance setF :: (type) order
apply (intro_classes)
apply (unfold subsetF_def psubsetF_def)
(* apply (simp add: less_fun_def)                (* isabelle 2009-2011 !! *)*)
apply (simp only: order_less_le Rep_setF_inject)
apply (auto simp add: Rep_setF_inject)
done

(***********************************************************
                          lemmas
 ***********************************************************)

(*******************************
             basic
 *******************************)

lemma setF_F2:
  "[| F : setF ; (s,X) : F ; Y <= X |] ==> (s,Y) : F"
apply (simp add: setF_def)
apply (unfold HC_F2_def)
apply (drule_tac x="s" in spec)
apply (drule_tac x="X" in spec)
apply (drule_tac x="Y" in spec)
by (simp)

(*** {} in setF ***)

lemma emptyset_in_setF[simp]: "{} : setF"
by (simp add: setF_def HC_F2_def)

(*******************************
         check in setF
 *******************************)

(*** [] (for STOP) ***)

lemma nilt_in_setF[simp]: "{(<>, X) |X. X <= EvsetTick} : setF"
by (auto simp add: setF_def HC_F2_def)

(*** [Tick] (for SKIP) ***)
lemma nilt_Tick_in_setF[simp]: "{(<>, X) |X. X <= Evset} Un 
                                {(<Tick>, X) |X. X <= EvsetTick} : setF"
apply (simp add: setF_def HC_F2_def)
apply (intro allI impI)
apply (elim conjE disjE)
by (simp_all)

(*** Union ***)

lemma setF_Union_in_setF: "(Union (Rep_setF ` Fs)) : setF"
apply (simp add: setF_def HC_F2_def)
apply (intro allI impI)

apply (erule conjE)
apply (erule bexE)
apply (rename_tac s X Y F)
apply (rule_tac x="F" in bexI)
apply (rule setF_F2)
by (simp_all)

(*** Un ***)

lemma setF_Un_in_setF:
  "(Rep_setF F Un Rep_setF E) : setF"
apply (insert setF_Union_in_setF[of "{F,E}"])
by (simp)

(*** Inter ***)

lemma setF_Inter_in_setF: "(Inter (Rep_setF ` Fs)) : setF"
apply (simp add: setF_def HC_F2_def)
apply (intro allI impI)

apply (rule ballI)
apply (rename_tac s X Y F)
apply (erule conjE)
apply (drule_tac x="F" in bspec, simp)
apply (rule setF_F2)
by (simp_all)

(*** Int ***)

lemma setF_Int_in_setF:
  "(Rep_setF F Int Rep_setF E) : setF"
apply (insert setF_Inter_in_setF[of "{F,E}"])
by (simp)

lemmas in_setF = setF_Union_in_setF setF_Un_in_setF
                 setF_Inter_in_setF setF_Int_in_setF

(*******************************
     setF type --> set type
 *******************************)

(*** UnionF ***)

lemma setF_UnionF_Rep:
  "Rep_setF (UnionF Fs) = Union (Rep_setF ` Fs)"
by (simp add: UnionF_def Abs_setF_inverse in_setF)

(*** UnF ***)

lemma setF_UnF_Rep:
  "Rep_setF (F UnF E) = (Rep_setF F) Un (Rep_setF E)"
by (simp add: setF_UnionF_Rep)

(*** InterF ***)

lemma setF_InterF_Rep:
  "Rep_setF (InterF Fs) = Inter (Rep_setF ` Fs)"
by (simp add: InterF_def Abs_setF_inverse in_setF)

(*** IntF ***)

lemma setF_IntF_Rep:
  "Rep_setF (F IntF E) = (Rep_setF F) Int (Rep_setF E)"
by (simp add: setF_InterF_Rep)

(*********************************************************
                       memF
 *********************************************************)

(* memF_F2 *)

lemma memF_F2:
  "[| (s,X) :f F ; Y <= X |] ==> (s,Y) :f F"
apply (simp add: memF_def)
apply (rule setF_F2)
by (simp_all)

(* UnionF *)

lemma memF_UnionF_only_if:
  "sX :f UnionF Fs ==> EX F:Fs. sX :f F"
by (simp add: memF_def setF_UnionF_Rep)

lemma memF_UnionF_if:
  "[| F:Fs ; sX :f F |] ==> sX :f UnionF Fs"
apply (subgoal_tac "Fs ~= {}")
apply (simp add: memF_def setF_UnionF_Rep)
apply (rule_tac x="F" in bexI)
by (auto)

lemma memF_UnionF[simp]:
  "sX :f UnionF Fs = (EX F:Fs. sX :f F)"
apply (rule iffI)
apply (simp add: memF_UnionF_only_if)
by (auto simp add: memF_UnionF_if)

(* InterF *)

lemma memF_InterF_only_if:
  "sX :f InterF Fs ==> ALL F:Fs. sX :f F"
by (simp add: memF_def setF_InterF_Rep)

lemma memF_InterF_if:
  "ALL F:Fs. sX :f F ==> sX :f InterF Fs"
by (simp add: memF_def setF_InterF_Rep)

lemma memF_InterF[simp]:
  "sX :f InterF Fs = (ALL F:Fs. sX :f F)"
apply (rule iffI)
apply (rule memF_InterF_only_if, simp_all)
by (simp add: memF_InterF_if)

(* empty *)

lemma memF_empF[simp]: "sX ~:f {}f"
apply (simp add: memF_def empF_def)
by (simp add: Abs_setF_inverse)

(* pair *)

lemma memF_pair_iff: "(f :f F) = (EX s X. f = (s,X) & (s,X) :f F)"
apply (rule)
apply (rule_tac x="fst f" in exI)
apply (rule_tac x="snd f" in exI)
by (auto)

lemma memF_pairI: "(EX s X. f = (s,X) & (s,X) :f F) ==> (f :f F)"
by (auto)

lemma memF_pairE_lm: "[| f :f F ; (EX s X. f = (s,X) & (s,X) :f F) --> R |] ==> R"
apply (drule mp)
apply (rule_tac x="fst f" in exI)
apply (rule_tac x="snd f" in exI)
by (auto)

lemma memF_pairE: "[| f :f F ; !! s X. [| f = (s,X) ; (s,X) :f F |] ==> R |] ==> R"
apply (erule memF_pairE_lm)
by (auto)

(*********************************************************
                       subsetF
 *********************************************************)

lemma subsetFI [intro!]: "(!! s X. (s, X) :f E ==> (s, X) :f F) ==> E <= F"
by (auto simp add: subsetF_def memF_def)

lemma subsetFE [elim!]: 
  "[| E <= F ; (!!s X. (s, X) :f E ==> (s, X) :f F) ==> R |] ==> R"
by (auto simp add: subsetF_def memF_def)

lemma subsetFE_ALL: 
  "[| E <= F ; (ALL s X. (s, X) :f E --> (s, X) :f F) ==> R |] ==> R"
by (auto simp add: subsetF_def memF_def)

lemma subsetF_iff: "((E::'a setF) <= F) 
                  = (ALL s X. (s, X) :f E --> (s, X) :f F)"
by (auto)

(*** {}f is bottom ***)

lemma BOT_is_bottom_setF[simp]: "{}f <= F"
by (simp add: subsetF_iff)

lemma memF_subsetF: "[| (s,X) :f E ; E <= F |] ==> (s,X) :f F"
by (simp add: subsetF_iff)

(*********************************************************
                         UnF
 *********************************************************)

lemma UnF_commut: "E UnF F = F UnF E"
apply (rule order_antisym)
by (simp_all add: subsetF_iff)

lemma UnF_assoc: "(E UnF F) UnF R = E UnF (F UnF R)"
apply (rule order_antisym)
by (simp_all add: subsetF_iff)

lemma UnF_left_commut: "E UnF (F UnF R) = F UnF (E UnF R)"
apply (rule order_antisym)
by (simp_all add: subsetF_iff)

lemmas UnF_rules = UnF_commut UnF_assoc UnF_left_commut

(*********************************************************
                         IntF
 *********************************************************)

lemma IntF_commut: "E IntF F = F IntF E"
apply (rule order_antisym)
by (simp_all add: subsetF_iff)

lemma IntF_assoc: "(E IntF F) IntF R = E IntF (F IntF R)"
apply (rule order_antisym)
by (simp_all add: subsetF_iff)

lemma IntF_left_commut: "E IntF (F IntF R) = F IntF (E IntF R)"
apply (rule order_antisym)
by (simp_all add: subsetF_iff)

lemmas IntF_rules = IntF_commut IntF_assoc IntF_left_commut

(*********************************************************
                         CollectT
 *********************************************************)

(*** open ***)

lemma CollectF_open[simp]: "{u. u :f F}f = F"
apply (subgoal_tac "{f. f :f F} : setF")
apply (auto simp add: memF_def Abs_setF_inverse)
by (simp add: Rep_setF_inverse)

lemma CollectF_open_memF: "{f. P f} : setF ==> f :f {f. P f}f = P f"
by (simp add: memF_def Abs_setF_inverse)

(*** implies {  }f ***)

lemma set_CollectF_eq: 
  "{f. Pr1 f} = {f. Pr2 f} ==>{f. Pr1 f}f = {f. Pr2 f}f"
by (simp)

lemma CollectF_eq: 
  "[| !! f. Pr1 f = Pr2 f |] ==>{f. Pr1 f}f = {f. Pr2 f}f"
by (simp)

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
