           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                 August 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2013         |
            |                   June 2013  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Domain_F
imports CSP_T.Domain_T Set_F
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
                 type def (Stable Failure)
 ***********************************************************)

(* types 'a domTsetF = "'a domT * 'a setF"       (* synonym *)  2011 *)
type_synonym 'a domTsetF = "'a domT * 'a setF" 

definition
  HC_T2    :: "'a domTsetF => bool"
  where
  HC_T2_def : 
    "HC_T2 TF == ALL s X. (s, X) :f (snd TF)
                --> s :t (fst TF)"
  
definition  
  HC_T3    :: "'a domTsetF => bool"
  where
  HC_T3_def : 
    "HC_T3 TF == ALL s. s ^^^ <Tick> :t (fst TF) & noTick s
                --> (ALL X. (s ^^^ <Tick>, X) :f (snd TF))"
  
definition  
  HC_F3    :: "'a domTsetF => bool"
  where
  HC_F3_def : 
    "HC_F3 TF == ALL s X Y. (s, X) :f (snd TF) & noTick s &
                          (ALL a. a : Y --> s ^^^ <a> ~:t fst TF)
                --> (s, X Un Y) :f (snd TF)"
  
definition  
  HC_F4    :: "'a domTsetF => bool"
  where
  HC_F4_def : 
    "HC_F4 TF == ALL s. s ^^^ <Tick> :t (fst TF) & noTick s
                --> (s, Evset) :f (snd TF)"
  
definition  
  HC_T3_F4 :: "'a domTsetF => bool"
  where
  HC_T3_F4_def : 
    "HC_T3_F4 TF == ALL s. s ^^^ <Tick> :t (fst TF) & noTick s
                    --> ((s, Evset) :f (snd TF) &
                         (ALL X. (s ^^^ <Tick>, X) :f (snd TF)))"

lemma HC_T3_F4_iff : "HC_T3_F4 TF = (HC_T3 TF & HC_F4 TF)"
apply (simp add: HC_T3_F4_def HC_T3_def HC_F4_def)
by (auto)

(*** BOT in domF ***)

lemma BOT_T2_T3_F3_F4: "HC_T2({<>}t , {}f) & HC_F3({<>}t , {}f) & 
                        HC_T3_F4({<>}t , {}f)"
by (auto simp add: HC_T2_def HC_F3_def HC_T3_F4_def)

(**************************************************
           Type domF (Stable-Failures model)
 **************************************************)

definition "domF  = {SF::('a domTsetF). HC_T2(SF) & HC_T3(SF) & HC_F3(SF) & HC_F4(SF)}"
typedef 'a domF = "domF :: 'a domTsetF set"
apply (rule_tac x ="({<>}t , {}f)" in exI)
apply (simp add: domF_def)
by (simp add: BOT_T2_T3_F3_F4 HC_T3_F4_iff[THEN sym])

declare Rep_domF         [simp]

lemma domF_iff: "domF = {SF. HC_T2 SF & HC_F3 SF & HC_T3_F4 SF}"
by (auto simp add: domF_def HC_T3_F4_iff)

(*********************************************************
          The relation (<=) is defined over domF
 *********************************************************)

instantiation domF :: (type) ord 
begin
definition
  subdomF_def:
    "SF <= SE  ==  (Rep_domF SF) <= (Rep_domF SE)"
definition
  psubdomF_def:
    "SF <  SE  ==  (Rep_domF SF) <  (Rep_domF SE)"

instance
by (intro_classes)
end

(*********************************************************
          The relation (<=) is a partial order
 *********************************************************)

instance domF :: (type) order
apply (intro_classes)
apply (unfold subdomF_def psubdomF_def)
apply (auto)
apply (simp add: Rep_domF_inject)
done

(***********************************************************
                          lemmas
 ***********************************************************)

(*******************************
              basic
 *******************************)

(*** T2 ***)

lemma domTsetF_T2:
    "[| TF : domF ; (s, X) :f snd TF |] ==> s :t fst TF"
by (auto simp add: domF_def HC_T2_def)

lemma domF_T2:
    "[| (T,F) : domF ; (s, X) :f F |] ==> s :t T"
by (auto simp add: domF_def HC_T2_def)

(*** T3 ***)

lemma domTsetF_T3:
  "[| TF : domF ; s ^^^ <Tick> :t fst TF ; noTick s |]
   ==> (s ^^^ <Tick>, X) :f snd TF"
by (simp add: domF_def HC_T3_def)

lemma domF_T3:
  "[| (T,F) : domF ; s ^^^ <Tick> :t T ; noTick s |]
   ==> (s ^^^ <Tick>, X) :f F"
by (simp add: domF_def HC_T3_def)

(*** F3 ***)

lemma domTsetF_F3:
  "[| TF : domF ; (s, X) :f snd TF ; noTick s ;
      (ALL a. a : Y --> s ^^^ <a> ~:t fst TF) |]
   ==> (s, X Un Y) :f snd TF"
by (simp add: domF_def HC_F3_def)

lemma domF_F3:
  "[| (T,F) : domF ; (s, X) :f F ; noTick s ;
      (ALL a. a : Y --> s ^^^ <a> ~:t T) |]
   ==> (s, X Un Y) :f F"
by (simp add: domF_def HC_F3_def)

(*** F4 ***)

lemma domTsetF_F4:
  "[| TF : domF ; s ^^^ <Tick> :t fst TF ; noTick s |]
   ==> (s, Evset) :f snd TF"
by (simp add: domF_def HC_F4_def)

lemma domF_F4:
  "[| (T,F) : domF ; s ^^^ <Tick> :t T ; noTick s |]
   ==> (s, Evset) :f F"
by (simp add: domF_def HC_F4_def)

(*** T3_F4 ***)

lemma domTsetF_T3_F4:
  "[| TF : domF ; s ^^^ <Tick> :t fst TF ; noTick s |]
   ==> (s, Evset) :f snd TF & (ALL X. (s ^^^ <Tick>, X) :f snd TF)"
by (simp add: domF_iff HC_T3_F4_def)

lemma domF_T3_F4:
  "[| (T,F) : domF ; s ^^^ <Tick> :t T ; noTick s |]
   ==> (s, Evset) :f F & (ALL X. (s ^^^ <Tick>, X) :f F)"
by (simp add: domF_iff HC_T3_F4_def)

(*** F2_F4 ***)

lemma domTsetF_F2_F4:
  "[| TF : domF ; s ^^^ <Tick> :t fst TF ; noTick s ; X <= Evset |]
   ==> (s, X) :f snd TF"
apply (simp add: domF_def HC_F4_def)
by (auto intro: memF_F2)

lemma domF_F2_F4:
  "[| (T,F) : domF ; s ^^^ <Tick> :t T ; noTick s ; X <= Evset |]
   ==> (s, X) :f F"
apply (insert domTsetF_F2_F4[of "(T,F)" s X])
by (simp)

(*******************************
         check in domF
 *******************************)

(*** ({<>}t, {}f) ***)

lemma BOT_in_domF[simp]: "({<>}t, {}f) : domF"
by (simp add: domF_iff BOT_T2_T3_F3_F4)

(*******************************
       BOT is the bottom
 *******************************)

lemma BOT_is_bottom_domF[simp]: "({<>}t , {}f) <= SF"
by (simp add: order_pair_def)

(***********************************************************
                   operators on domF
 ***********************************************************)

definition
  pairF :: "'a domT => 'a setF => 'a domF"  ("(0_ ,,/ _)" [51,52] 0)
  where
  pairF_def : "(T ,, F) == Abs_domF (T, F)"
  
definition
  fstF  :: "'a domF => 'a domT"
  where
  fstF_def  : "fstF     == fst o Rep_domF"
  
definition  
  sndF  :: "'a domF => 'a setF"
  where
  sndF_def  : "sndF     == snd o Rep_domF"

(***********************************************************
                     pairSF lemmas
 ***********************************************************)

lemma fold_fstF: "fst (Rep_domF SF) = fstF SF"
by (simp add: fstF_def comp_def)

lemma fold_sndF: "snd (Rep_domF SF) = sndF SF"
by (simp add: sndF_def comp_def)

lemma pairF_fstF: "(S,F) : domF ==> fstF (S,,F) = S"
apply (simp add: pairF_def fstF_def)
by (simp add: Abs_domF_inverse)

lemma pairF_sndF: "(S,F) : domF ==> sndF (S,,F) = F"
apply (simp add: pairF_def sndF_def)
by (simp add: Abs_domF_inverse)

lemma eqF_decompo: 
  "(SF = SE) = (fstF SF = fstF SE & sndF SF = sndF SE)"
apply (simp add: Rep_domF_inject[THEN sym])
apply (simp add: pair_eq_decompo)
apply (simp add: fstF_def sndF_def)
done

lemmas pairF = pairF_fstF pairF_sndF eqF_decompo

lemma mono_fstF: "mono fstF"
apply (simp add: mono_def)
apply (simp add: fstF_def)
apply (simp add: subdomF_def)
apply (simp add: order_pair_def)
done

lemma mono_sndF: "mono sndF"
apply (simp add: mono_def)
apply (simp add: sndF_def)
apply (simp add: subdomF_def)
apply (simp add: order_pair_def)
done

(*********************************************************
           Healthiness conditions for pairF
 *********************************************************)

lemma pairF_domF_T2:
    "(s, X) :f sndF SF ==> s :t fstF SF"
apply (simp add: sndF_def fstF_def)
apply (rule domF_T2[of _ "snd (Rep_domF SF)"])
by (simp_all)

lemma pairF_domF_T3:
  "[| s ^^^ <Tick> :t fstF SF ; noTick s |]
   ==> (s ^^^ <Tick>, X) :f sndF SF"
apply (simp add: sndF_def fstF_def)
apply (rule domF_T3[of "fst (Rep_domF SF)" "snd (Rep_domF SF)"])
by (simp_all)

lemma pairF_domF_T3_Tick:
  "<Tick> :t fstF SF ==> (<Tick>, X) :f sndF SF"
apply (insert pairF_domF_T3[of "<>" SF X])
by (simp)

lemma pairF_domF_F4:
  "[| s ^^^ <Tick> :t fstF SF ; noTick s |]
   ==> (s, Evset) :f sndF SF"
apply (simp add: sndF_def fstF_def)
apply (rule domF_F4[of "fst (Rep_domF SF)" "snd (Rep_domF SF)"])
by (simp_all)

lemma pairF_domF_F3:
  "[| (s, X) :f sndF SF ; noTick s ;
      (ALL a. a : Y --> s ^^^ <a> ~:t fstF SF) |]
   ==> (s, X Un Y) :f sndF SF"
apply (simp add: sndF_def fstF_def)
apply (rule domF_F3[of "fst (Rep_domF SF)" "snd (Rep_domF SF)"])
by (simp_all)

lemma pairF_domF_F3I:
  "[| (s, X) :f sndF SF ; noTick s ;
      (ALL a. a : Y --> s ^^^ <a> ~:t fstF SF) ;
      Z = X Un Y |]
   ==> (s, Z) :f sndF SF"
by (simp add: pairF_domF_F3)

(*** F2_F4 ***)

lemma pairF_domF_F2_F4:
  "[| s ^^^ <Tick> :t fstF SF ; noTick s ; X <= Evset|]
   ==> (s, X) :f sndF SF"
apply (rule memF_F2[of _ "Evset"])
apply (rule pairF_domF_F4)
by (simp_all)

(*** T2_T3 ***)

lemma pairF_domF_T2_T3:
  "[| (s ^^^ <Tick>, X) :f sndF SF ; noTick s |] 
  ==> (s ^^^ <Tick>, Y) :f sndF SF"
apply (rule pairF_domF_T3)
apply (rule pairF_domF_T2)
by (simp_all)

(*********************************************************
                     fstF and sndF
 *********************************************************)

lemma fstF_sndF_in_domF[simp]: "(fstF SF , sndF SF) : domF"
apply (simp add: domF_iff)
apply (simp add: HC_T2_def HC_F3_def HC_T3_F4_def)
apply (intro conjI)
apply (intro allI impI)
apply (elim exE)
apply (simp add: pairF_domF_T2)
apply (intro allI impI)
apply (elim conjE)
apply (simp add: pairF_domF_F3)
apply (intro allI impI)
apply (elim conjE)
apply (simp add: pairF_domF_T3 pairF_domF_F4)
done

lemma fstF_sndF_domF[simp]: "(fstF SF ,, sndF SF) = SF"
by (simp add: pairF)

(*********************************************************
                      subdomF
 *********************************************************)

lemma subdomF_decompo: 
  "(SF <= SE) = (fstF SF <= fstF SE & sndF SF <= sndF SE)"
apply (simp add: subdomF_def)
apply (simp add: order_pair_def)
apply (simp add: fstF_def sndF_def)
done

(*********************************************************
                define max F from T
 *********************************************************)

definition
 maxFof :: "'a domT => 'a setF"
 where
 maxFof_def: "maxFof T == {f. EX s. (EX X. f = (s, X)) & s :t T}f"

(* in setF *)

lemma maxFof_setF: "{f. EX s. (EX X. f = (s, X)) & s :t T} : setF"
by (simp add: setF_def HC_F2_def)

(* in maxFof *)

lemma in_maxFof:
  "(f :f maxFof T) = (EX s. (EX X. f = (s, X)) & s :t T)"
apply (simp add: maxFof_def)
apply (simp add: memF_def)
apply (simp add: maxFof_setF Abs_setF_inverse)
done

(* in domF *)

lemma maxFof_domF: "(T, maxFof T) : domF"
apply (simp (no_asm) add: domF_iff)
apply (simp add: HC_T2_def HC_F3_def HC_T3_F4_def in_maxFof)
apply (intro allI impI)
apply (elim conjE)
apply (rule memT_prefix_closed)
apply (simp)
apply (simp)
done

(* max *)

lemma maxFof_max: "s :t T ==> (s,X) :f maxFof T"
by (simp add: in_maxFof)

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
