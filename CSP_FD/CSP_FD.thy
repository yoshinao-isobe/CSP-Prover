theory FD
imports CSP_F
begin

(*
lemma nilt_in_setF : "{(<>, X)|X. True} : setF"
by (auto simp add: setF_def HC_F2_def)
*)


(*
lemma proc_T2:
    "(s, X) :f failures(P) M ==> s :t traces(P) (fstF o M)"

lemma pairF_domF_F3:
  "[| (s, X) :f sndF SF ; noTick s ;
      (ALL a. a : Y --> s ^^^ <a> ~:t fstF SF) |]
   ==> (s, X Un Y) :f sndF SF"
apply (simp add: sndF_def fstF_def)
apply (rule domF_F3[of "fst (Rep_domF SF)" "snd (Rep_domF SF)"])
by (simp_all)
*)


(*** F5 (D1 + D2 + D3) ***)

(*definition
  HC_T0    :: "'a trace set => bool"
  where
  HC_T0_def : "HC_T0 T == (T ~= {})"

definition "EvStar  = {T::('a trace set). HC_T0(T)}"

Roscoe assumes D is a subset of EvStarTick, but EvStar does not allows {}.
*)

definition "EvStar  = {T::('a trace set). True}"

abbreviation EvStarSugar ("\<Sigma>*") where "\<Sigma>* == EvStar"

lemma emptyset_notin_EvStar [simp]: "{} \<in> \<Sigma>*"
  by (simp add: EvStar_def)
(*  by (simp add: HC_T0_def) *)

typedef 'a domT0 = "EvStar :: 'a trace set set"
  apply (rule_tac x ="{<>}" in exI)
  by (simp add: EvStar_def)
(*  by (simp add: HC_T0_def) *)

(*declare [[coercion "Rep_domT0 :: 'a domT0 \<Rightarrow> 'a trace set"]]*)

lemma T1_T0 [simp]:
    "domT \<le> EvStar"
  by (simp add: EvStar_def)
(*  apply (simp add: domT_def)
  by (auto simp add: HC_T0_def HC_T1_def) *)

(*lemma HC_T1_HC_T0 [simp]:
   "HC_T1 T \<Longrightarrow> HC_T0 T"
  by (simp add: HC_T0_def HC_T1_def) *)

definition
  empD     :: "'a domT0" ("{}d")
  where
  empD_def     : "{}d == Abs_domT0 {}"

definition
  memD     :: "'a trace => 'a domT0 => bool"  ("(_/ :d _)" [50, 51] 50)
  where
  memD_def     : "x :d T     == x : (Rep_domT0 T)"

syntax
  "@CollD"    :: "pttrn => bool => 'a domT0"     ("(1{_./ _}d)" [1000,10] 1000)
  "@FindomD"  :: "args => 'a domT0"              ("{(_)}d" [1000] 1000)

translations
  "{x. P}d"    == "CONST Abs_domT0 {x. P}"
  "{X}d"       == "CONST Abs_domT0 {X}"



type_synonym 'a domTsetFdomT0 = "'a domTsetF * 'a domT0" (* F * D *)


definition
  HC_D1    :: "'a domTsetFdomT0 => bool"
  where
  HC_D1_def : 
    "HC_D1 FD == ALL s t. s :d (snd FD) & noTick t --> s ^^^ t :d (snd FD)"
(* Int ( \<Union> \<Sigma>* ) *)
(* The intersection of D with EvStar is unnecessary because it is the type of D *)

definition  
  HC_D2    :: "'a domTsetFdomT0 => bool"
  where
  HC_D2_def : 
    "HC_D2 FD == ALL s. s :d (snd FD) --> (\<exists>X. (s, X) :f (snd (fst FD)))"

definition  
  HC_D3    :: "'a domTsetFdomT0 => bool"
  where
  HC_D3_def : 
    "HC_D3 FD == ALL s. s ^^^ <Tick> :d (snd FD) --> s :d (snd FD)"

definition
  HC_F5    :: "'a domTsetFdomT0 => bool"
  where
  HC_F5_def : 
    "HC_F5 TF == HC_D1(TF) & HC_D2(TF) & HC_D3(TF)"
  
(*definition  
  HC_D1_D2_D3 :: "'a domTsetFdomT0 => bool"
  where
  HC_D1_D2_D3_def : 
    "HC_D1_D2_D3 TF == ...*)

(*lemma HC_D1_D2_D3_iff : "HC_D1_D2_D3 FD = (HC_D1 FD & HC_D2 FD & HC_D3 FD )"
apply (simp add: HC_D1_def HC_D2_def HC_D3_def)
by (auto)*)

(**************************************************
       Type domFD (Failures-Divergences model)
 **************************************************)


definition "domFD  = {FD::('a domTsetFdomT0). HC_T2 (fst FD) & HC_T3 (fst FD) &
                                              (HC_F3 (fst FD) & HC_F4 (fst FD)) &
                                              (HC_D1 (FD) & HC_D2 (FD) & HC_D3 (FD))}"
typedef 'a domFD = "domFD :: 'a domTsetFdomT0 set"
  apply (rule_tac x ="( ({<>}t , {}f), {}d )" in exI)
  apply (simp add: domFD_def)
  apply (simp add: BOT_T2_T3_F3_F4)
  apply (subst conj_assoc[THEN sym])
  apply (rule)
  apply (simp add: BOT_T2_T3_F3_F4 HC_T3_F4_iff[THEN sym])
  apply (simp add: HC_D1_def HC_D2_def HC_D3_def empD_def memD_def)
  by (simp add: Abs_domT0_inverse)


declare Rep_domFD [simp]

lemma domFD_iff: "domFD = {FD. HC_T2 (fst FD) & HC_F3 (fst FD) & HC_T3_F4 (fst FD) &
                              (HC_D1 (FD) & HC_D2 (FD) & HC_D3 (FD)) }"
by (auto simp add: domFD_def HC_T3_F4_iff)



lemma domTsetFdomT0_F3_D2:
    "[| FD : domFD ; (s, X) :f snd (fst FD) ; noTick s ;
                    (s, Y) ~:f (snd (fst FD)) ; ~ Y <= X |]
     ==> (s, X Un (Y-X)) :f snd (fst FD)"
  apply (simp add: domFD_def, elim conjE)
  apply (simp add: HC_D2_def)

lemma domF_F3:
  "[| (T,F) : domF ; (s, X) :f F ; noTick s ;
      (ALL a. a : Y --> s ^^^ <a> ~:t T) |]
   ==> (s, X Un Y) :f F"
by (simp add: domF_def HC_F3_def)

lemma pairF_domF_F5:
  "[| (s, X) :f sndF SF ; noTick s ;
      (ALL a. a : Y --> s ^^^ <a> ~:t fstF SF) |]
   ==> (s, X Un Y) :f sndF SF"
apply (simp add: sndF_def fstF_def)
apply (rule domF_F3[of "fst (Rep_domF SF)" "snd (Rep_domF SF)"])
by (simp_all)

lemma a: "[||] [ (A(i),P(i)) . i <- I ] =F SKIP"


lemma proc_T2_non_T3:
    "[| (s,X) :f failures(P) M ; (s,Y) ~:f failures(P) M |] ==>
    ALL z : (Y-X) . s ^^^ <z> :t traces(P) (fstF o M)"
  (* ; Y \<noteq> {}
  apply (insert ex_in_conv[of Y], simp, elim exE)
  apply (rule_tac x=x in bexI, simp_all)*)
  apply (frule proc_T2)
  apply (rule)
  apply (rule proc_T2[of _ "Y - X"])

  apply (frule proc_F3)


  apply (erule contrapos_np)
  apply (rule classical)
  by (simp add: memF_F2 pairF_domF_F3)

end