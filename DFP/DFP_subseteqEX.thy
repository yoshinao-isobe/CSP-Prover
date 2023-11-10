           (*-------------------------------------------*
            |                DFP package                |
            |                   June 2005               |
            |               December 2005  (modified)   |
            |                                           |
            |   DFP on CSP-Prover ver.3.0               |
            |              September 2006  (modified)   |
            |                  April 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2021         |
            |                  2022 / 2023  (modified)  |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_subseteqEX
imports CSP_F_Main
begin
(*
datatype Event = left real | right "real * nat"
datatype Name = Empty nat | Full real nat
(*datatype DFName = DF*)

primrec
  Bufferfun :: "Name => (Name, Event) proc"
where
  "Bufferfun  (Empty n)  = left ? r -> $(Full r n)"
 |"Bufferfun  (Full r n) = right (r,n) -> $(Empty (Suc n))"

overloading Set_Bufferfun == 
  "PNfun :: (Name, Event) pnfun"
begin
  definition "PNfun == Bufferfun"
end
*)
(*****************************************************************

  1. safe subsets of [[P]]F, used for deadlock-free verification.

 *****************************************************************)

(*********************************************************
                    safe cut of [[_]]F
        This is used for deadlock-free verification.
 *********************************************************)

definition
  restRefusal :: "'a setF => 'a event set => 'a failure set"
                                     ("(0_/ restRefusal /_)" [52,990] 52)
  where
  restRefusal_def :
    "F restRefusal A == {(s,Y)| s Y. (s,Y) :f F & Y <= A}"

definition    
  subseteqEX   :: "'a failure set => 'a failure set => bool"
                                     ("(0_/ <=EX /_)" [50,50] 50)
  where
  subseteqEX_def :
    "F <=EX E == (F <= E) & (ALL s Y. (s,Y) : E --> (EX Z. (s,Z) : F & Y <= Z))"

(*********************************************************
                subseteqEX &  restRefusal
 *********************************************************)

lemma subseteqEX_reflex[simp]:  "F <=EX F"
apply (simp add: subseteqEX_def)
apply (auto)
done

lemma subseteqEX_Int:
   "F restRefusal A = {(s,Y Int A)|s Y. (s,Y) :f F}"
apply (simp add: restRefusal_def)
apply (auto)
apply (rule memF_F2)
apply (simp)
apply (fast)
done

lemma subseteqEX_restRefusal_iff:
  "(F <=EX E restRefusal A)
   = ((ALL s Y. (s, Y) : F --> (s, Y) :f E & Y <= A) &
      (ALL s Y. (s, Y) :f E --> (EX Z. (s, Z) : F & Y Int A <= Z)))"
apply (simp add: subseteqEX_def)
apply (simp add: restRefusal_def)
apply (rule iffI)

(* --> *)

 apply (rule conjI)

  apply (intro allI impI)
  apply (elim conjE)
  apply (erule subsetE)
  apply (drule_tac x="(s,Y)" in bspec, simp)
  apply (simp)

  apply (intro allI impI)
  apply (elim conjE)
  apply (drule_tac x="s" in spec)
  apply (drule_tac x="Y Int A" in spec)
  apply (drule mp)
   apply (rule conjI)
   apply (rule memF_F2, simp_all)
   apply (fast)

(* <-- *)
  apply (fast)
done

(*********************************************************
        How to prove F <=EX ([[P]]F restRefusal A)
 *********************************************************)

(*--------------------*
 |        DIV         |
 *--------------------*)

lemma subseteqEX_DIV[simp]: "{} <=EX failures (DIV) MF restRefusal A"
apply (simp add: subseteqEX_def)
apply (simp add: restRefusal_def)
apply (simp add: in_failures)
done

(*-----------*
 | csp rules |
 *-----------*)

lemma cspF_subseteqEX_DIV:
  "P =F DIV ==> {} <=EX failures (DIV) MF restRefusal A"
by (simp add: eqF_def)

(*--------------------*
 |     Int_choice     |
 *--------------------*)

(* eq *)

lemma subseteqEX_Int_choice: 
  "[| F1 <=EX failures P1 MF restRefusal A ; 
      F2 <=EX failures P2 MF restRefusal A |]
    ==> F1 Un F2 <=EX failures (P1 |~| P2) MF restRefusal A"
apply (simp add: subseteqEX_restRefusal_iff)
apply (simp add: in_failures)
apply (intro allI impI)
apply (elim conjE)
apply (rule conjI)

 apply (rotate_tac 1)
 apply (drule_tac x="s" in spec)
 apply (drule_tac x="Y" in spec)
 apply (fast)

 apply (rotate_tac 3)
 apply (drule_tac x="s" in spec)
 apply (drule_tac x="Y" in spec)
 apply (fast)
done

(*-----------*
 | csp rules |
 *-----------*)

lemma cspF_subseteqEX_Int_choice: 
  "[| P =F P1 |~| P2 ;
      F = F1 Un F2 ;
      F1 <=EX failures P1 MF restRefusal A ;
      F2 <=EX failures P2 MF restRefusal A |]
   ==> F <=EX failures P  MF restRefusal A"
apply (simp add: eqF_def)
apply (simp add: eqF_decompo)
apply (simp add: subseteqEX_Int_choice)
done

(*------------------------*
 |   Rep_int_choice_nat   |
 *------------------------*)

(* eq *)

lemma subseteqEX_Rep_int_choice_nat: 
  "[| ALL n : N. Ff n <=EX failures(Pf n) MF restRefusal A |]
    ==> Union {(Ff n)|n. n : N} <=EX failures (!nat :N .. Pf) MF restRefusal A"
apply (simp add: subseteqEX_restRefusal_iff)
apply (simp add: in_failures)
apply (rule conjI)

 (* 1 *)
 apply (force)

 (* 2 *)
 apply (intro allI impI)
 apply (elim conjE bexE)
 apply (drule_tac x="n" in bspec, simp)
 apply (elim conjE)
 apply (rotate_tac -1)
 apply (drule_tac x="s" in spec)
 apply (drule_tac x="Y" in spec)
 apply (auto)
done

(*-----------*
 | csp rules |
 *-----------*)

lemma cspF_subseteqEX_Rep_int_choice_nat: 
  "[| P =F !nat :N .. Pf ;
      F = Union {(Ff n)|n. n : N} ;
      ALL n : N. Ff n <=EX failures(Pf n) MF restRefusal A |]
   ==> F <=EX failures (!nat :N .. Pf) MF restRefusal A"
by (simp add: subseteqEX_Rep_int_choice_nat)

(*------------------------*
 |   Rep_int_choice_set   |
 *------------------------*)

(* eq *)

lemma subseteqEX_Rep_int_choice_set: 
  "[| ALL X : Xs. Ff X <=EX failures(Pf X) MF restRefusal A |]
    ==> Union {(Ff X)|X. X : Xs} <=EX failures (!set :Xs .. Pf) MF restRefusal A"
apply (simp add: subseteqEX_restRefusal_iff)
apply (simp add: in_failures)
apply (rule conjI)

 (* 1 *)
 apply (force)

 (* 2 *)
 apply (intro allI impI)
 apply (elim conjE bexE)
 apply (drule_tac x="X" in bspec, simp)
 apply (elim conjE)
 apply (rotate_tac -1)
 apply (drule_tac x="s" in spec)
 apply (drule_tac x="Y" in spec)
 apply (auto)
done

(*-----------*
 | csp rules |
 *-----------*)

lemma cspF_subseteqEX_Rep_int_choice_set: 
  "[| P =F !set :Xs .. Pf ;
      F = Union {(Ff X)|X. X : Xs} ;
      ALL X : Xs. Ff X <=EX failures(Pf X) MF restRefusal A |]
   ==> F <=EX failures (!set :Xs .. Pf) MF restRefusal A"
by (simp add: subseteqEX_Rep_int_choice_set)

(* com *)

lemma cspF_subseteqEX_Rep_int_choice_com: 
  "[| P =F ! :X .. Pf ;
      F = Union {(Ff a)|a. a : X} ;
      ALL a : X. Ff a <=EX failures(Pf a) MF restRefusal A |]
   ==> F <=EX failures (! :X .. Pf) MF restRefusal A"
apply (unfold Rep_int_choice_com_def)
apply (rule cspF_subseteqEX_Rep_int_choice_set[of _ _ _ _ "(%X. Ff(the_elem X))"])
apply (auto)
apply (rule_tac x="Ff (the_elem {aa})" in exI)
apply (simp)
apply (rule_tac x="{aa}" in exI)
apply (simp)
done

(* f *)

lemma cspF_subseteqEX_Rep_int_choice_f: 
  "[| inj f;  P =F !<f> :X .. Pf ;
      F = Union {(Ff a) |a. a : X} ;
      ALL a : X. Ff a <=EX failures(Pf a) MF restRefusal A |]
   ==> F <=EX failures (!<f> :X .. Pf) MF restRefusal A"
apply (unfold Rep_int_choice_f_def)
apply (rule cspF_subseteqEX_Rep_int_choice_com[of _ _ _ _ "(%x. Ff(inv f x))"])
apply (auto)

 apply (rule_tac x="Ff aa" in exI)
 apply (simp)
 apply (rule_tac x="f aa" in exI)
 apply (simp)
done

lemmas cspF_subseteqEX_Rep_int_choice =
       cspF_subseteqEX_Rep_int_choice_nat
       cspF_subseteqEX_Rep_int_choice_set
       cspF_subseteqEX_Rep_int_choice_com
       cspF_subseteqEX_Rep_int_choice_f

lemma cspF_subseteqEX_Rep_int_choice_nat_UNIV: 
  "[| P =F !nat n .. Pf n ;
      F = Union {(Ff a) |a. True} ;
      ALL a. Ff a <=EX failures(Pf a) MF restRefusal A |]
   ==> F <=EX failures (!nat n .. Pf n) MF restRefusal A"
apply (insert cspF_subseteqEX_Rep_int_choice_nat[of P UNIV Pf F Ff A])
by (simp_all)

(*--------------------*
 |   Ext_pre_choice   |
 *--------------------*)

(* eq *)

lemma subseteqEX_Ext_pre_choice: 
  "ALL a : X. Ff a <=EX failures (Pf a) MF restRefusal A
    ==> insert (<>, A - Ev ` X) 
        {(<Ev a> ^^^ s, Y) |a s Y. (s,Y) : Ff a & a : X}
        <=EX failures (? :X -> Pf) MF restRefusal A"
apply (simp add: subseteqEX_restRefusal_iff)
apply (simp add: in_failures)
apply (intro conjI)

 (* 1 *)
 apply (fast)

 (* 2 *)
 apply (intro allI impI)
 apply (rule conjI)
  apply (fast)

  apply (intro impI)
  apply (elim conjE exE)
  apply (drule_tac x="a" in bspec, simp)
  apply (elim conjE)
  apply (rotate_tac -1)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="Y" in spec)
  apply (simp)
done

(*-----------*
 | csp rules |
 *-----------*)

lemma cspF_subseteqEX_Ext_pre_choice: 
  "[| P =F ? :X -> Pf ;
      F = insert (<>, A - Ev ` X) 
          {(<Ev a> ^^^ s, Y) |a s Y. (s,Y) : Ff a & a : X} ;
      ALL a : X. Ff a <=EX failures (Pf a) MF restRefusal A |]
   ==> F <=EX failures P MF restRefusal A"
by (simp add: eqF_def eqF_decompo subseteqEX_Ext_pre_choice)

(*-----------*
 | csp rules |
 *-----------*)

lemma cspF_subseteqEX_eqF:
  "[| P =F Q ;
       FS <=EX failures Q MF restRefusal A |]
   ==> FS <=EX failures P MF restRefusal A"
by (simp add: eqF_def eqF_decompo)

(****************** to add them again ******************)

end

