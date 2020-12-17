           (*-------------------------------------------*
            |                   Test                    |
            |                                           |
            |        CSP-Prover on Isabelle2004         |
            |               August 2004                 |
            |             December 2004 (modified)      |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Test_infinite
imports CSP_F_Main
begin

(*****************************************************************

         1. simple example for fixed point inductuction theorem
         2. Parallel, Hiding, Internal choice
         3. Refinement
         4. 

 *****************************************************************)

(*********************************************************
                         event
 *********************************************************)

datatype Event = Num nat | Read nat
datatype SpcName = SPC nat
datatype ImpName = UI | VAR nat

(*********************************************************
            specification SPC and system IMP
 *********************************************************)

definition
  GTs :: "nat => nat set"
  where
  GTs_def : "GTs n == {m. n < m}"

(*** Spc ***)

primrec
  Spcfun :: "SpcName => (SpcName, Event) proc"
where
  "Spcfun   (SPC n) = Num n -> (!nat m:(GTs n) .. $(SPC m))"

overloading Set_Spcfun == 
  "PNfun :: (SpcName, Event) pnfun"
begin
(*  definition "PNfun (pn::SpcName) == Spcfun pn" *)
  definition "PNfun == Spcfun"
end

declare Set_Spcfun_def [simp]

(* Isabelle 2013
defs (overloaded)
Set_Spcfun_def [simp]: "PNfun == Spcfun"
*)

definition
  Spc :: "(SpcName, Event) proc"
  where
  Spc_def: "Spc == $(SPC 0)"

(*** Imp ***)

primrec
  Impfun :: "ImpName => (ImpName, Event) proc"
where
  "Impfun      (UI) = Read ? m -> Num m -> $UI"
 |"Impfun   (VAR n) = Read ! n -> $(VAR (Suc n))"
 
overloading Set_Impfun == 
  "PNfun :: (ImpName, Event) pnfun"
begin
(*  definition "PNfun (pn::ImpName) == Impfun pn" *)
  definition "PNfun == Impfun"
end
  
declare Set_Impfun_def [simp]

lemma "(PNfun::(ImpName, Event) pnfun) = Impfun"
by (simp)

(*
defs (overloaded)
Set_Impfun_def [simp]: "PNfun == Impfun"
*)

definition
  Imp :: "(ImpName, Event) proc"
  where
  Imp_def: "Imp == ($UI |[range Read]| $(VAR 0)) -- (range Read)"

(*********************************************************
            relation between SPC and IMP
 *********************************************************)

primrec
  Spc_to_Imp :: "SpcName => (ImpName, Event) proc"
where
  "Spc_to_Imp (SPC n) = ($UI |[range Read]| $(VAR n)) -- (range Read)"

(*********************************************************
                     small lemmas
 *********************************************************)

declare Int_commute [simp]

lemma set1[simp]: "range Read Int {(Read n)} = {(Read n)}"
by (auto)

lemma set2[simp]: "{(Read (Suc n))} Int (range Read Int {(Num n)}) Un
                    ({(Num n)} - range Read) = {(Num n)}"
by (auto)

lemma set3[simp]: "Num n ~: range Read"
by (simp add: image_def)

(*********************************************************
               guardedfun (rutine work)
 *********************************************************)

(*** To automatically unfold syntactic sugar ***)
declare csp_prefix_ss_def[simp]

lemma guardedfun_Spc_Imp[simp]:
      "guardedfun Spcfun"
      "guardedfun Impfun"
by (simp add: guardedfun_def, rule allI, induct_tac p, simp_all)+

declare inj_on_def[simp]

(*********************************************************
                   ? SPC <=F IMP ?
 *********************************************************)
(* Isabelle 2013
defs FPmode_def [simp]: "FPmode == CMSmode"
*)

overloading FPmode == 
  "FPmode :: fpmode"
begin
  definition "FPmode == CMSmode"
end

declare FPmode_def [simp]


(* it declares to use CMS approach.

   If you want to verify them by CPO approach, 
   use the following mode:

defs FPmode_def [simp]: "FPmode == CPOmode"

   In this example, both modes are available,
   because Spcfun and Impfun are guarded.       *)

lemma "Spc <=F Imp"
apply (simp add: Spc_def Imp_def)

  (***** by fixed point induction *****)
apply (rule cspF_fp_induct_left[of _ "Spc_to_Imp"])

  (***** check guarded and no hiding operators *****)

apply (simp_all)
apply (simp)

  (***** by step laws (for transforming it to a hnf) *****)

apply (induct_tac p)
apply (cspF_unwind)
apply (cspF_hsf)+
apply (cspF_unwind)
apply (cspF_hsf)+
apply (auto)
apply (cspF_simp)+

  (***** instantiate a non-deterministic choice *****)

apply (rule cspF_Rep_int_choice_left)
apply (rule_tac  x="(Suc xa)" in exI)
apply (simp add: GTs_def)

apply (cspF_auto)+
done

end
