           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                January 2006               |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory FNF_F_sf_int
imports FNF_F_sf_def
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*  The following simplification rules are deleted in this theory file *)
(*       P (if Q then x else y) = ((Q --> P x) & (~ Q --> P y))        *)
(* Isabelle 2017: split_if --> if_split *)

declare if_split  [split del]

(*****************************************************************

         1. full sequentialization for Rep_int_choice_nat
         2. full sequentialization for Rep_int_choice_set
         3. full sequentialization for Int_choice
         3. 

 *****************************************************************)

(*============================================================*
 |                                                            |
 |                    Rep_int_choice_nat                      |
 |                                                            |
 *============================================================*)

definition
  fsfF_Rep_int_choice ::
  "'a sets_nats => ('a aset_anat => ('p,'a) proc) => ('p,'a) proc"
  where
  fsfF_Rep_int_choice_def :
    "fsfF_Rep_int_choice C SPf == 
     if (sumset C = {}) then SDIV else !! :C .. SPf"

syntax
  "_fsfF_Rep_int_choice" :: 
      "'a sets_nats => ('a aset_anat => ('p,'a) proc) => ('p,'a) proc"
                                     ("(1!! :_ ..seq /_)" [900,68] 68) 
  "@fsfF_Rep_int_choice":: 
      "pttrn => 'a sets_nats => ('p,'a) proc => ('p,'a) proc"  
                               ("(1!! _:_ ..seq /_)" [900,900,68] 68)

translations
  "!! :C ..seq SPf"  == "CONST fsfF_Rep_int_choice C SPf"
  "!! c:C ..seq SP"  == "!! :C ..seq (%c. SP)"

(*------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------*)

lemma fsfF_Rep_int_choice_in:
  "ALL c: sumset C. SPf c : fsfF_proc ==> !! :C ..seq SPf : fsfF_proc"
apply (simp add: fsfF_Rep_int_choice_def)

(* Isabelle 2017 *)
 apply (simp split: if_split)
 apply (intro impI)

 apply (rule fsfF_procI)
 apply (simp)
done

(*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*)

lemma cspF_fsfF_Rep_int_choice_eqF:
  "!! :C .. SPf =F !! :C ..seq SPf"
apply (simp add: fsfF_Rep_int_choice_def)
apply (case_tac "sumset C={}")
apply (simp)
apply (rule cspF_rw_left)
apply (rule cspF_Rep_int_choice_DIV)
apply (simp)
apply (rule cspF_SDIV_eqF)

      (* N~={} *)
apply (simp)
done

(* =F also can be semi-automatically proven by using tactics. *)
(*
lemma "!! :C .. SPf =F !! :C ..seq SPf"
apply (simp add: fsfF_Rep_int_choice_def)
  apply (case_tac "sumset C={}")
  apply (cspF_hsf)
apply (rule cspF_SDIV_eqF)
done
*)

lemmas cspF_fsfF_Rep_int_choice_eqF_sym =
       cspF_fsfF_Rep_int_choice_eqF[THEN cspF_sym]

(*============================================================*
 |                                                            |
 |                       for convenience                      |
 |                                                            |
 *============================================================*)

definition
  fsfF_Rep_int_choice_set :: 
    "'a set set => ('a set => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1!set :_ ..seq /_)" [900,68] 68)
  where
  fsfF_Rep_int_choice_set_def:
        "!set :Xs ..seq Pf == !! c:(type1 Xs) ..seq (Pf ((inv type1) c))"
        
definition
  fsfF_Rep_int_choice_nat ::
    "nat set => (nat => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1!nat :_ ..seq /_)" [900,68] 68)
  where
  fsfF_Rep_int_choice_nat_def:
        "!nat :N ..seq Pf == !! c:(type2 N) ..seq (Pf ((inv type2) c))"

syntax
  "@fsfF_Rep_int_choice_set" :: 
       "pttrn => ('a set) set => ('a set => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1!set _:_ ..seq /_)" [900,900,68] 68)
  "@fsfF_Rep_int_choice_nat" :: 
       "pttrn => nat set => (nat => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1!nat _:_ ..seq /_)" [900,900,68] 68)

translations
    "!set X:Xs ..seq P" == "!set :Xs ..seq (%X. P)"
    "!nat n:N ..seq P"  == "!nat :N ..seq (%n. P)"

(* com *)

definition
  fsfF_Rep_int_choice_com :: "'a set => ('a => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1! :_ ..seq /_)" [900,68] 68)
  where
  fsfF_Rep_int_choice_com_def:
     "! :A ..seq Pf == !set X:{{a} |a. a : A} ..seq Pf (the_elem(X))"

syntax
  "@fsfF_Rep_int_choice_com" :: 
      "pttrn => 'a set => ('a => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1! _:_ ..seq /_)" [900,900,68] 68)
translations
    "! x:X ..seq P"    == "! :X ..seq (%x. P)"

(* f *)

definition
  fsfF_Rep_int_choice_f :: "('b => 'a)
          => 'b set => ('b => ('p,'a) proc) => ('p,'a) proc"
                                        ("(1!<_> :_ ..seq /_)" [0,900,68] 68)
  where
  fsfF_Rep_int_choice_f_def : 
        "!<f> :X ..seq Pf == ! :(f ` X) ..seq (%x. (Pf ((inv f) x)))"

syntax
  "@fsfF_Rep_int_choice_f":: 
  "('b => 'a) => pttrn => 'b set => ('p,'a) proc => ('p,'a) proc"
                               ("(1!<_> _:_ ..seq /_)" [0,900,900,68] 68)
translations
  "!<f> x:X ..seq P"   == "!<f> :X ..seq (%x. P)"

(*============================================================*
 |                                                            |
 |                 convenient expressions                     |
 |                                                            |
 *============================================================*)

(*------------------------------------*
 |                 in                 |
 *------------------------------------*)

lemma fsfF_Rep_int_choice_nat_in:
  "ALL n:N. SPf n : fsfF_proc ==>
       !nat :N ..seq SPf : fsfF_proc"
apply (simp add: fsfF_Rep_int_choice_nat_def)
apply (rule fsfF_Rep_int_choice_in)
apply (auto)
done

lemma fsfF_Rep_int_choice_set_in:
  "ALL X:Xs. SPf X : fsfF_proc ==>
       !set :Xs ..seq SPf : fsfF_proc"
apply (simp add: fsfF_Rep_int_choice_set_def)
apply (rule fsfF_Rep_int_choice_in)
apply (auto)
done

lemma fsfF_Rep_int_choice_com_in:
  "ALL x:X. SPf x : fsfF_proc ==>
       ! :X ..seq SPf : fsfF_proc"
apply (simp add: fsfF_Rep_int_choice_com_def)
apply (rule fsfF_Rep_int_choice_set_in)
apply (auto)
done

lemma fsfF_Rep_int_choice_f_in:
  "[| inj f ; ALL x:X. SPf x : fsfF_proc |] ==>
    !<f> :X ..seq SPf : fsfF_proc"
apply (insert fsfF_Rep_int_choice_com_in[of "(f ` X)" "(%x. SPf (inv f x))"])
apply (simp add: fsfF_Rep_int_choice_f_def)
done

(*------------------------------------*
 |                 eqF                |
 *------------------------------------*)

lemma cspF_fsfF_Rep_int_choice_nat_eqF:
  "!nat :N .. SPf =F !nat :N ..seq SPf"
apply (simp add: fsfF_Rep_int_choice_nat_def)
apply (simp add: Rep_int_choice_nat_def)
apply (simp add: cspF_fsfF_Rep_int_choice_eqF)
done

lemma cspF_fsfF_Rep_int_choice_set_eqF:
  "!set :Xs .. SPf =F !set :Xs ..seq SPf"
apply (simp add: fsfF_Rep_int_choice_set_def)
apply (simp add: Rep_int_choice_set_def)
apply (simp add: cspF_fsfF_Rep_int_choice_eqF)
done

lemma cspF_fsfF_Rep_int_choice_com_eqF:
  "! :X .. SPf =F ! :X ..seq SPf"
apply (simp add: fsfF_Rep_int_choice_com_def)
apply (simp add: Rep_int_choice_com_def)
apply (simp add: cspF_fsfF_Rep_int_choice_set_eqF)
done

lemma cspF_fsfF_Rep_int_choice_f_eqF:
  "inj f ==>
   !<f> :X .. SPf =F !<f> :X ..seq SPf"
apply (insert cspF_fsfF_Rep_int_choice_com_eqF
              [of "(f ` X)" "(%x. SPf (inv f x))"])
apply (simp add: Rep_int_choice_f_def)
apply (simp add: fsfF_Rep_int_choice_f_def)
done

(*============================================================*
 |                                                            |
 |                        Int_choice                          |
 |                                                            |
 *============================================================*)

definition
  fsfF_Int_choice ::
  "('p,'a) proc => ('p,'a) proc => ('p,'a) proc"
        ("(1_ /|~|seq _)" [64,65] 64)

  where
  fsfF_Int_choice_def :
    "P |~|seq Q ==
           !nat : {0, (Suc 0)} ..
               (%x. if (x = 0) then P else Q)"

(*------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------*)

lemma fsfF_Int_choice_in:
  "[| P : fsfF_proc ; Q : fsfF_proc |] ==>
   P |~|seq Q : fsfF_proc"
apply (simp add: fsfF_Int_choice_def)
apply (simp add: Rep_int_choice_ss_def)
apply (rule fsfF_proc_int)
apply (auto)
done

(*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*)

lemma cspF_fsfF_Int_choice_eqF:
  "P |~| Q =F P |~|seq Q"
apply (simp add: fsfF_Int_choice_def)
apply (rule cspF_rw_left)
apply (rule cspF_Int_choice_to_Rep)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_rw_left)
apply (rule cspF_IF_split)
apply (auto)
done

(****************** to add them again ******************)

declare if_split    [split]
declare disj_not1   [simp]

end
