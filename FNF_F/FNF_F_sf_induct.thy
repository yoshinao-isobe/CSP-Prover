           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                January 2006               |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory FNF_F_sf_induct
imports FNF_F_sf_int
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

         1. induction method for full sequentialization
         2. 
         3. 

 *****************************************************************)

(*============================================================*
 |                         Pfun P1 P2                         |
 *============================================================*)
(*
consts
  fsfF_induct2_rel ::
  "(('p,'a) proc => ('p,'a) proc => ('p,'a) proc) =>

   ('a set => ('a => ('p,'a) proc) => ('p,'a) proc =>
    'a set => ('a => ('p,'a) proc) => ('p,'a) proc => 
    ('a => ('p,'a) proc) =>
    ('a => ('p,'a) proc) => 
    ('a => ('p,'a) proc) => ('p,'a) proc) =>

   (('p,'a) proc * ('p,'a) proc * ('p,'a) proc) set"

  fsfF_induct2 ::
  "(('p,'a) proc => ('p,'a) proc => ('p,'a) proc) =>

   ('a set => ('a => ('p,'a) proc) => ('p,'a) proc => 
    'a set => ('a => ('p,'a) proc) => ('p,'a) proc => 
    ('a => ('p,'a) proc) =>
    ('a => ('p,'a) proc) =>
    ('a => ('p,'a) proc) => ('p,'a) proc) =>

   ('p,'a) proc => ('p,'a) proc => ('p,'a) proc"
*)
(* 

   Pfun P1 P2
   SP_step  A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2

*)

(*** relation ***)

inductive_set
  fsfF_induct2_rel ::
  "(('p,'a) proc => ('p,'a) proc => ('p,'a) proc) =>

   ('a set => ('a => ('p,'a) proc) => ('p,'a) proc =>
    'a set => ('a => ('p,'a) proc) => ('p,'a) proc => 
    ('a => ('p,'a) proc) =>
    ('a => ('p,'a) proc) => 
    ('a => ('p,'a) proc) => ('p,'a) proc) =>

   (('p,'a) proc * ('p,'a) proc * ('p,'a) proc) set"
for
 Pfun :: "(('p,'a) proc => ('p,'a) proc => ('p,'a) proc)"
and
 SP_step :: "('a set => ('a => ('p,'a) proc) => ('p,'a) proc =>
    'a set => ('a => ('p,'a) proc) => ('p,'a) proc => 
    ('a => ('p,'a) proc) =>
    ('a => ('p,'a) proc) => 
    ('a => ('p,'a) proc) => ('p,'a) proc)"

where
fsfF_induct2_rel_etc_left:
  "[| P1 ~: fsfF_proc |]
   ==> (P1, P2, Pfun P1 P2)
   : fsfF_induct2_rel Pfun SP_step" 
|
fsfF_induct2_rel_etc_right:
  "[| P2 ~: fsfF_proc |]
   ==> (P1, P2, Pfun P1 P2)
   : fsfF_induct2_rel Pfun SP_step"
|
fsfF_induct2_rel_step_int_left:
  "[| ALL c. if (c: sumset C1)
             then (Rf1 c, P2, SRf c) : fsfF_induct2_rel Pfun SP_step
             else SRf c = DIV ;                           
      sumset C1 ~= {} ; ALL c: sumset C1. Rf1 c : fsfF_proc ;
      P2 : fsfF_proc |]
   ==>
   ((!! :C1 .. Rf1), P2, !! c:C1 .. SRf c)
   : fsfF_induct2_rel Pfun SP_step"
|
fsfF_induct2_rel_step_int_right:
  "[| ALL c. if (c: sumset C2)
             then (P1, Rf2 c, SRf c) : fsfF_induct2_rel Pfun SP_step
             else SRf c = DIV ;                           
      sumset C2 ~= {} ; ALL c: sumset C2. Rf2 c : fsfF_proc ;
      P1 : fsfF_proc ; (EX A Pf Q. P1 = (? :A -> Pf) [+] Q) |]
   ==>
   (P1, (!! :C2 .. Rf2),  !! c:C2 .. SRf c)
   : fsfF_induct2_rel Pfun SP_step"
|
fsfF_induct2_rel_step:
  "[| ALL a. if (a:A1 & a:A2) 
             then (Pf1 a, Pf2 a, SPf a) : fsfF_induct2_rel Pfun SP_step
             else SPf a = DIV ;
      ALL a. if a:A1 
             then (Pf1 a, (? :A2 -> Pf2) [+] Q2, SPf1 a) : fsfF_induct2_rel Pfun SP_step
             else SPf1 a = DIV ;
      ALL a. if a:A2
             then ((? :A1 -> Pf1) [+] Q1, Pf2 a, SPf2 a) : fsfF_induct2_rel Pfun SP_step
             else SPf2 a = DIV ;
      ALL a:A1. Pf1 a : fsfF_proc ;
      ALL a:A2. Pf2 a : fsfF_proc ;
      Q1 = SKIP | Q1 = DIV | Q1 = STOP ;
      Q2 = SKIP | Q2 = DIV | Q2 = STOP |]
   ==> 
   ((? :A1 -> Pf1) [+] Q1, (? :A2 -> Pf2) [+] Q2, 
    SP_step A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2)
   : fsfF_induct2_rel Pfun SP_step"

(*** function ***)

definition
  fsfF_induct2 ::
  "(('p,'a) proc => ('p,'a) proc => ('p,'a) proc) =>

   ('a set => ('a => ('p,'a) proc) => ('p,'a) proc => 
    'a set => ('a => ('p,'a) proc) => ('p,'a) proc => 
    ('a => ('p,'a) proc) =>
    ('a => ('p,'a) proc) =>
    ('a => ('p,'a) proc) => ('p,'a) proc) =>

   ('p,'a) proc => ('p,'a) proc => ('p,'a) proc"

  where
  fsfF_induct2_def:
    "fsfF_induct2 Pfun SP_step ==
     (%P1 P2. THE SP. (P1, P2, SP) 
      : fsfF_induct2_rel Pfun SP_step)"

(****************************************************************
 |                      uniquness                               |
 ****************************************************************)

lemma fsfF_induct2_rel_unique_in_lm:
   "(P1, P2, SP1) : fsfF_induct2_rel Pfun SP_step
    ==> (ALL SP2. ((P1, P2, SP2) : fsfF_induct2_rel Pfun SP_step
                   --> SP1 = SP2))"
apply (rule fsfF_induct2_rel.induct[of P1 P2 SP1])
apply (simp)

(* etc_left *)
apply (intro allI impI)
apply (rotate_tac -1)
apply (erule fsfF_induct2_rel.cases)
apply (simp_all)
apply (simp add: fsfF_proc_int)
apply (simp add: fsfF_proc_ext)

(* etc_right *)
apply (intro allI impI)
apply (rotate_tac -1)
apply (erule fsfF_induct2_rel.cases)
apply (simp_all)
apply (simp add: fsfF_proc_int)
apply (simp add: fsfF_proc_ext)

(* step_int_left *)
apply (intro allI impI)
apply (rotate_tac -1)
apply (erule fsfF_induct2_rel.cases, simp_all)

 apply (rotate_tac -4)
 apply (drule sym)
 apply (simp add: fsfF_proc_int)

 apply (subgoal_tac "SRf = SRfa", simp)
 apply (simp add: fun_eq_iff)
 apply (intro allI)
 apply (drule_tac x="x" in spec)+
 apply (case_tac "x : sumset C1")
 apply (simp)
 apply (simp)

 apply (elim conjE exE)
 apply (rotate_tac -8)
 apply (drule sym)
 apply (simp)

 apply (elim conjE exE)
 apply (simp)

(* step_int_right *)
apply (intro allI impI)
apply (rotate_tac -1)
apply (erule fsfF_induct2_rel.cases, simp_all)

 apply (rotate_tac -3)
 apply (drule sym)
 apply (simp add: fsfF_proc_int)

 apply (subgoal_tac "SRf = SRfa", simp)
 apply (simp add: fun_eq_iff)
 apply (intro allI)
 apply (drule_tac x="x" in spec)+
 apply (case_tac "x : sumset C2")
 apply (simp)
 apply (simp)

(* step *)
apply (intro allI impI)
apply (rotate_tac -1)
apply (erule fsfF_induct2_rel.cases, simp_all)

 apply (rotate_tac -4)
 apply (drule sym)
 apply (simp add: fsfF_proc_ext)

 apply (rotate_tac -3)
 apply (drule sym)
 apply (simp add: fsfF_proc_ext)

 apply (subgoal_tac "SPf = SPfa & SPf1 = SPf1a & SPf2 = SPf2a ", simp)

  apply (rule conjI)
  apply (simp add: fun_eq_iff)
  apply (rule allI)
  apply (drule_tac x="x" in spec)+
  apply (case_tac "x : A1a & x : A2a")
  apply (simp_all)

  apply (rule conjI)
  apply (simp (no_asm_simp) add: fun_eq_iff)
  apply (rule allI)
  apply (drule_tac x="x" in spec)+
  apply (case_tac "x : A1a")
  apply (simp_all)

  apply (simp (no_asm_simp) add: fun_eq_iff)
  apply (rule allI)
  apply (drule_tac x="x" in spec)+
  apply (case_tac "x : A2a")
  apply (simp_all)
done

(*-----------------------*
 |        unique         |
 *-----------------------*)

lemma fsfF_induct2_rel_unique:
   "[| (P1, P2, SP1) : fsfF_induct2_rel Pfun SP_step;
       (P1, P2, SP2) : fsfF_induct2_rel Pfun SP_step |]
    ==> SP1 = SP2"
by (simp add: fsfF_induct2_rel_unique_in_lm)

lemma fsfF_induct2_rel_EX1:
   "(EX SP. (P1, P2, SP) : fsfF_induct2_rel Pfun SP_step)
 = (EX! SP. (P1, P2, SP) : fsfF_induct2_rel Pfun SP_step)"
apply (rule iffI)

 apply (erule exE)
 apply (rule_tac a="SP" in ex1I)
 apply (simp)
 apply (simp add: fsfF_induct2_rel_unique)

 apply (elim ex1_implies_exE)
 apply (simp)
done

(*------------------------------------------------------------*
 |                   fsfF_induct2_rel (iff)                   |
 *------------------------------------------------------------*)

(* etc_left *)

lemma fsfF_induct2_rel_etc_left_iff:
  "P1 ~: fsfF_proc
   ==> (P1, P2, SP) : fsfF_induct2_rel Pfun SP_step
       = (SP = Pfun P1 P2)"
apply (rule)
apply (erule fsfF_induct2_rel.cases, simp_all)
 apply (simp add: fsfF_proc_int)
 apply (simp add: fsfF_proc_ext)
apply (simp add: fsfF_induct2_rel_etc_left)
done

(* etc_right *)

lemma fsfF_induct2_rel_etc_right_iff:
  "P2 ~: fsfF_proc
   ==> (P1, P2, SP) : fsfF_induct2_rel Pfun SP_step
       = (SP = Pfun P1 P2)"
apply (rule)
apply (erule fsfF_induct2_rel.cases, simp_all)

 apply (simp add: fsfF_proc_int)
 apply (simp add: fsfF_proc_ext)
apply (simp add: fsfF_induct2_rel_etc_right)
done

(* step_int_left *)

lemma fsfF_induct2_rel_step_int_left_iff:
  "[| ALL c. if c: sumset C1 then 
               (Rf1 c, P2, SRf c) : fsfF_induct2_rel Pfun SP_step
             else SRf c = DIV ;
      sumset C1 ~= {} ; ALL c. Rf1 c : fsfF_proc ;
      P2 : fsfF_proc |]
   ==>
   ((!! :C1 .. Rf1), P2, SP) : fsfF_induct2_rel Pfun SP_step
   = (SP = !! :C1 .. SRf)"
apply (rule)
apply (erule fsfF_induct2_rel.cases, simp_all)

 apply (rotate_tac -4)
 apply (drule sym)
 apply (simp add: fsfF_proc_int)

 apply (subgoal_tac "SRfa = SRf", simp)
 apply (simp add: fun_eq_iff)
 apply (rule allI)
 apply (drule_tac x="x" in spec)+
 apply (case_tac "x : sumset C1a")
 apply (simp add: fsfF_induct2_rel_unique)

 apply (simp)
 apply (elim conjE exE)
 apply (rotate_tac -8)
 apply (drule sym)
 apply (simp)

apply (simp add: fsfF_induct2_rel_step_int_left)
done

(* step *)

lemma fsfF_induct2_rel_step_iff:
  "[| ALL a. if (a:A1 & a:A2) 
             then (Pf1 a, Pf2 a, SPf a) : fsfF_induct2_rel Pfun SP_step
             else SPf a = DIV ;
      ALL a. if a:A1 
             then (Pf1 a, (? :A2 -> Pf2) [+] Q2, SPf1 a) : fsfF_induct2_rel Pfun SP_step
             else SPf1 a = DIV ;
      ALL a. if a:A2
             then ((? :A1 -> Pf1) [+] Q1, Pf2 a, SPf2 a) : fsfF_induct2_rel Pfun SP_step
             else SPf2 a = DIV ;
      ALL a:A1. Pf1 a : fsfF_proc ;
      ALL a:A2. Pf2 a : fsfF_proc ;
      Q1 = SKIP | Q1 = DIV | Q1 = STOP ;
      Q2 = SKIP | Q2 = DIV | Q2 = STOP |]
   ==> 
   ((? :A1 -> Pf1) [+] Q1, (? :A2 -> Pf2) [+] Q2, SP) : fsfF_induct2_rel Pfun SP_step
   = (SP = SP_step A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2)"
apply (rule)
apply (erule fsfF_induct2_rel.cases, simp_all)

 apply (rotate_tac -4)
 apply (drule sym)
 apply (simp add: fsfF_proc_ext)

 apply (rotate_tac -3)
 apply (drule sym)
 apply (simp add: fsfF_proc_ext)

 apply (subgoal_tac "SPf = SPfa & SPf1 = SPf1a & SPf2 = SPf2a ", simp)
 apply (simp (no_asm_simp) add: fun_eq_iff)
 apply (intro allI conjI)

 apply (drule_tac x="x" in spec)+
 apply (case_tac "x : A1a & x : A2a")
 apply (simp add: fsfF_induct2_rel_unique)
 apply (simp)
 apply (drule_tac x="x" in spec)+
 apply (case_tac "x : A1a")
 apply (simp add: fsfF_induct2_rel_unique)
 apply (simp)
 apply (drule_tac x="x" in spec)+
 apply (case_tac "x : A2a")
 apply (simp add: fsfF_induct2_rel_unique)
 apply (simp)

apply (simp add: fsfF_induct2_rel_step)
done

(****************************************************************
 |                      existency                               |
 ****************************************************************)

(*** exists ***)

lemma fsfF_induct2_rel_exists_notin1:
   "P1 ~: fsfF_proc
    ==> (EX SP. (P1, P2, SP)
                : fsfF_induct2_rel Pfun SP_step)"
apply (rule_tac x="Pfun P1 P2" in exI)
apply (simp add: fsfF_induct2_rel.intros)
done

lemma fsfF_induct2_rel_exists_notin2:
   "P2 ~: fsfF_proc
    ==> (EX SP. (P1, P2, SP)
                : fsfF_induct2_rel Pfun SP_step)"
apply (rule_tac x="Pfun P1 P2" in exI)
apply (simp add: fsfF_induct2_rel.intros)
done

(*** in fsfF_proc ***)

(********* P1 and P2 *********)

lemma fsfF_induct2_rel_exists_in_lm1:
 "P2 : fsfF_proc ==>
   (ALL a:A. Pf a : fsfF_proc &
   (ALL P2. EX SP. (Pf a, P2, SP) : fsfF_induct2_rel Pfun SP_step)) &
   (Q = SKIP | Q = DIV | Q = STOP)
    --> (EX SP. (? :A -> Pf [+] Q, P2, SP) : fsfF_induct2_rel Pfun SP_step)"
apply (rule fsfF_proc.induct[of P2])
apply (simp)

(* proc int *)
apply (intro allI impI)
apply (elim conjE)
apply (simp add: Ball_def)
apply (simp add: dist_ALL_imply_conjE)
apply (elim conjE)
apply (simp add: choice_ALL_imply_EX)
apply (erule exE)
apply (rule_tac x="!! c:C .. (if c: sumset C then f c else DIV)" in exI)
apply (rule fsfF_induct2_rel.intros)
apply (simp_all)
apply (rule allI)
apply (simp split: if_split)
apply (rule fsfF_proc_ext)
apply (simp_all)

(* step *)
apply (intro allI impI)
apply (elim conjE)
apply (rotate_tac -2)
apply (erule dist_BALL_conjE)

apply (simp add: exchange_ALL_BALL)
apply (frule_tac x="? :Aa -> Pfa [+] Qa" in spec)
apply (erule ALL_BALL_funE)
apply (drule_tac x="Pfa" in spec)
apply (simp add: choice_BALL_EX)
apply (elim exE)
apply (erule dist_BALL_conjE)
apply (simp add: choice_BALL_EX)
apply (elim exE)
apply (rename_tac Aa Pfa Qa SPf1 SPf SPf2)
apply (rule_tac x="SP_step A Pf Q Aa Pfa Qa 
                   (%a. if (a:A & a:Aa) then SPf a else DIV)
                   (%a. if (a:A) then SPf1 a else DIV)
                   (%a. if (a:Aa) then SPf2 a else DIV)" in exI)
apply (rule fsfF_induct2_rel.intros)
apply (simp_all)
apply (simp split: if_split)
apply (simp split: if_split)
apply (simp split: if_split)
done

lemma fsfF_induct2_rel_exists_in_lm:
   "P1 : fsfF_proc
      ==> (ALL P2. (EX SP. (P1, P2, SP) 
              : fsfF_induct2_rel Pfun SP_step))"
apply (rule fsfF_proc.induct[of P1])
apply (simp)

apply (intro allI)
apply (case_tac "P2 ~: fsfF_proc")
apply (simp add: fsfF_induct2_rel_exists_notin2)
apply (simp)

(* P2 : fsfF_proc *)
apply (erule dist_BALL_conjE)
apply (simp add: exchange_ALL_BALL)
apply (drule_tac x="P2" in spec)
apply (simp add: choice_BALL_EX)
apply (erule exE)
apply (rule_tac x="!! c:C .. (if c: sumset C then f c else DIV)" in exI)
apply (rule fsfF_induct2_rel.intros)
apply (simp_all)
apply (rule allI)
apply (simp split: if_split)

apply (intro allI)
apply (case_tac "P2 ~: fsfF_proc")
apply (simp add: fsfF_induct2_rel_exists_notin2)
apply (simp)

(* step *)
apply (case_tac "P2 ~: fsfF_proc")
apply (simp add: fsfF_induct2_rel_exists_notin2)
apply (simp add: fsfF_induct2_rel_exists_in_lm1)
done

lemma fsfF_induct2_rel_exists_in:
   "P1 : fsfF_proc
    ==> (EX SP. (P1, P2, SP) :  fsfF_induct2_rel Pfun SP_step)"
apply (insert fsfF_induct2_rel_exists_in_lm
              [of P1 Pfun SP_step])
apply (simp_all)
done

(*-----------------------*
 |        exists         |
 *-----------------------*)

lemma fsfF_induct2_rel_exists:
   "EX SP. (P1, P2, SP) :  fsfF_induct2_rel Pfun SP_step"
apply (case_tac "P1 ~: fsfF_proc")
apply (simp add: fsfF_induct2_rel_exists_notin1)
apply (simp add: fsfF_induct2_rel_exists_in)
done

(*-----------------------*
 |    uniquely exists    |
 *-----------------------*)

lemma fsfF_induct2_rel_unique_exists:
   "EX! SP. (P1, P2, SP) :  fsfF_induct2_rel Pfun SP_step"
apply (simp add: fsfF_induct2_rel_EX1[THEN sym])
apply (simp add: fsfF_induct2_rel_exists)
done

(*------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------*)

lemma fsfF_induct2_rel_in_lm:
   "[| (P1, P2, SP) : fsfF_induct2_rel Pfun SP_step ;

    !! A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2. 
                   [| ALL a:A1. Pf1 a : fsfF_proc ; 
                      ALL a:A2. Pf2 a : fsfF_proc ; 
                      ALL a:(A1 Int A2). SPf a : fsfF_proc ;
                      ALL a:A1. SPf1 a : fsfF_proc ;
                      ALL a:A2. SPf2 a : fsfF_proc ;

                      Q1 = SKIP | Q1 = DIV | Q1 = STOP ;
                      Q2 = SKIP | Q2 = DIV | Q2 = STOP |]
        ==> SP_step A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2 : fsfF_proc |]

    ==> (P1 : fsfF_proc & P2 : fsfF_proc)
             --> SP : fsfF_proc"
apply (rule fsfF_induct2_rel.induct[of P1 P2 SP])
apply (simp_all)
apply (intro impI)
apply (rule fsfF_proc.intros)
apply (simp_all)
apply (intro impI)
apply (rule fsfF_proc.intros)
apply (simp_all)
done

(*------------------------------------*
 |                 in                 |
 *------------------------------------*)

lemma fsfF_induct2_rel_in:
   "[| (P1, P2, SP) : fsfF_induct2_rel Pfun SP_step ;
       P1 : fsfF_proc ;
       P2 : fsfF_proc ;

    !! A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2. 
                   [| ALL a:A1. Pf1 a : fsfF_proc ; 
                      ALL a:A2. Pf2 a : fsfF_proc ; 
                      ALL a:(A1 Int A2). SPf a : fsfF_proc ;
                      ALL a:A1. SPf1 a : fsfF_proc ;
                      ALL a:A2. SPf2 a : fsfF_proc ;

                      Q1 = SKIP | Q1 = DIV | Q1 = STOP ;
                      Q2 = SKIP | Q2 = DIV | Q2 = STOP |]
        ==> SP_step A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2 : fsfF_proc |]

    ==> SP : fsfF_proc"
apply (simp add: fsfF_induct2_rel_in_lm)
done

(*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*)

(*** relation ***)

lemma cspF_fsfF_induct2_rel_eqF:
    "[| (P1, P2, SP) : fsfF_induct2_rel Pfun SP_step ;

    !!C1 Rf1 P2. sumset C1 ~= {} ==> 
      Pfun (!! :C1 .. Rf1) P2 =F (!! c:C1 .. Pfun (Rf1 c) P2) ;
    !!P1 C2 Rf2. sumset C2 ~= {} ==>
      Pfun P1 (!! :C2 .. Rf2) =F (!! c:C2 .. Pfun P1 (Rf2 c)) ;

    !!A1 Pf1 Q1 A2 Pf2 Q2. [| Q1 = SKIP | Q1 = DIV | Q1 = STOP ;
                              Q2 = SKIP | Q2 = DIV | Q2 = STOP |]
             ==> Pfun (? :A1 -> Pf1 [+] Q1) (? :A2 -> Pf2 [+] Q2)
                 =F SP_step A1 Pf1 Q1 A2 Pf2 Q2
                   (%a. Pfun (Pf1 a) (Pf2 a))
                   (%a. Pfun (Pf1 a) (? :A2 -> Pf2 [+] Q2))
                   (%a. Pfun (? :A1 -> Pf1 [+] Q1) (Pf2 a)) ;

    !!A1 Pf1 Q1 A2 Pf2 Q2 SPf SQf SPf1 SQf1 SPf2 SQf2. 
         [| ALL a:(A1 Int A2). SPf a =F SQf a ; 
            ALL a:A1. SPf1 a =F SQf1 a ; ALL a:A2. SPf2 a =F SQf2 a |]
      ==> SP_step A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2 =F
          SP_step A1 Pf1 Q1 A2 Pf2 Q2 SQf SQf1 SQf2 |]

  ==> Pfun P1 P2 =F SP"
apply (rule fsfF_induct2_rel.induct[of P1 P2 SP])
apply (simp_all)

(* etc *)
apply (rule cspF_reflex)
apply (rule cspF_reflex)

(* step_int_left *)
apply (rule cspF_rw_left)
apply (subgoal_tac
   "Pfun (!! :C1 .. Rf1) P2a =F (!! c:C1 .. (Pfun (Rf1 c) P2a))")
apply (assumption)
apply (simp_all)

(* step_int_right *)
apply (rule cspF_rw_left)
apply (subgoal_tac 
  "Pfun P1a (!! :C2 .. Rf2) =F (!! c:C2 .. (Pfun P1a (Rf2 c)))")
apply (assumption)
apply (simp_all)

(* step *)
apply (rule cspF_rw_left)
apply (subgoal_tac 
  "Pfun (? :A1 -> Pf1 [+] Q1) (? :A2 -> Pf2 [+] Q2) =F 
          SP_step A1 Pf1 Q1 A2 Pf2 Q2 
                  (%a. Pfun (Pf1 a) (Pf2 a))
                  (%a. Pfun (Pf1 a) (? :A2 -> Pf2 [+] Q2))
                  (%a. Pfun (? :A1 -> Pf1 [+] Q1) (Pf2 a))")
apply (assumption)
apply (simp_all)
done

(*************************************************************
                  relation --> function
 *************************************************************)

lemma fsfF_induct2_in_rel:
    "(P1, P2, fsfF_induct2 Pfun SP_step P1 P2)
     : fsfF_induct2_rel Pfun SP_step"
apply (simp add: fsfF_induct2_def)
apply (rule theI'
  [of "(%R. (P1, P2, R) : fsfF_induct2_rel Pfun SP_step)"])
apply (simp add: fsfF_induct2_rel_unique_exists)
done

lemma fsfF_induct2_from_rel:
    "((P1, P2, SP) : fsfF_induct2_rel Pfun SP_step) 
   = (fsfF_induct2 Pfun SP_step P1 P2 = SP)"
apply (rule iffI)
apply (simp add: fsfF_induct2_def)
apply (simp add: fsfF_induct2_rel_unique_exists the1_equality)

apply (drule sym)
apply (simp add: fsfF_induct2_in_rel)
done

lemma fsfF_induct2_to_rel:
    "(fsfF_induct2 Pfun SP_step P1 P2 = SP)
   = ((P1, P2, SP) : fsfF_induct2_rel Pfun SP_step)"
by (simp add: fsfF_induct2_from_rel)

(*************************************************************
                          function
 *************************************************************)

lemma fsfF_induct2_etc:
  "[| P1 ~: fsfF_proc | P2 ~: fsfF_proc |]
   ==> fsfF_induct2 Pfun SP_step P1 P2 = Pfun P1 P2"
apply (simp add: fsfF_induct2_to_rel)
apply (erule disjE)
apply (simp add: fsfF_induct2_rel_etc_left_iff)
apply (simp add: fsfF_induct2_rel_etc_right_iff)
done

lemma fsfF_induct2_step_int_left:
  "[| sumset C1 ~= {} ; ALL c: sumset C1. Rf1 c : fsfF_proc ;
      P2 : fsfF_proc |]
   ==>
   fsfF_induct2 Pfun SP_step (!! :C1 .. Rf1) P2
   = !! c:C1 .. (if c: sumset C1 then 
                 fsfF_induct2 Pfun SP_step (Rf1 c) P2 else DIV)"
apply (simp add: fsfF_induct2_to_rel)
apply (rule fsfF_induct2_rel_step_int_left)
apply (simp_all)
apply (simp split: if_split)
apply (simp add: fsfF_induct2_in_rel)
done

lemma fsfF_induct2_step_int_right:
  "[| sumset C2 ~= {} ; ALL c: sumset C2. Rf2 c : fsfF_proc ;
      P1 : fsfF_proc ; (EX A Pf Q. P1 = (? :A -> Pf) [+] Q) |]
   ==>
   fsfF_induct2 Pfun SP_step P1 (!! :C2 .. Rf2)
   = !! c:C2 .. (if c: sumset C2 then 
                 fsfF_induct2 Pfun SP_step P1 (Rf2 c) else DIV)"
apply (simp add: fsfF_induct2_to_rel)
apply (rule fsfF_induct2_rel_step_int_right)
apply (simp_all)
apply (simp split: if_split)
apply (simp add: fsfF_induct2_in_rel)
done

lemma fsfF_induct2_step:
  "[| ALL a:A1. Pf1 a : fsfF_proc ;
      ALL a:A2. Pf2 a : fsfF_proc ;
      Q1 = SKIP | Q1 = DIV | Q1 = STOP ;
      Q2 = SKIP | Q2 = DIV | Q2 = STOP |]
   ==> 
   fsfF_induct2 Pfun SP_step 
               ((? :A1 -> Pf1) [+] Q1) ((? :A2 -> Pf2) [+] Q2)
 = (SP_step  A1 Pf1 Q1 A2 Pf2 Q2
   (%a. if a:A1 Int A2 then fsfF_induct2 Pfun SP_step (Pf1 a) (Pf2 a) else DIV)
   (%a. if a:A1 then fsfF_induct2 Pfun SP_step (Pf1 a) ((? :A2 -> Pf2) [+] Q2) else DIV)
   (%a. if a:A2 then fsfF_induct2 Pfun SP_step ((? :A1 -> Pf1) [+] Q1) (Pf2 a) else DIV))"
apply (simp add: fsfF_induct2_to_rel)
apply (rule fsfF_induct2_rel_step[of
A1 A2 Pf1 Pf2 
"(%a. if a : A1 & a : A2 then fsfF_induct2 Pfun SP_step (Pf1 a) (Pf2 a) else DIV)"
Pfun SP_step Q2 
"(%a. if a : A1 then fsfF_induct2 Pfun SP_step (Pf1 a) (? :A2 -> Pf2 [+] Q2) else DIV)"
Q1 
"(%a. if a : A2 then fsfF_induct2 Pfun SP_step (? :A1 -> Pf1 [+] Q1) (Pf2 a) else DIV)"
])
apply (simp_all split: if_split)
apply (simp_all add: fsfF_induct2_in_rel)
done

lemmas fsfF_induct2 =
       fsfF_induct2_etc
       fsfF_induct2_step_int_left
       fsfF_induct2_step_int_right
       fsfF_induct2_step

(*------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------*)

lemma fsfF_induct2_in:
   "[| P1 : fsfF_proc ;
       P2 : fsfF_proc ;

    !! A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2. 
                   [| ALL a:A1. Pf1 a : fsfF_proc ; 
                      ALL a:A2. Pf2 a : fsfF_proc ; 
                      ALL a:(A1 Int A2). SPf a : fsfF_proc ;
                      ALL a:A1. SPf1 a : fsfF_proc ;
                      ALL a:A2. SPf2 a : fsfF_proc ;

                      Q1 = SKIP | Q1 = DIV | Q1 = STOP ;
                      Q2 = SKIP | Q2 = DIV | Q2 = STOP |]
        ==> SP_step A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2 : fsfF_proc |]
    ==> fsfF_induct2 Pfun SP_step P1 P2 : fsfF_proc"
apply (rule fsfF_induct2_rel_in
            [of P1 P2 _ Pfun SP_step])
apply (simp_all add: fsfF_induct2_in_rel)
done

(*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*)

lemma cspF_fsfF_induct2_eqF:
"[| 
    !!C1 Rf1 P2. sumset C1 ~= {} ==> 
    Pfun (!! :C1 .. Rf1) P2 =F (!! c:C1 .. Pfun (Rf1 c) P2);
    !!P1 C2 Rf2. sumset C2 ~= {} ==> 
    Pfun P1 (!! :C2 .. Rf2) =F (!! c:C2 .. Pfun P1 (Rf2 c));

    !!A1 Pf1 Q1 A2 Pf2 Q2. [| Q1 = SKIP | Q1 = DIV | Q1 = STOP ;
                              Q2 = SKIP | Q2 = DIV | Q2 = STOP |]
             ==> Pfun (? :A1 -> Pf1 [+] Q1) (? :A2 -> Pf2 [+] Q2)
                 =F SP_step A1 Pf1 Q1 A2 Pf2 Q2
                   (%a. Pfun (Pf1 a) (Pf2 a))
                   (%a. Pfun (Pf1 a) (? :A2 -> Pf2 [+] Q2))
                   (%a. Pfun (? :A1 -> Pf1 [+] Q1) (Pf2 a)) ;

    !!A1 Pf1 Q1 A2 Pf2 Q2 SPf SQf SPf1 SQf1 SPf2 SQf2. 
         [| ALL a:(A1 Int A2). SPf a =F SQf a ; 
            ALL a:A1. SPf1 a =F SQf1 a ; ALL a:A2. SPf2 a =F SQf2 a |]
      ==> SP_step A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2 =F
          SP_step A1 Pf1 Q1 A2 Pf2 Q2 SQf SQf1 SQf2 |]

  ==> Pfun P1 P2 =F fsfF_induct2 Pfun SP_step P1 P2"
apply (rule cspF_fsfF_induct2_rel_eqF
            [of P1 P2 "fsfF_induct2 Pfun SP_step P1 P2"
                Pfun SP_step])
apply (simp_all add: fsfF_induct2_in_rel)
done

(*===========================================================*
 |                                                           |
 |               fsfF_induct1 (take one process)             |
 |                                                           |
 *===========================================================*)

definition
  fsfF_induct1 ::
  "(('p,'a) proc => ('p,'a) proc) =>
   ('a set => ('a => ('p,'a) proc) => ('p,'a) proc =>
              ('a => ('p,'a) proc) => ('p,'a) proc) =>
   ('p,'a) proc => ('p,'a) proc"

(* 
   Pfun P1
   SP_step  A1 Pf1 Q1 SPf1
*)

  where
  fsfF_induct1_def :
    "fsfF_induct1 Pfun SP_step == (%P1. 
       (fsfF_induct2 (%P1 P2. Pfun P1) 
                     (%A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2. SP_step A1 Pf1 Q1 SPf1)
                      P1 SDIV))"

(*------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------*)

lemma fsfF_induct1_in:
    "[| P1 : fsfF_proc ;
    !! A Pf Q SPf. [| ALL a:A. Pf a : fsfF_proc ; 
                      ALL a:A. SPf a : fsfF_proc ; 
                      Q = SKIP | Q = DIV | Q = STOP |]
            ==> SP_step A Pf Q SPf : fsfF_proc |]
     ==> fsfF_induct1  Pfun SP_step P1 : fsfF_proc"
apply (simp add: fsfF_induct1_def)
apply (rule fsfF_induct2_in)
apply (simp_all)
done

(*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*)

lemma cspF_fsfF_induct1_eqF:
    "[| !!C1 Rf1. sumset C1 ~= {} ==>
         Pfun (!! :C1 .. Rf1) =F (!! c:C1 .. Pfun (Rf1 c)) ;

        !!A1 Pf1 Q1. Q1 = SKIP | Q1 = DIV | Q1 = STOP
             ==> Pfun (? :A1 -> Pf1 [+] Q1)
                 =F SP_step A1 Pf1 Q1 (%a. Pfun (Pf1 a)) ;

        !!A1 Pf1 Q1 SPf SQf. ALL a:A1. SPf a =F SQf a 
             ==> SP_step A1 Pf1 Q1 SPf =F SP_step A1 Pf1 Q1 SQf |]
     ==> Pfun P1 =F fsfF_induct1 Pfun SP_step P1"
apply (simp add: fsfF_induct1_def)
apply (rule cspF_rw_right)
apply (rule cspF_fsfF_induct2_eqF[THEN cspF_sym])
apply (simp_all)
apply (simp add: cspF_Rep_int_choice_unit[THEN cspF_sym])
done

(****************** to add them again ******************)

declare if_split    [split]
declare disj_not1   [simp]

end
