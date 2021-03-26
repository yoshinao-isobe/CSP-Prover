           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   June 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                January 2007  (modified)   |
            |                  April 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2007         |
            |                January 2008  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                  April 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_syntax
imports Infra
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  Union (B ` A) = (UN x:A. B x)                      *)
(*                  Inter (B ` A) = (INT x:A. B x)                     *)

(* for Isabelle 2016
declare Union_image_eq [simp del]
declare Inter_image_eq [simp del]
*)


type_synonym 'e alphabet = "('e) set"

abbreviation chanset :: "('a => 'e) =>  'e alphabet" ("{| _ |}")
where
  "{| c |} == { e . \<exists>x. e = c x }"


(*-----------------------------------------------------------*
 |                                                           |
 |    Process Type Definitions                               |
 |                                                           |
 |             'a proc : type of process expressions         |
 |                       'n : process name                   |
 |                       'a : event                          |
 |                                                           |
 *-----------------------------------------------------------*)

(*********************************************************************
                       process expression
 *********************************************************************)

type_synonym
   'a sets_nats = "('a set set, nat set) sum"
type_synonym
   'a aset_anat = "('a set, nat) sum"

datatype 
 ('p,'a) proc
    = STOP

    | SKIP

    | DIV

    | Act_prefix     "'a" "('p,'a) proc"      ("(1_ /-> _)" [150,80] 80)

    | Ext_pre_choice "'a set" "'a => ('p,'a) proc"
                                               ("(1? :_ /-> _)" [900,80] 80)
    | Ext_choice     "('p,'a) proc" "('p,'a) proc"  
                                               ("(1_ /[+] _)" [72,73] 72)
    | Int_choice     "('p,'a) proc" "('p,'a) proc"  
                                               ("(1_ /|~| _)" [64,65] 64)
    | Rep_int_choice "'a sets_nats" "'a aset_anat => ('p,'a) proc"
                                               ("(1!! :_ .. /_)" [900,68] 68) 
    | IF             "bool" "('p,'a) proc" "('p,'a) proc"
                                 ("(0IF _ /THEN _ /ELSE _)" [900,88,88] 88)
(*                               ("(0IF _ /THEN _ /ELSE _)" [900,60,60] 88) *)
    | Parallel       "('p,'a) proc" "'a set" "('p,'a) proc"  
                                               ("(1_ /|[_]| _)" [76,0,77] 76)
    | Hiding         "('p,'a) proc" "'a set"   ("(1_ /-- _)" [84,85] 84)

    | Renaming       "('p,'a) proc" "('a * 'a) set"
                                               ("(1_ /[[_]])" [84,0] 84)
(*                                               ("(1_ /[[_]])" [84,0] 84) *)
    | Seq_compo      "('p,'a) proc" "('p,'a) proc"  
                                               ("(1_ /;; _)" [79,78] 78)
    | Depth_rest     "('p,'a) proc" "nat"  
                                               ("(1_ /|. _)" [84,900] 84)
    | Proc_name      "'p"                      ("$_" [900] 90)

(*--------------------------------------------------------------------*
 |                                                                    |
 | (1) binding power:                                                 |
 |      Proc_Name > IF > {Hiding, Renaming, Restriction} >            |
 |      {Act_prefix, Ext_pre_choice} > Seq_compo > Parallel >         |
 |      Ext_choice > Rep_int_choice > int_choice                      |
 |                                                                    |
 |   The binding power 90 is higher than ones of processes ops.       |
 |                                                                    |
 | (2) About ("(1_ /-> _)" [150,80] 80)                               |
 |      The nth operator ! has the power 101.                         |
 |      So, 150 > 101 is needed.                                      |
 |                                                                    |
 | (3) "selector" is necessary for having our CSP expressive          |
 |     with respect to the domain for stable-failures model F.        |
 |                                                                    |
 *--------------------------------------------------------------------*)

(*** external prefix ***)

syntax
  "@Ext_pre_choice"  :: "pttrn => 'a set => ('p,'a) proc 
                => ('p,'a) proc"  ("(1? _:_ /-> _)" [900,900,80] 80)

translations
  "? x:X -> P"  == "? :X -> (%x. P)"


syntax
  "@Ext_pre_choice_UNIV" ::  "pttrn => ('p,'a) proc => ('p,'a) proc"
                                           ("(1? _ /-> _)" [900,80] 80)
translations
  "? x -> P"    == "? x:(CONST UNIV) -> P"



(*** Inductive external choice ***)

primrec Inductive_ext_choice :: "(('p,'a) proc) list \<Rightarrow> ('p,'a) proc" ("(1[+] _)" [80] 80)
where
  "[+] [] = STOP"
 |"[+] (P#Ps) = P [+] ( [+] Ps)"



(*** Replicated external choice ***)

definition Rep_ext_choice :: "'x set \<Rightarrow> ('x \<Rightarrow> ('p,'a) proc) \<Rightarrow> ('p,'a) proc"  ("(1[+]_ .. _)" [900,80] 80)
where
  "[+]X .. PXf == [+] [ PXf i . i <- (SOME x . x isListOf X) ]"

syntax
  "@Rep_ext_choice"  ::
      "pttrn \<Rightarrow> 'x set \<Rightarrow> ('p,'a) proc \<Rightarrow> ('p,'a) proc"  ("(1[+] _:_ .. _)" [900,900,80] 80)
translations
  "[+] x:X .. P" == "[+]X .. (%x . P)"



(*** replicated internal choice (bound variable, UNIV) ***)

syntax
  "@Rep_int_choice":: 
      "pttrn => 'a sets_nats => ('p,'a) proc => ('p,'a) proc"  
                               ("(1!! _:_ .. /_)" [900,900,68] 68)
translations
  "!! c:C .. P"    == "!! :C .. (%c. P)"

(* this is not collect *)
(*
syntax
  "@Rep_int_choice_UNIV":: 
      "pttrn => ('p,'a) proc => ('p,'a) proc"
                               ("(1!! _ .. /_)" [900,68] 68)

translations
  "!! c .. P"      == "!! c:UNIV .. P"
*)

(*** set, nat ***)

(*
consts
  Rep_int_choice_set :: 
    "'a set set => ('a set => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1!set :_ .. /_)" [900,68] 68)
  Rep_int_choice_nat ::
    "nat set => (nat => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1!nat :_ .. /_)" [900,68] 68)

defs
  Rep_int_choice_set_def:
        "!set :Xs .. Pf == !! c:(type1 Xs) .. (Pf ((inv type1) c))"
  Rep_int_choice_nat_def:
        "!nat :N .. Pf == !! c:(type2 N) .. (Pf ((inv type2) c))"
*)

definition
  Rep_int_choice_set :: 
    "'a set set => ('a set => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1!set :_ .. /_)" [900,68] 68)
  where
  "!set :Xs .. Pf == !! c:(type1 Xs) .. (Pf ((inv type1) c))"

definition
  Rep_int_choice_nat ::
    "nat set => (nat => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1!nat :_ .. /_)" [900,68] 68)
  where
  Rep_int_choice_nat_def:
        "!nat :N .. Pf == !! c:(type2 N) .. (Pf ((inv type2) c))"

(* bound variable *)

syntax
  "@Rep_int_choice_set" :: 
     "pttrn => ('a set) set => ('a set => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1!set _:_ .. /_)" [900,900,68] 68)
  "@Rep_int_choice_nat" :: 
     "pttrn => nat set => (nat => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1!nat _:_ .. /_)" [900,900,68] 68)

translations
    "!set X:Xs .. P" == "!set :Xs .. (%X. P)"
    "!nat n:N .. P"  == "!nat :N .. (%n. P)"

(* UNIV *)

syntax
  "@Rep_int_choice_set_UNIV" ::
     "pttrn => ('a set => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1!set _ .. /_)" [900,68] 68)
  "@Rep_int_choice_nat_UNIV" ::
     "pttrn => (nat => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1!nat _ .. /_)" [900,68] 68)

translations
      "!set X .. P" == "!set X:(CONST UNIV) .. P"
      "!nat n .. P" == "!nat n:(CONST UNIV) .. P"

(*** com ***)
(* Isabelle 2013
consts
  Rep_int_choice_com :: "'a set => ('a => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1! :_ .. /_)" [900,68] 68)
defs
  Rep_int_choice_com_def :
     "! :A .. Pf == !set X:{{a} |a. a : A} .. Pf (the_elem(X))"
*)

definition
  Rep_int_choice_com :: "'a set => ('a => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1! :_ .. /_)" [900,68] 68)
  where
  "! :A .. Pf == !set X:{{a} |a. a : A} .. Pf (the_elem(X))"

syntax
  "@Rep_int_choice_com" ::
      "pttrn => 'a set => ('a => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1! _:_ .. /_)" [900,900,68] 68)
  "@Rep_int_choice_com_UNIV" ::
      "pttrn => ('a => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1! _ .. /_)" [900,68] 68)
translations
    "! x:X .. P" == "! :X .. (%x. P)"
      "! x .. P" == "! x:(CONST UNIV) .. P"

(*** f ***)

(* Isabelle 2013
consts
  Rep_int_choice_f ::
    "('b => 'a) => 'b set => ('b => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1!<_> :_ .. /_)" [0,900,68] 68)

defs
 Rep_int_choice_f_def : 
        "!<f> :X .. Pf == ! :(f ` X) .. (%x. (Pf ((inv f) x)))"
*)

definition
  Rep_int_choice_f ::
    "('b => 'a) => 'b set => ('b => ('p,'a) proc) => ('p,'a) proc"
                                      ("(1!<_> :_ .. /_)" [0,900,68] 68)
  where
  "!<f> :X .. Pf == ! :(f ` X) .. (%x. (Pf ((inv f) x)))"

syntax
  "@Rep_int_choice_f"::
      "('b => 'a) => pttrn => 'b set => ('p,'a) proc => ('p,'a) proc"
                                      ("(1!<_> _:_ .. /_)" [0,900,900,68] 68)
  "@Rep_int_choice_f_UNIV"::
      "('b => 'a) => pttrn => ('p,'a) proc => ('p,'a) proc"
                                      ("(1!<_> _ .. /_)" [900,900,68] 68)

translations
    "!<f> x:X .. P" == "!<f> :X .. (%x. P)"
    "!<f> x .. P"   == "!<f> x:(CONST UNIV) .. P"

lemmas Rep_int_choice_ss_def =
       Rep_int_choice_set_def
       Rep_int_choice_nat_def
       Rep_int_choice_com_def
       Rep_int_choice_f_def

(*** internal prefix choice ***)

(* 2013
consts
  Int_pre_choice :: "'a set => ('a => ('p,'a) proc) => ('p,'a) proc"  
                                      ("(1! :_ /-> _)" [900,80] 80)

defs
  Int_pre_choice_def : "! :X -> Pf == ! :X .. (%x. x -> (Pf x))"
*)

definition
  Int_pre_choice :: "'a set => ('a => ('p,'a) proc) => ('p,'a) proc"  
                                      ("(1! :_ /-> _)" [900,80] 80)
  where
  "! :X -> Pf == ! :X .. (%x. x -> (Pf x))"

syntax
  "@Int_pre_choice"  :: "pttrn => 'a set => ('p,'a) proc 
                         => ('p,'a) proc"  ("(1! _:_ /-> _)" [900,900,80] 80)

  "@Int_pre_choice_UNIV" ::  "pttrn => ('p,'a) proc => ('p,'a) proc"
                                           ("(1! _ /-> _)" [900,80] 80)

translations
  "! x:X -> P"  == "! :X -> (%x. P)"
  "! x -> P"    == "! x:(CONST UNIV) -> P"

(*** sending and receiving prefixes ***)

(* Isabelle 2013
consts
  Send_prefix :: "('x => 'a) => 'x => ('p,'a) proc => ('p,'a) proc" 
                                      ("(1_ ! _ /-> _)" [900,1000,80] 80)
  Nondet_send_prefix :: "('x => 'a) => 'x set => 
                         ('x => ('p,'a) proc) => ('p,'a) proc" 
  Rec_prefix  :: "('x => 'a) => 'x set => 
                  ('x => ('p,'a) proc) => ('p,'a) proc" 

defs
  Send_prefix_def : 
    "a ! x -> P    == a x -> P"
  Nondet_send_prefix_def : 
    "Nondet_send_prefix f X Pf == ! :(f ` X) -> (%x. (Pf ((inv f) x)))"
  Rec_prefix_def : 
    "Rec_prefix f X Pf == ? :(f ` X) -> (%x. (Pf ((inv f) x)))"
*)

definition
  Send_prefix :: "('x => 'a) => 'x => ('p,'a) proc => ('p,'a) proc" 
                                      ("(1_ ! _ /-> _)" [900,1000,80] 80)
  where
  "a ! x -> P    == a x -> P"

definition
  Nondet_send_prefix :: "('x => 'a) => 'x set => 
                         ('x => ('p,'a) proc) => ('p,'a) proc" 
  where
  "Nondet_send_prefix f X Pf == ! :(f ` X) -> (%x. (Pf ((inv f) x)))"

definition
  Rec_prefix  :: "('x => 'a) => 'x set => 
                  ('x => ('p,'a) proc) => ('p,'a) proc" 
  where
  "Rec_prefix f X Pf == ? :(f ` X) -> (%x. (Pf ((inv f) x)))"

(*
The sending "a ! v -> P" causes syntactical ambiguity.
So, it is recommended to directly use "a v -> P" instead of "a ! v -> P".
*)

syntax
  "@Nondet_send_prefix" :: 
     "('x => 'a) => pttrn => 'x set => ('p,'a) proc => ('p,'a) proc"
                               ("(1_ !? _:_ /-> _)" [900,900,1000,80] 80)

  "@Nondet_send_prefix_UNIV" :: 
     "('x => 'a) => pttrn => ('p,'a) proc => ('p,'a) proc"
                               ("(1_ !? _ /-> _)" [900,900,80] 80)

  "@Rec_prefix" :: 
     "('x => 'a) => pttrn => 'x set => ('p,'a) proc => ('p,'a) proc"
                               ("(1_ ? _:_ /-> _)" [900,900,1000,80] 80)
  "@Rec_Prefix_UNIV" :: 
     "('x => 'a) => pttrn => ('p,'a) proc => ('p,'a) proc"
                               ("(1_ ? _ /-> _)" [900,900,80] 80)

translations
  "a !? x:X -> P" == "CONST Nondet_send_prefix a X (%x. P)"
  "a !? x -> P"   == "a !? x:(CONST UNIV) -> P"

  "a ? x:X -> P"  == "CONST Rec_prefix a X (%x. P)"
  "a ? x -> P"    == "a? x:(CONST UNIV) -> P"

(*** unfolding syntactic sugar ***)

lemmas csp_prefix_ss_def = Int_pre_choice_def
                           Send_prefix_def
                           Nondet_send_prefix_def
                           Rec_prefix_def

(*** parallel ***)

abbreviation
   Interleave :: "('p,'a) proc => ('p,'a) proc
                    => ('p,'a) proc"  ("(1_ /||| _)" [76,77] 76)
where "P ||| Q == P |[{}]| Q"

abbreviation
   Synchro   :: "('p,'a) proc => ('p,'a) proc
                    => ('p,'a) proc"  ("(1_ /|| _)" [76,77] 76)
where "P || Q == P |[UNIV]| Q"

(*
syntax
  "_Interleave"    :: "('p,'a) proc => ('p,'a) proc
                    => ('p,'a) proc"  ("(1_ /||| _)" [76,77] 76)
  "_Synchro"       :: "('p,'a) proc => ('p,'a) proc
                    => ('p,'a) proc"  ("(1_ /|| _)" [76,77] 76)

translations
  "P ||| Q"     == "P |[{}]| Q"
  "P || Q"      == "P |[UNIV]| Q"
*)

(* Isabelle 2013
consts
  Alpha_parallel :: "('p,'a) proc => 'a set => 'a set => ('p,'a) proc
                      => ('p,'a) proc"  ("(1_ /(2|[_,/_]|)/ _)" [76,0,0,77] 76)
defs
  Alpha_parallel_def :
   "P |[X,Y]| Q  == (P |[- X]| SKIP) |[X Int Y]| (Q |[- Y]| SKIP)"
*)

definition
  Alpha_parallel :: "('p,'a) proc => 'a set => 'a set => ('p,'a) proc
                      => ('p,'a) proc"  ("(1_ /(2|[_,/_]|)/ _)" [76,0,0,77] 76)
  where
  "P |[X,Y]| Q  == (P |[- X]| SKIP) |[X Int Y]| (Q |[- Y]| SKIP)"

primrec
  Inductive_parallel :: "(('p,'a) proc * 'a set) list
                   => ('p,'a) proc"  ("(1[||] _)" [78] 78)
where
  "[||] [] = SKIP"
 |"[||] (PX # PXs) = (fst PX) |[snd PX, Union (snd ` set PXs)]| ([||] PXs)"

(* Isabelle 2013 
consts
  Rep_parallel :: "'i set => ('i => (('p,'a) proc * 'a set))
                      => ('p,'a) proc"  ("(1[||]:_ /_)" [90,78] 78)

defs
  Rep_parallel_def :
   "[||]:I PXf == [||] (map PXf (SOME Is. Is isListOf I))"
*)   

definition
  Rep_parallel :: "'i set => ('i => (('p,'a) proc * 'a set))
                      => ('p,'a) proc"  ("(1[||]:_ /_)" [90,78] 78)
  where
  Rep_parallel_def :
   "[||]:I PXf == [||] (map PXf (SOME Is. Is isListOf I))"

syntax
  "@Rep_parallel" :: 
     "pttrn => 'i set => (('p,'a) proc * 'a set)
                      => ('p,'a) proc"  ("(1[||] _:_ .. /_)" [900,90,78] 78)

translations
  "[||] i:I .. PX"  == "[||]:I (%i. PX)"

(************************************
 |           empty Index            |
 ************************************)

lemma Rep_parallel_empty[simp]: "I = {} ==> [||]:I PXf = SKIP"
by (simp add: Rep_parallel_def)

(************************************
 |            one Index             |
 ************************************)

lemma Rep_parallel_one: 
  "I = {i} ==> [||]:I PXf = (fst (PXf i)) |[snd (PXf i), {}]| SKIP"
by (simp add: Rep_parallel_def)


(*** Inductive interleave ***)

primrec
  Inductive_interleave :: "(('p,'a) proc) list \<Rightarrow> ('p,'a) proc" ("(1||| _)" [80] 80)
where
  "||| [] = SKIP"
 |"||| (P#Ps) = P ||| ( ||| Ps)"


(*** Replicated interleaving ***)

definition
  Rep_interleaving :: "'x set \<Rightarrow> ('x \<Rightarrow> ('p,'a) proc) \<Rightarrow> ('p,'a) proc" ("(1|||_ ..  _)" [900,80] 80)
  where
  Rep_interleaving_def :
  "|||X .. PXf == ||| [ PXf i . i <- (SOME x . x isListOf X) ]"


(*
datatype Events = a | b

lemma test : "[||] [ (a -> SKIP, {a}), (b -> SKIP, {b}) ] =F (a -> SKIP ||| b -> SKIP)"
  apply (simp add: Rep_interleaving_def)
*)


(* consts Rep_interleaving :: "'x set \<Rightarrow> ('x \<Rightarrow> ('p,'a) proc) \<Rightarrow> ('p,'a) proc" ("(1|||_ ..  _)" [900,80] 80)
defs Rep_interleaving_def : "Rep_interleaving X PXf == [||] [ (PXf i, eventsOf(PXf i )) . i <- (SOME x . x isListOf X) ]" *)

syntax
  "@Rep_interleaving" ::
    "pttrn => 'x set => ('p,'a) proc => ('p,'a) proc" ("(1||| _:_ .. /_)" [900,900,68] 68)
translations
  "||| x:X .. P" == "|||X .. (%x . P)"


(************************************
 |     Inductive_interleave_map     |
 ************************************)

lemma Inductive_interleave_map_to_List :
    "map PXf x = l \<Longrightarrow> ( ||| map PXf x) = ( ||| l)"
by (simp)

lemma Inductive_interleave_map_to_List_Cons :
    "l \<noteq> [] \<Longrightarrow> ||| map PXf l = ||| ( (PXf (hd l)) # map PXf (tl l) )"
by (rule Inductive_interleave_map_to_List, induct l, simp, simp add: map_def)


(*** timeout ***)

abbreviation
 Timeout_abb :: "('p,'a) proc => ('p,'a) proc 
             => ('p,'a) proc"  ("(1_ /[> _)" [73,74] 73)
 where "P [> Q == (P |~| STOP) [+] Q"

(*
syntax
  "_Timeout"  :: "('p,'a) proc => ('p,'a) proc 
               => ('p,'a) proc"  ("(1_ /[> _)" [73,74] 73)
translations
  "P [> Q"      == "(P |~| STOP) [+] Q"
*)

(*** it is sometimes useful to prevent automatic unfolding [> ***)

(* Isabelle 2013
consts
  Timeout  :: "('p,'a) proc => ('p,'a) proc 
               => ('p,'a) proc"  ("(1_ /[>def _)" [73,74] 73)
defs
  Timeout_def : "P [>def Q == P [> Q"
*)  

definition
  Timeout  :: "('p,'a) proc => ('p,'a) proc 
               => ('p,'a) proc"  ("(1_ /[>def _)" [73,74] 73)
  where
  Timeout_def : "P [>def Q == P [> Q"


(************************************
 |       Renaming by lists          |
 ************************************)

primrec
  Renaming_List  :: "('p,'a) proc => ('a * 'a) set list => ('p,'a) proc"
                                               ("(1_ /[[ _ ]]*)" [84,0] 84)
where
  "P [[ [] ]]* = P"
 |"P [[ r#rs ]]* = P[[r]] [[ rs ]]*"


(* --------------------------------------------------- *
             pipe operator (CSP-Prover 5)
 * --------------------------------------------------- *)

(* Isabelle 2013
consts
 Pipe :: "('p,'a) proc => 
          ('x => 'a) => ('x => 'a) => ('x => 'a) =>
          ('p,'a) proc => ('p,'a) proc"
          ("(1_ /<[_,_,_]> _)" [76,0,0,0,77] 76)

defs
 Pipe_def: 
   "P <[left,mid,right]> Q == 
   (P[[right<==>mid]] 
    |[range left Un range mid, range mid Un range right]| 
    Q[[left<==>mid]]) -- (range mid)"
*)

definition
 Pipe :: "('p,'a) proc => 
          ('x => 'a) => ('x => 'a) => ('x => 'a) =>
          ('p,'a) proc => ('p,'a) proc"
          ("(1_ /<[_,_,_]> _)" [76,0,0,0,77] 76)

  where
   "P <[left,mid,right]> Q == 
   (P[[right<==>mid]] 
    |[range left Un range mid, range mid Un range right]| 
    Q[[left<==>mid]]) -- (range mid)"

(*===================================================================*

(1) We assume that a process-name-function PNfun is given for 
    defining the meaning of each process-name.

    When you define a type of process names, you have to define
    the function PNfun by "overloaded" as follows:

      defs (overloaded)
      PNfun_test_def :  "PNfun == ..."

(2) There are two kinds of approahes for fixed points, i.e. 
    cms and cpo approaches. You can defin the mode for fixed 
    points by

      defs FPmode = CPOmode  
    or
      defs FPmode = CMSmode

    In addtion, you can use MIXmode as follows

      defs FPmode = CMSmode

    It means the least fixed point (in subset order) is used for
    giving the meaning of process names based on cpo approach, and if
    the process function is guarded then cms appoach is also used
    because the least fixed point is the unique fixed point in this
    case.

 *==================================================================*)

(* Isabelle 2013
consts PNfun :: "'p => ('p,'a) proc"  (* Definition of process names *)
*)

type_synonym ('p,'a) pnfun = "'p => ('p,'a) proc"
consts PNfun :: "('p,'a) pnfun"  (* Definition of process names *)

datatype fpmode = CPOmode | CMSmode | MIXmode
consts FPmode :: "fpmode"

(* overloading test:
overloading FP_CPOmode == 
  "FPmode :: fpmode"
begin
  definition "FPmode == CPOmode"
end

lemma "FPmode = CPOmode"
apply (simp add:FP_CPOmode_def)
done
*)

lemma CPOmode_or_CMSmode_or_MIXmode_lm: 
   "m = FPmode --> m = CPOmode | m = CMSmode | m = MIXmode"
apply (induct_tac m)
apply (auto)
done

lemma CPOmode_or_CMSmode_or_MIXmode: 
  "FPmode = CPOmode | FPmode = CMSmode | FPmode = MIXmode"
by (simp add: CPOmode_or_CMSmode_or_MIXmode_lm)

(*-------*
 | CHAOS |
 *-------*)

(* This CHAOS may cause some error on process definition ... ? *)

datatype 'a ChaosName = Chaos "'a set"

primrec
  Chaosfun :: "'a ChaosName => ('a ChaosName, 'a) proc"
where
  "Chaosfun   (Chaos A) = (! x:A -> $(Chaos A)) |~| STOP"

(* Isabelle 2013
defs (overloaded)
Set_Chaosfun_def [simp]: "PNfun == Chaosfun 
*)

overloading Set_Chaosfun == 
  "PNfun :: ('a ChaosName, 'a) pnfun"
begin
  definition "PNfun (pn::'a ChaosName) == Chaosfun pn"
end

(* test of overloading *)
lemma "((PNfun pn)::('a ChaosName, 'a) proc) = Chaosfun pn"
apply (simp add: Set_Chaosfun_def)
done

(* Isabelle 2013
consts CHAOS :: "'a set => ('a ChaosName, 'a) proc"
defs   CHAOS_def : "CHAOS == (%A. $(Chaos A))"
*)

definition
  CHAOS :: "'a set => ('a ChaosName, 'a) proc"
  where
  CHAOS_def : "CHAOS == (%A. $(Chaos A))"


(* --------------------------------------- *
     an example of recursive processes

datatype AB = A | B

consts ABfun :: "AB => (AB,nat) proc"

primrec
  "ABfun  A = 0 -> $B"
  "ABfun  B = 1 -> $A"

defs (overloaded)
PNfun_AB_def : "PNfun == ABfun"

 * --------------------------------------- *)

(*********************************************************************
            substitution by functions : 'p => ('a,'p) proc
 *********************************************************************)


primrec
  Subst_procfun :: "('p,'a) proc => ('p => ('q,'a) proc)
                   => ('q,'a) proc"  ("_ <<" [1000] 1000)
where
  "STOP<<Pf         = STOP"
 |"SKIP<<Pf         = SKIP"
 |"DIV<<Pf          = DIV"
 |"(a -> P)<<Pf     = a -> P<<Pf"
 |"(? :X -> Qf)<<Pf = ? a:X -> (Qf a)<<Pf"
 |"(P [+] Q)<<Pf    = P<<Pf [+] Q<<Pf"
 |"(P |~| Q)<<Pf    = P<<Pf |~| Q<<Pf"
 |"(!! :C .. Qf)<<Pf = !! c:C .. (Qf c)<<Pf"
 |"(IF b THEN P ELSE Q)<<Pf = IF b THEN P<<Pf ELSE Q<<Pf"
 |"(P |[X]| Q)<<Pf  = P<<Pf |[X]| Q<<Pf"
 |"(P -- X)<<Pf     = P<<Pf -- X"
 |"(P [[r]])<<Pf    = P<<Pf [[r]]"
 |"(P ;; Q)<<Pf     = P<<Pf ;; Q<<Pf"
 |"(P |. n)<<Pf     = P<<Pf |. n"
 |"($p) <<Pf        = Pf p"

 (* Isabelle 2013
consts
  Subst_procfun_prod :: 
     "('p => ('q,'a) proc) => 
      ('q => ('r,'a) proc) => ('p => ('r,'a) proc)"
                                     ("_ <<<" [1000] 1000)
defs
  Subst_procfun_prod_def: "Pf <<< == (%Qf p. (Pf p)<<Qf)"
*)

definition
  Subst_procfun_prod :: 
     "('p => ('q,'a) proc) => 
      ('q => ('r,'a) proc) => ('p => ('r,'a) proc)"
                                     ("_ <<<" [1000] 1000)
  where
  "Pf <<< == (%Qf p. (Pf p)<<Qf)"


(*** Mapping procfun ***)

definition isMapping_procfun :: "('p \<Rightarrow> ('q,'e) proc) \<Rightarrow> bool"
where
  "isMapping_procfun Pf \<equiv> \<forall> x. \<exists>y . Pf(x) = $y"

(* lemmas *)

lemma Subst_procfun_Rep_int_choice_set[simp]:
  "(!set :Xs .. Qf)<<Pf      = !set X:Xs .. (Qf X)<<Pf"
by (simp add: Rep_int_choice_ss_def)

lemma Subst_procfun_Rep_int_choice_nat[simp]:
  "(!nat :N .. Qf)<<Pf      = !nat n:N .. (Qf n)<<Pf"
by (simp add: Rep_int_choice_ss_def)

lemma Subst_procfun_Rep_int_choice_com[simp]:
  "(! :X .. Qf)<<Pf      = ! x:X .. (Qf x)<<Pf"
by (simp add: Rep_int_choice_com_def)

lemma Subst_procfun_Rep_int_choice_f[simp]:
  "(!<f> :X .. Qf)<<Pf      = !<f> x:X .. (Qf x)<<Pf"
by (simp add: Rep_int_choice_f_def)

lemma Subst_procfun_prod_p:
  "(Pf <<< Qf) p = (Pf p) << Qf"
by (simp add: Subst_procfun_prod_def)

lemma Subst_procfun_Inductive_interleave_map :
   "\<forall> i \<in> set l. (PXf i) << Pf = PXf i
    \<Longrightarrow> ( ||| map PXf l) << Pf = ( ||| map PXf l)"
by (induct l, simp_all add: Subst_procfun_def)


(* for sending and receiving *)

lemma Subst_procfun_Send_prefix[simp]:
  "(a ! v -> P)<<Pf      = a ! v -> P<<Pf"
by (simp add: csp_prefix_ss_def)

lemma Subst_procfun_Rec_prefix[simp]:
  "(a ? x:X -> Pf x)<<Qf      = a ? x:X ->(Pf x)<<Qf"
by (simp add: csp_prefix_ss_def)

lemma Subst_procfun_Int_pre_choice[simp]:
  "(! :X -> Pf)<<Qf      = ! x:X -> (Pf x)<<Qf"
by (simp add: csp_prefix_ss_def)

lemma Subst_procfun_Nondet_send_prefix[simp]:
  "(a !? x:X -> Pf x)<<Qf      = a !? x:X ->(Pf x)<<Qf"
by (simp add: csp_prefix_ss_def)

(* subst *)

lemma Subst_procfun_Alpha_parallel[simp]: (* <- added for Alpha_parallel *)
  "(P |[X,Y]| Q)<<Pf = (P<<Pf) |[X,Y]| (Q<<Pf)"
by (simp add: Alpha_parallel_def)

lemma Subst_procfun_Pipe[simp]:
  "(P <[left,mid,right]> Q)<<Pf = (P<<Pf) <[left,mid,right]> (Q<<Pf)"
by (simp add: Pipe_def)


(*************************************************************
                   Syntactical functions
 *************************************************************)

(*** guarded fun) ***)

(*** noPN ***)

primrec
  noPN   :: "('p,'a) proc => bool"   (* no Proc_name *)
where
  "noPN STOP          = True"
 |"noPN SKIP          = True"
 |"noPN DIV           = True"
 |"noPN (a -> P)      = noPN P"
 |"noPN (? :X -> Pf)  = (ALL a. noPN (Pf a))"
 |"noPN (P [+] Q)     = (noPN P & noPN Q)"
 |"noPN (P |~| Q)     = (noPN P & noPN Q)"
 |"noPN (!! :C .. Pf) = (ALL c. noPN (Pf c))"
 |"noPN (IF b THEN P ELSE Q) = (noPN P & noPN Q)"
 |"noPN (P |[X]| Q)   = (noPN P & noPN Q)"
 |"noPN (P -- X)      = noPN P"
 |"noPN (P [[r]])     = noPN P"
 |"noPN (P ;; Q)      = (noPN P & noPN Q)"
 |"noPN (P |. n)      = noPN P"
 |"noPN ($p)          = False"

(*** gSKIP ***)

primrec
  gSKIP  :: "('p,'a) proc => bool"   (* guarded SKIP *)
where
  "gSKIP STOP          = True"
 |"gSKIP SKIP          = False"
 |"gSKIP DIV           = True"
 |"gSKIP (a -> P)      = True"
 |"gSKIP (? :X -> Pf)  = True"
 |"gSKIP (P [+] Q)     = (gSKIP P & gSKIP Q)"
 |"gSKIP (P |~| Q)     = (gSKIP P & gSKIP Q)"
 |"gSKIP (!! :C .. Pf) = (ALL c. gSKIP (Pf c))"
 |"gSKIP (IF b THEN P ELSE Q) = (gSKIP P & gSKIP Q)"
 |"gSKIP (P |[X]| Q)   = (gSKIP P | gSKIP Q)"
 |"gSKIP (P -- X)      = False"
 |"gSKIP (P [[r]])     = gSKIP P"
 |"gSKIP (P ;; Q)      = (gSKIP P | gSKIP Q)"
 |"gSKIP (P |. n)      = (gSKIP P | n=0)"
 |"gSKIP ($p)          = False"

(*** no hide ***)

primrec
  noHide :: "('p,'a) proc => bool"   (* no Hide      *)
where
  "noHide STOP          = True"
 |"noHide SKIP          = True"
 |"noHide DIV           = True"
 |"noHide (a -> P)      = noHide P"
 |"noHide (? :X -> Pf)  = (ALL a. noHide (Pf a))"
 |"noHide (P [+] Q)     = (noHide P & noHide Q)"
 |"noHide (P |~| Q)     = (noHide P & noHide Q)"
 |"noHide (!! :C .. Pf) = (ALL c. noHide (Pf c))"
 |"noHide (IF b THEN P ELSE Q) = (noHide P & noHide Q)"
 |"noHide (P |[X]| Q)   = (noHide P & noHide Q)"
 |"noHide (P -- X)      = noPN P"
 |"noHide (P [[r]])     = noHide P"
 |"noHide (P ;; Q)      = (noHide P & noHide Q)"
 |"noHide (P |. n)      = (noHide P | n=0)"
 |"noHide ($p)          = True"

(*** guarded ***)

primrec
  guarded:: "('p,'a) proc => bool"   (* guarded proc *)
where
  "guarded STOP          = True"
 |"guarded SKIP          = True"
 |"guarded DIV           = True"
 |"guarded (a -> P)      = noHide P"
 |"guarded (? :X -> Pf)  = (ALL a. noHide (Pf a))"
 |"guarded (P [+] Q)     = (guarded P & guarded Q)"
 |"guarded (P |~| Q)     = (guarded P & guarded Q)"
 |"guarded (!! :C .. Pf) = (ALL c. guarded (Pf c))"
 |"guarded (IF b THEN P ELSE Q) = (guarded P & guarded Q)"
 |"guarded (P |[X]| Q)   = (guarded P & guarded Q)"
 |"guarded (P -- X)      = noPN P"
 |"guarded (P [[r]])     = guarded P"
 |"guarded (P ;; Q)      = ((guarded P & gSKIP P & noHide Q) | 
                           (guarded P & guarded Q))"
 |"guarded (P |. n)      = (guarded P | n=0)"
 |"guarded ($p)          = False"

(*** for process function ***)

(*
consts
  noPNfun   :: "('p => ('q,'a) proc) => bool"
  gSKIPfun  :: "('p => ('q,'a) proc) => bool"
  noHidefun :: "('p => ('q,'a) proc) => bool"
  guardedfun:: "('p => ('q,'a) proc) => bool"

defs
  noPNfun_def   : "noPNfun Pf    == (ALL p. noPN (Pf p))"
  gSKIPfun_def  : "gSKIPfun Pf   == (ALL p. gSKIP (Pf p))"
  noHidefun_def : "noHidefun Pf  == (ALL p. noHide (Pf p))"
  guardedfun_def: "guardedfun Pf == (ALL p. guarded (Pf p))"
*)

definition
  noPNfun   :: "('p => ('q,'a) proc) => bool"
  where 
  "noPNfun Pf    == (ALL p. noPN (Pf p))"

definition
  gSKIPfun  :: "('p => ('q,'a) proc) => bool"
  where
  "gSKIPfun Pf   == (ALL p. gSKIP (Pf p))"

definition
  noHidefun :: "('p => ('q,'a) proc) => bool"
  where
  "noHidefun Pf  == (ALL p. noHide (Pf p))"

definition
  guardedfun:: "('p => ('q,'a) proc) => bool"
  where
  "guardedfun Pf == (ALL p. guarded (Pf p))"

  (****** short notations ******)

(* noPN *)

lemma noPN_Rep_ext_choice [rule_format]:
    "\<lbrakk> finite X; \<And>x. noPN (PXf x) \<rbrakk> \<Longrightarrow> noPN ([+]X .. PXf)"
  apply (simp add: Rep_ext_choice_def)
    apply (rule someI2_ex, rule isListOf_EX, simp)
by (induct_tac x, simp_all add: Inductive_ext_choice_def)

lemma noPN_Rep_int_choice_set[simp]:
  "noPN (!set :Xs .. Pf) = (ALL X. noPN (Pf X))"
by (simp add: Rep_int_choice_ss_def)

lemma noPN_Rep_int_choice_nat[simp]:
  "noPN (!nat :N .. Pf) = (ALL n. noPN (Pf n))"
by (simp add: Rep_int_choice_ss_def)

lemma noPN_Rep_int_choice_com[simp]:
  "noPN (! :X .. Pf) = (ALL a. noPN (Pf a))"
apply (auto simp add: Rep_int_choice_com_def)
apply (drule_tac x="{a}" in spec)
apply (simp)
done

lemma noPN_Rep_int_choice_f[simp]:
  "[| inj f ; ALL a. noPN (Pf a) |] ==> noPN (!<f> :X .. Pf)"
by (simp add: Rep_int_choice_f_def)

lemma noPN_Alpha_parallel[simp]:
  "noPN (P |[X,Y]| Q) = (noPN P & noPN Q)"
by (simp add: Alpha_parallel_def)

lemma noPN_Inductive_interleaving :
    "\<lbrakk> noPN(P); noPN( ||| Ps) \<rbrakk> \<Longrightarrow> noPN( ||| (P#Ps))"
by (induct P, simp_all)

lemma noPN_Inductive_interleave_map :
    "\<lbrakk> \<forall> aa \<in> set list . noPN(Pf aa) \<rbrakk> \<Longrightarrow> noPN ( ||| map Pf list)"
by (induct list, simp_all)

lemma noPN_Rep_interleaving :
    "\<lbrakk>  finite X; \<forall> aa \<in> X . noPN(PfX aa) \<rbrakk> \<Longrightarrow> noPN ( ||| x:X .. PfX x)"
  apply (simp add: Rep_interleaving_def)
  apply (rule someI2_ex, rule isListOf_EX, simp add: isListOf_set_eq)
  apply (rule noPN_Inductive_interleave_map)
by (simp add: isListOf_set_eq)

(* gSKIP *)

lemma gSKIP_Rep_int_choice_set[simp]:
  "gSKIP (!set :Xs .. Pf) = (ALL X. gSKIP (Pf X))"
by (simp add: Rep_int_choice_ss_def)

lemma gSKIP_Rep_int_choice_nat[simp]:
  "gSKIP (!nat :N .. Pf) = (ALL n. gSKIP (Pf n))"
by (simp add: Rep_int_choice_ss_def)

lemma gSKIP_Rep_int_choice_com[simp]:
  "gSKIP (! :X .. Pf) = (ALL a. gSKIP (Pf a))"
apply (auto simp add: Rep_int_choice_com_def)
apply (drule_tac x="{a}" in spec)
apply (simp)
done

lemma gSKIP_Rep_int_choice_f[simp]:
  "[| inj f ; ALL a. gSKIP (Pf a) |] ==> gSKIP (!<f> :X .. Pf)"
by (simp add: Rep_int_choice_f_def)

lemma gSKIP_Alpha_parallel[simp]:
  "gSKIP (P |[X,Y]| Q) = (gSKIP P | gSKIP Q)"
by (simp add: Alpha_parallel_def)

lemma gSKIP_Inductive_interleave_map :
    "\<lbrakk> list \<noteq> []; \<forall> aa\<in> set list . gSKIP(Pf aa) \<rbrakk> \<Longrightarrow> gSKIP ( ||| map Pf list)"
by (induct list, simp_all)

lemma gSKIP_Rep_interleaving :
    "X \<noteq> {} \<Longrightarrow> finite X \<Longrightarrow> \<forall> x \<in> X . gSKIP (PfX x) \<Longrightarrow> gSKIP ( ||| x:X .. PfX x )"
  apply (simp add: Rep_interleaving_def)
  apply (rule someI2_ex, rule isListOf_EX, simp)
  apply (rule gSKIP_Inductive_interleave_map)
    apply (clarsimp)
    apply (simp add: isListOf_set_eq)
done

(* noHide *)

lemma noHide_Rep_ext_choice :
    "\<lbrakk> finite X; \<And>x. noHide (PXf x) \<rbrakk> \<Longrightarrow> noHide ([+]X .. PXf)"
  apply (simp add: Rep_ext_choice_def)
    apply (rule someI2_ex, rule isListOf_EX, simp)
    apply (induct_tac x, simp_all add: Inductive_ext_choice_def)
done

lemma noHide_Rep_int_choice_set[simp]:
  "noHide (!set :Xs .. Pf) = (ALL X. noHide (Pf X))"
by (simp add: Rep_int_choice_ss_def)

lemma noHide_Rep_int_choice_nat[simp]:
  "noHide (!nat :N .. Pf) = (ALL n. noHide (Pf n))"
by (simp add: Rep_int_choice_ss_def)

lemma noHide_Rep_int_choice_com[simp]:
  "noHide (! :X .. Pf) = (ALL a. noHide (Pf a))"
apply (auto simp add: Rep_int_choice_com_def)
apply (drule_tac x="{a}" in spec)
apply (simp)
done

lemma noHide_Rep_int_choice_f[simp]:
  "[| inj f ; ALL a. noHide (Pf a) |]
   ==> noHide (!<f> :X .. Pf)"
by (simp add: Rep_int_choice_f_def)

lemma noHide_Alpha_parallel[simp]:
  "noHide (P |[X,Y]| Q) = (noHide P & noHide Q)"
by (simp add: Alpha_parallel_def)

lemma noHide_Rep_parallel_Nil [simp]:
    "noHide ([||] map PXf [])"
by (auto)

lemma noHide_Rep_parallel [simp]:
    "\<lbrakk> \<forall> aa . noHide(fst(PXf aa)) \<rbrakk> \<Longrightarrow> noHide ([||] map PXf list)"
by (induct_tac list, simp, simp)

lemma noHide_Inductive_parallel_Nil [simp]:
    "noHide([||] [])"
by (simp)

lemma noHide_Inductive_parallel [simp]:
    "\<lbrakk> noHide(fst(PX)); \<And> p . p \<in> (fst ` (set PXs)) \<and> noHide(p) \<rbrakk> \<Longrightarrow>  noHide([||] (PX # PXs))"
by (induct "PXs", simp, simp)

lemma noHide_Inductive_interleaving_Nil :
    "noHide( ||| [])"
by (simp)

lemma noHide_Inductive_interleaving_Cons :
    "\<lbrakk> noHide(P); \<And> p . p \<in> (set Ps) \<and> noHide(p) \<rbrakk> \<Longrightarrow>  noHide( ||| (P # Ps))"
by (induct "Ps", simp, simp)

lemma noHide_Inductive_interleaving_Cons2 :
    "\<lbrakk> noHide(P); noHide( ||| Ps) \<rbrakk> \<Longrightarrow> noHide ( ||| (P#Ps))"
by (simp only: Inductive_interleave_def, simp)

lemmas noHide_Inductive_interleaving =
    noHide_Inductive_interleaving_Nil
    noHide_Inductive_interleaving_Cons
    noHide_Inductive_interleaving_Cons2

lemma noHide_Inductive_interleave_map :
    "\<lbrakk> \<forall> aa \<in> set list . noHide(Pf aa) \<rbrakk> \<Longrightarrow> noHide ( ||| map Pf list)"
by (induct list, simp_all)

lemma noHide_Inductive_interleave_map_cons :
    "\<lbrakk> noHide(PXf x); noHide ( ||| map PXf xs) \<rbrakk> \<Longrightarrow> noHide ( ||| map PXf (x#xs))"
by (simp)

lemma noHide_Rep_interleaving :
    "\<lbrakk>  finite X; \<forall> aa \<in> X . noHide(PfX aa) \<rbrakk> \<Longrightarrow> noHide ( ||| x:X .. PfX x)"
  apply (simp add: Rep_interleaving_def)
  apply (rule someI2_ex, rule isListOf_EX, simp add: isListOf_set_eq)
  apply (rule noHide_Inductive_interleave_map)
    apply (simp add: isListOf_set_eq)
done

(* guarded *)

lemma guarded_Rep_ext_choice :
    "\<lbrakk> finite X; \<And>x. guarded (PXf x) \<rbrakk> \<Longrightarrow> guarded ([+]X .. PXf)"
  apply (simp add: Rep_ext_choice_def)
    apply (rule someI2_ex, rule isListOf_EX, simp)
    apply (induct_tac x, simp_all add: Inductive_ext_choice_def)
done

lemma Rep_ext_choice_map_to_List :
    "map PXf x = l \<Longrightarrow> ( [+] map PXf x) = ( [+] l)"
by (simp)

lemma Rep_ext_choice_map_to_List_Cons :
    "l \<noteq> [] \<Longrightarrow> [+] map PXf l = [+] ( (PXf (hd l)) # map PXf (tl l) )"
by (induct l, simp_all)

lemma guarded_Rep_int_choice_set[simp]:
  "guarded (!set :Xs .. Pf) = (ALL X. guarded (Pf X))"
by (simp add: Rep_int_choice_ss_def)

lemma guarded_Rep_int_choice_nat[simp]:
  "guarded (!nat :N .. Pf) = (ALL n. guarded (Pf n))"
by (simp add: Rep_int_choice_ss_def)

lemma guarded_Rep_int_choice_com[simp]:
  "guarded (! :X .. Pf) = (ALL a. guarded (Pf a))"
apply (auto simp add: Rep_int_choice_com_def)
apply (drule_tac x="{a}" in spec)
apply (simp)
done

lemma guarded_Rep_int_choice_f[simp]:
  "[| inj f ; ALL a. guarded (Pf a) |] 
   ==> guarded (!<f> :X .. Pf)"
by (simp add: Rep_int_choice_f_def)

lemma guarded_Alpha_parallel[simp]:
  "guarded (P |[X,Y]| Q) = (guarded P & guarded Q)"
by (simp add: Alpha_parallel_def)

lemma guarded_Rep_parallel_Nil [simp]:
    "guarded ([||] map PXf [])"
by (auto)

lemma guarded_Rep_parallel [simp]:
    "\<lbrakk> \<forall> aa . guarded(fst(PXf aa)) \<rbrakk> \<Longrightarrow> guarded ([||] map PXf list)"
  apply (induct_tac list)
  apply (simp)
  apply (simp)
done

lemma guarded_Inductive_interleave_map :
    "\<lbrakk> \<forall> aa\<in> set list . guarded(Pf aa) \<rbrakk> \<Longrightarrow> guarded ( ||| map Pf list)"
by (induct list, simp_all)

lemma guarded_Rep_interleaving :
    "finite X \<Longrightarrow> \<forall> x \<in> X . guarded (PfX x) \<Longrightarrow> guarded ( ||| x:X .. PfX x )"
  apply (simp add: Rep_interleaving_def)
  apply (rule someI2_ex, rule isListOf_EX, simp)
  apply (rule guarded_Inductive_interleave_map, simp add: isListOf_set_eq)
done

(* --------- for sending and receiving --------- *)

(* noPN *)

lemma noPN_Send_prefix[simp]:
  "noPN (a ! v -> P) = noPN(P)"
by (simp add: csp_prefix_ss_def)

lemma noPN_Rec_prefix[simp]:
  "noPN (a ? x:X -> Pf x) = (ALL x. noPN(Pf (inv a x)))"
by (simp add: csp_prefix_ss_def)

lemma noPN_Int_pre_choice[simp]:
  "noPN (! :X -> Pf) = (ALL x. noPN(Pf x))"
by (simp add: csp_prefix_ss_def)

lemma noPN__Nondet_send_prefix[simp]:
  "noPN (a !? x:X -> Pf x) = (ALL x. noPN(Pf (inv a x)))"
by (simp add: csp_prefix_ss_def)

(* gSKIP *)

lemma gSKIP_Send_prefix[simp]:
  "gSKIP (a ! v -> P)"
by (simp add: csp_prefix_ss_def)

lemma gSKIP_Rec_prefix[simp]:
  "gSKIP (a ? x:X -> Pf x)"
by (simp add: csp_prefix_ss_def)

lemma gSKIP_Int_pre_choice[simp]:
  "gSKIP (! :X -> Pf)"
by (simp add: csp_prefix_ss_def)

lemma gSKIP__Nondet_send_prefix[simp]:
  "gSKIP (a !? x:X -> Pf x)"
by (simp add: csp_prefix_ss_def)

(* noHide *)

lemma noHide_Send_prefix[simp]:
  "noHide (a ! v -> P) = noHide(P)"
by (simp add: csp_prefix_ss_def)

lemma noHide_Rec_prefix[simp]:
  "noHide (a ? x:X -> Pf x) = (ALL x. noHide(Pf (inv a x)))"
by (simp add: csp_prefix_ss_def)

lemma noHide_Int_pre_choice[simp]:
  "noHide (! :X -> Pf) = (ALL x. noHide(Pf x))"
by (simp add: csp_prefix_ss_def)

lemma noHide__Nondet_send_prefix[simp]:
  "noHide (a !? x:X -> Pf x) = (ALL x. noHide(Pf (inv a x)))"
by (simp add: csp_prefix_ss_def)

(* guarded *)

lemma guarded_Send_prefix[simp]:
  "guarded (a ! v -> P) = noHide(P)"
by (simp add: csp_prefix_ss_def)

lemma guarded_Rec_prefix[simp]:
  "guarded (a ? x:X -> Pf x) = (ALL x. noHide(Pf (inv a x)))"
by (simp add: csp_prefix_ss_def)

lemma guarded_Int_pre_choice[simp]:
  "guarded (! :X -> Pf) = (ALL x. noHide(Pf x))"
by (simp add: csp_prefix_ss_def)

lemma guarded__Nondet_send_prefix[simp]:
  "guarded (a !? x:X -> Pf x) = (ALL x. noHide(Pf (inv a x)))"
by (simp add: csp_prefix_ss_def)

(* --------- for pipe --------- *)

(* noPN *)

lemma noPN_Pipe[simp]:
  "noPN (P <[left,mid,right]> Q) = ((noPN P) & (noPN Q))"
by (simp add: Pipe_def)

(* gSKIP *)

lemma gSKIP_Pipe[simp]:
  "gSKIP (P <[left,mid,right]> Q) = False"
by (simp add: Pipe_def)

(* noHide *)

lemma noHide_Pipe[simp]:
  "noHide (P <[left,mid,right]> Q) = (noPN P & noPN Q)"
by (simp add: Pipe_def)

(* guarded *)

lemma guarded_Pipe[simp]:
  "guarded (P <[left,mid,right]> Q) = (noPN P & noPN Q)"
by (simp add: Pipe_def)

(*-----------------------------------------------------*
 |                   Substitution                      |
 *-----------------------------------------------------*)

lemma noPN_Subst_lm: "noPN P --> noPN (P<<Pf)"
apply (induct_tac P)
apply (simp_all)
done

lemma noPN_Subst: "noPN P ==> noPN (P<<Pf)"
by (simp add: noPN_Subst_lm)

lemma noPN_Subst_Pf: "noPNfun Pf ==> noPN (P<<Pf)"
apply (induct_tac P)
apply (simp_all)
apply (simp add: noPNfun_def)
done

lemma noHide_Mapping_procfun [simp]:
    "isMapping_procfun Pf \<Longrightarrow> noHide(Pf x)"
by (simp add: isMapping_procfun_def, erule_tac x="x" in allE, erule exE, simp)

lemma noHidefun_Mapping_procfun_lm : "isMapping_procfun Pf --> noHidefun Pf"
by (simp add: isMapping_procfun_def noHidefun_def)

lemma noHidefun_isMapping_procfun : "isMapping_procfun Pf ==> noHidefun Pf"
by (simp add: isMapping_procfun_def noHidefun_def)

lemma noHide_Subst_lm: "(noHide P & noHidefun Pf) --> noHide (P<<Pf)"
apply (induct_tac P)
apply (simp_all)
apply (simp add: noPN_Subst)
apply (force)
apply (simp add: noHidefun_def)
done

lemma noHide_Subst: "[| noHide P ; noHidefun Pf |] ==> noHide (P<<Pf)"
by (simp add: noHide_Subst_lm)

lemma noHide_Subst_procfun_pn :
    "P = $x \<and> Pf(x) = y \<and> noHide(y) \<Longrightarrow> noHide (P << Pf)"
by (simp)

lemma noHide_Subst_procfun_Inductive_interleave :
    "\<forall>a. noHide ((PXf a) << Pf) \<Longrightarrow> noHide (( ||| map PXf x) << Pf)"
by (induct_tac x, simp_all)

lemma gSKIP_Subst_lm: "(gSKIP P) --> gSKIP (P<<Pf)"
apply (induct_tac P)
apply (simp_all)
done

lemma gSKIP_Subst: "(gSKIP P) ==> gSKIP (P<<Pf)"
by (simp add: gSKIP_Subst_lm)

lemma guarded_Subst_lm: "(guarded P & noHidefun Pf) --> guarded (P<<Pf)"
apply (induct_tac P)
apply (simp_all)
apply (simp add: noHide_Subst)
apply (intro allI impI)
apply (simp add: noHide_Subst)
apply (simp add: noPN_Subst)
apply (intro allI impI)
apply (elim conjE exE disjE)
apply (simp add: gSKIP_Subst noHide_Subst)
apply (simp)
apply (force)
done

lemma guarded_Subst: "[| guarded P ; noHidefun Pf |] ==> guarded (P<<Pf)"
by (simp add: guarded_Subst_lm)

lemma guarded_Subst_procfun :
    "(\<exists> s Q . P = (Q -- s) \<and> noHide(Q << Pf) \<and> noPN(Q << Pf)) \<Longrightarrow> guarded (P << Pf)"
by (induct P, simp_all)

lemma not_guarded_Mapping_procfun :
    "isMapping_procfun Pf \<Longrightarrow> \<not> guarded (Pf x)"
  apply (simp add: isMapping_procfun_def)
  apply (erule_tac x="x" in allE, erule exE, simp)
done

lemma guarded_Mapping_procfun :
    "(guarded(P) \<or> noPN(P)) \<and> noHide(P) \<and> isMapping_procfun Pf \<Longrightarrow> guarded (P << Pf)"
  apply (induction P, simp_all)
  apply (rule noHide_Subst, simp, simp add: noHidefun_isMapping_procfun)
  apply (rule)
  apply (rule noHide_Subst, simp, simp add: noHidefun_isMapping_procfun)
  apply (clarify)
  apply (erule disjE)
  apply (rule, safe)
  apply (simp_all add: isMapping_procfun_def)
  apply (rule noPN_Subst, simp, rule gSKIP_Subst, simp)
  apply (rule noHide_Subst, simp)
  apply (simp add: noHidefun_isMapping_procfun isMapping_procfun_def)
done

lemma guarded_Subst_procfun_Rep_ext_choice :
    "\<forall>a. guarded ((PXf a) << Pf) \<Longrightarrow> guarded (( [+] map PXf x) << Pf)"
by (induct_tac x, simp_all)

lemma guarded_Subst_procfun_Inductive_interleave :
    "\<forall>a. guarded ((PXf a) << Pf) \<Longrightarrow> guarded (( ||| map PXf x) << Pf)"
by (induct_tac x, simp_all)

(*********************************************************
             termination relation for proc
 *********************************************************)

(* Isabelle 2005
consts
  procterm :: "(('p,'a) proc * ('p,'a) proc) set"

inductive procterm
intros
  "(P, a -> P)             : procterm"
  "(Pf a, ? :X -> Pf)      : procterm"
  "(P, P [+] Q)            : procterm"
  "(Q, P [+] Q)            : procterm"
  "(P, P |~| Q)            : procterm"
  "(Q, P |~| Q)            : procterm"
  "(Pf c, !! :C .. Pf)     : procterm"
  "(P, IF b THEN P ELSE Q) : procterm"
  "(Q, IF b THEN P ELSE Q) : procterm"
  "(P, P |[X]| Q)          : procterm"
  "(Q, P |[X]| Q)          : procterm"
  "(P, P -- X)             : procterm"
  "(P, P [[r]])            : procterm"
  "(P, P ;; Q)             : procterm"
  "(Q, P ;; Q)             : procterm"
  "(P, P |. n)             : procterm"
*)

inductive_set
  procterm :: "(('p,'a) proc * ('p,'a) proc) set"
where
  "(P, a -> P)             : procterm" |
  "(Pf a, ? :X -> Pf)      : procterm" |
  "(P, P [+] Q)            : procterm" |
  "(Q, P [+] Q)            : procterm" |
  "(P, P |~| Q)            : procterm" |
  "(Q, P |~| Q)            : procterm" |
  "(Pf c, !! :C .. Pf)     : procterm" |
  "(P, IF b THEN P ELSE Q) : procterm" |
  "(Q, IF b THEN P ELSE Q) : procterm" |
  "(P, P |[X]| Q)          : procterm" |
  "(Q, P |[X]| Q)          : procterm" |
  "(P, P -- X)             : procterm" |
  "(P, P [[r]])            : procterm" |
  "(P, P ;; Q)             : procterm" |
  "(Q, P ;; Q)             : procterm" |
  "(P, P |. n)             : procterm"

lemma wf_procterm: "wf procterm"
  apply (unfold wf_def)
  apply (intro strip)
  apply (induct_tac x)

  apply (erule allE, erule mp, intro strip,
         erule procterm.cases,
         simp, simp, simp, simp, simp, simp,
         simp, simp, simp, simp, simp, simp,
         simp, simp, simp, simp)+
done

(* procterm.elims in Isabelle 2005 
   -->  procterm.cases in Isabelle 2007 *)

(*-------------------------------------------------------* 
 |                                                       |
 |      decompostion controlled by Not_Decompo_Flag      |
 |                                                       |
 *-------------------------------------------------------*)
(* Isabelle 2013
consts Not_Decompo_Flag :: bool
defs   Not_Decompo_Flag_def : "Not_Decompo_Flag == True"
*)

definition
  Not_Decompo_Flag :: bool
  where
  Not_Decompo_Flag_def : "Not_Decompo_Flag == True"

lemma on_Not_Decompo_Flag: "Not_Decompo_Flag & R ==> R"
by (simp)

lemma off_Not_Decompo_Flag: "R ==> Not_Decompo_Flag & R"
by (simp add: Not_Decompo_Flag_def)

lemma off_Not_Decompo_Flag_True: "Not_Decompo_Flag"
by (simp add: Not_Decompo_Flag_def)

(*
ML_setup {*
    val ON_Not_Decompo_Flag       = thms "on_Not_Decompo_Flag";
    val OFF_Not_Decompo_Flag      = thms "off_Not_Decompo_Flag";
    val OFF_Not_Decompo_Flag_True = thms "off_Not_Decompo_Flag_True";
*}
for Isabelle 2007
*)

ML \<open>
    val ON_Not_Decompo_Flag       = @{thms on_Not_Decompo_Flag};
    val OFF_Not_Decompo_Flag      = @{thms off_Not_Decompo_Flag};
    val OFF_Not_Decompo_Flag_True = @{thms off_Not_Decompo_Flag_True};
\<close>

(*-------------------------------------------------------* 
 |                                                       |
 |        rewriting controlled by Not_Rewrite_Flag       |
 |                      CSP-Prover 5                     |
 *-------------------------------------------------------*)
(* Isabelle 2013
consts Not_Rewrite_Flag :: bool
defs   Not_Rewrite_Flag_def : "Not_Rewrite_Flag == True"
*)

definition
  Not_Rewrite_Flag :: bool
  where
  "Not_Rewrite_Flag == True"

lemma on_Not_Rewrite_Flag: "Not_Rewrite_Flag & R ==> R"
by (simp)

lemma off_Not_Rewrite_Flag: "R ==> Not_Rewrite_Flag & R"
by (simp add: Not_Rewrite_Flag_def)

lemma off_Not_Rewrite_Flag_True: "Not_Rewrite_Flag"
by (simp add: Not_Rewrite_Flag_def)

lemmas off_All_Flag_True = off_Not_Decompo_Flag_True
                           off_Not_Rewrite_Flag_True

ML \<open>
    val ON_Not_Rewrite_Flag       = @{thms on_Not_Rewrite_Flag};
    val OFF_Not_Rewrite_Flag      = @{thms off_Not_Rewrite_Flag};
    val OFF_Not_Rewrite_Flag_True = @{thms off_Not_Rewrite_Flag_True};
    val OFF_All_Flag_True         = @{thms off_All_Flag_True};
\<close>

(* 0 *)
(****************** to add them again ******************)
(*
declare Union_image_eq [simp]
declare Inter_image_eq [simp]
*)
end
