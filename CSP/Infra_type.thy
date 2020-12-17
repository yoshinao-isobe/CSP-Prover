           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   June 2005  (modified)   |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Infra_type
imports Infra_fun
begin

(*****************************************************
              Infinite Sequence type
 *****************************************************)

(* types 'a infinite_seq = "nat => 'a"   isabelle 2011   *)     (* synonym *)

type_synonym 'a infinite_seq = "nat => 'a"           (* synonym *)

(********************************************************** 
                      two types
 **********************************************************)

datatype
  ('a,'b) sum
   = type1 "'a"
   | type2 "'b"

(* lemmas *)

lemma inj_type1[simp]: "inj type1"
by (simp add: inj_on_def)

lemma inj_type2[simp]: "inj type2"
by (simp add: inj_on_def)

lemma type1_or_type2:
  "ALL x. ( (EX b. x = type1 b)
          | (EX c. x = type2 c) )"
apply (intro allI)
apply (induct_tac x)
by (auto)

lemma P_inv_type1I:
  "ALL x. P (inv type1 x) ==> P y"
by (simp)

lemma P_inv_type2I:
  "ALL x. P (inv type2 x) ==> P y"
by (simp)

(*** functions ***)

primrec
 sumset :: "('a set, 'b set) sum => ('a,'b) sum set"
where
  "sumset (type1 X) = {type1 a |a. a : X}"
 |"sumset (type2 X) = {type2 a |a. a : X}"

(*
consts
 open1  :: "('a, 'b) sum => 'a"
 open2  :: "('a, 'b) sum => 'b"

recdef open1 "{}"
  "open1 (type1 x) = x"

recdef open2 "{}"
  "open2 (type2 x) = x"

*)

primrec
 open1  :: "('a, 'b) sum => 'a"
where
  "open1 (type1 x) = x"

primrec
 open2  :: "('a, 'b) sum => 'b"
where
  "open2 (type2 x) = x"


(* primrec can be used for these defs, but it displays warnings. *)

primrec
  type1check :: "('a,'b) sum => bool"  ("type1?")
where
  "type1? (type1 x) = True"
 |"type1? (type2 x) = False"

primrec
  type2check :: "('a,'b) sum => bool"  ("type2?")
where
  "type2? (type1 x) = False"
 |"type2? (type2 x) = True"

abbreviation
 sum_type_eq_chk :: "('a,'b) sum => ('a,'b) sum => bool"  ("_ =type= _"  [55,55] 55)
 where "x =type= y  ==  type1? x = type1? y"

(* Isabelle 2005
syntax
  "_sum_type_eq_chk" :: "('a,'b) sum => ('a,'b) sum => bool"
                                  ("_ =type= _"  [55,55] 55)

translations
  "x =type= y" == "type1? x = type1? y"
*)

fun
 sum_cup  :: 
   "(('a set,'b set) sum * ('a set,'b set) sum) => ('a set,'b set) sum"
where
  "sum_cup (type1 X, type1 Y) = type1 (X Un Y)"
 |"sum_cup (type1 X, type2 Y) = type1 {}"
 |"sum_cup (type2 X, type1 Y) = type1 {}"
 |"sum_cup (type2 X, type2 Y) = type2 (X Un Y)"

fun
 sum_cap  :: 
   "(('a set,'b set) sum * ('a set,'b set) sum) => ('a set,'b set) sum"
where
  "sum_cap (type1 X, type1 Y) = type1 (X Int Y)"
 |"sum_cap (type1 X, type2 Y) = type1 {}"
 |"sum_cap (type2 X, type1 Y) = type1 {}"
 |"sum_cap (type2 X, type2 Y) = type2 (X Int Y)"

(*
isabelle 2011

consts
 sum_cup  :: 
   "(('a set,'b set) sum * ('a set,'b set) sum) => ('a set,'b set) sum"
 sum_cap  :: 
   "(('a set,'b set) sum * ('a set,'b set) sum) => ('a set,'b set) sum"

recdef sum_cup "{}"
  "sum_cup (type1 X, type1 Y) = type1 (X Un Y)"
  "sum_cup (type1 X, type2 Y) = type1 {}"
  "sum_cup (type2 X, type1 Y) = type1 {}"
  "sum_cup (type2 X, type2 Y) = type2 (X Un Y)"
*)



abbreviation
 sum_cup_mix :: "('a set,'b set) sum => ('a set,'b set) sum
                 => ('a set,'b set) sum"  ("_ Uns _" [65,66] 65)
 where "X Uns Y  == sum_cup (X,Y)"

abbreviation
 sum_cap_mix :: "('a set,'b set) sum => ('a set,'b set) sum
                 => ('a set,'b set) sum"  ("_ Ints _" [65,66] 65)
 where "X Ints Y  == sum_cap (X,Y)"

(*
Isabelle 2005
syntax
  "_sum_cup"  :: "('a set,'b set) sum => ('a set,'b set) sum
               => ('a set,'b set) sum"  ("_ Uns _" [65,66] 65)

  "_sum_cap"  :: "('a set,'b set) sum => ('a set,'b set) sum
               => ('a set,'b set) sum"  ("_ Ints _" [65,66] 65)

translations
  "X Uns Y"   == "sum_cup (X,Y)"
  "X Ints Y"  == "sum_cap (X,Y)"
*)

(******** X-symbols ********)
(*
notation (xsymbols) sum_cup_mix ("_ \<union>s _" [65,66] 65)
notation (xsymbols) sum_cap_mix ("_ \<inter>s _" [70,71] 70)
*)
(*
Isabelle 2005
syntax (output)
  "_sum_cupX"  :: "('a set,'b set) sum => ('a set,'b set) sum
                => ('a set,'b set) sum"  ("_ Uns _" [65,66] 65)

  "_sum_capX"  :: "('a set,'b set) sum => ('a set,'b set) sum
                => ('a set,'b set) sum"  ("_ Ints _" [65,66] 65)

syntax (xsymbols)
  "_sum_cupX"  :: "('a set,'b set) sum => ('a set,'b set) sum
                => ('a set,'b set) sum"  ("_ \<union>s _" [65,66] 65)

  "_sum_capX"  :: "('a set,'b set) sum => ('a set,'b set) sum
                => ('a set,'b set) sum"  ("_ \<inter>s _" [70,71] 70)

translations
  "X \<union>s Y"  == "X Uns Y"
  "X \<inter>s Y"  == "X Ints Y"
*)

(* lemmas *)

lemma type1_sumset_type1: "(type1 x : sumset (type1 X)) = (x : X)"
by (simp)

lemma type2_sumset_type2: "(type2 x : sumset (type2 X)) = (x : X)"
by (simp)

lemma P_inv_type1:
  "[| ALL x:X. P x ; y : sumset (type1 X) |] ==> P ((inv type1) y)"
by (auto)

lemma P_inv_type2:
  "[| ALL x:X. P x ; y : sumset (type2 X) |] ==> P ((inv type2) y)"
by (auto)

lemma mem_sumset_cup_lm:
  "X =type= Y -->
   (x : sumset (X Uns Y)) = (x : sumset X | x : sumset Y)"
apply (induct_tac X)
apply (induct_tac Y)
apply (force)
apply (simp)
apply (induct_tac Y)
apply (simp)
apply (force)
done

lemma mem_sumset_cup[simp]:
  "X =type= Y ==>
   (x : sumset (X Uns Y)) = (x : sumset X | x : sumset Y)"
by (simp add: mem_sumset_cup_lm)

lemma mem_sumset_cap_lm:
  "X =type= Y -->
   (x : sumset (X Ints Y)) = (x : sumset X & x : sumset Y)"
apply (induct_tac X)
apply (induct_tac Y)
apply (force)
apply (simp)
apply (induct_tac Y)
apply (simp)
apply (force)
done

lemma mem_sumset_cap[simp]:
  "X =type= Y ==>
   (x : sumset (X Ints Y)) = (x : sumset X & x : sumset Y)"
by (simp add: mem_sumset_cap_lm)

lemma sum_type1_or_type2: "type1? x | type2? x"
apply (induct_tac x)
by (simp_all)

(*** sub set ***)

(* isabelle2009-1

consts
 sub_sumset ::
   "('a set,'b set) sum => (('a,'b)sum => bool) => ('a set,'b set) sum"

primrec
  "sub_sumset (type1 X) f = type1 {x:X. f(type1 x)}"
  "sub_sumset (type2 X) f = type2 {x:X. f(type2 x)}"

*)

primrec
  sub_sumset ::
   "('a set,'b set) sum => (('a,'b)sum => bool) => ('a set,'b set) sum"
where
   "sub_sumset (type1 X) f = type1 {x:X. f(type1 x)}"
 | "sub_sumset (type2 X) f = type2 {x:X. f(type2 x)}"


syntax
  "@sub_sumset" :: "pttrn => ('a set,'b set) sum => bool =>
                   ('a set,'b set) sum"    ("(1{_:_./ _}s)")

translations
  "{x:X. b}s"  == "CONST sub_sumset X (%x. b)"     (* modified for 2009-2 *)

lemma sub_sumset_true[simp]:
  "{x:X. True}s = X"
by (induct_tac X, auto)

lemma sub_sumset_cup[simp]:
  "((sub_sumset X f) Uns (sub_sumset X g)) = {x:X. f x | g x}s"
by (induct_tac X, auto)

lemma sub_sumset_cap[simp]:
  "((sub_sumset X f) Ints (sub_sumset X g)) = {x:X. f x & g x}s"
by (induct_tac X, auto)

lemma sub_sumset_type_eq[simp]: 
  "sub_sumset X f =type= sub_sumset X g"
by (induct_tac X, auto)

lemma sumset_sub_sumset[simp]: 
  "sumset (sub_sumset X f) = {x: sumset X. f x}"
by (induct_tac X, auto)

lemma sub_sumset_eq_lm: 
  "(ALL c : sumset C. f c = g c) -->  sub_sumset C f = sub_sumset C g"
apply (induct_tac C)
apply (auto)
done

lemma sub_sumset_eq: 
  "ALL c : sumset C. f c = g c ==>  sub_sumset C f = sub_sumset C g"
by (simp add: sub_sumset_eq_lm)

end
