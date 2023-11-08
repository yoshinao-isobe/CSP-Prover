           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   June 2005  (modified)   |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2013         |
            |                   June 2013  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                  April 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory Infra_set
imports Infra_list
begin

section \<open> Set \<close>

(*****************************************************
               Small lemmas for Set
 *****************************************************)
subsection \<open> Small lemmas for Set \<close>

(*notin_subset = contra_subsetD*)

lemma notin_set_butlast: "a ~: set s ==> a ~: set (butlast s)"
apply (erule contrapos_pp)
by (simp add: in_set_butlastD)


(*in_set_butlast = List.in_set_butlastD
lemma in_set_butlast: "a : set (butlast s) ==> a : set s"
apply (erule contrapos_pp)
by (simp add: notin_set_butlast)*)

lemma in_image_set: "x : f ` X = (EX y. x = f y & y:X)"
by (auto)

(*inj_image_diff_dist = image_set_diff
lemma inj_image_diff_dist: "inj f ==> f ` (A - B) = f ` A - f ` B"
by (auto simp add: inj_on_def)*)

(*inj_image_Int_dist = image_Int
lemma inj_image_Int_dist: "inj f ==> f ` (A Int B) = f ` A Int f ` B"
by (auto simp add: inj_on_def)*)

lemma subsetE: "[| A <= B ; [| ALL x:A. x:B |] ==> R |] ==> R"
by (auto)

(*Un_sym = Un_commute
lemma Un_sym: "X Un Y = Y Un X"
by (simp only: Un_commute)*)

(*Int_subset_eq = Int_absorb2
lemma Int_subset_eq:"A <= B ==> A Int B = A"
by (simp only: Int_absorb2)*)

lemma Int_insert_eq: "A Int insert x A = A"
by (auto)

lemma in_Union_EX: "x : Union Xs = (EX X. x:X & X:Xs)"
by (auto)

lemma subset_or_not_subset:
 "ALL A B. ((A::'a set) <= B) | (B <= A) | (EX a b. a : A & a ~: B & b ~: A & b : B)"
by (auto)

lemma not_subset_iff:
  "(~ (A::'a set) < B) = ((B <= A) | (EX a b. a : A & a ~: B & b ~: A & b : B))"
by (auto)

lemma Union_snd_Un: 
  "Union (snd ` f ` (I1 Un I2))=
   Union (snd ` f ` I1) Un Union (snd ` f ` I2)"
by (auto)

(*Union_snd_set_Un = UN_Un
lemma Union_snd_set_Un: 
  "Union (snd ` (set s Un set t)) = Union (snd ` set s) Un Union (snd ` set t)"
by (simp only: UN_Un)*)

lemma neq_Set_EX1: "EX a:A. a~:B ==> A ~= B"
by (auto)

lemma neq_Set_EX2: "EX a:A. a~:B ==> B ~= A"
by (auto)




(*****************************
          finite set
 *****************************)
subsection \<open> finite set \<close>


lemma Union_index_fun:
   "ALL i:I1. PXf2 (f i) = PXf1 i
    ==> Union (snd ` PXf2 ` f ` I1) = Union (snd ` PXf1 ` I1)"
apply (rule)
apply (rule, simp)
apply (rule, simp)
done

lemma finite_pair_set1:
   "[| finite F1 ;ALL j:F1. finite (F2 j) |]
       ==> finite {(i, j)|i j. j : F1 & i : F2 j}"
(*
apply (induct set: Finites)     Isabelle 2005
*)
apply (induct set: finite)     (* Isabelle 2007 *)
apply (simp)
apply (subgoal_tac 
   "{(i, j). (j = x | j : F) & i : F2 j}
  = (%i. (i, x)) ` (F2 x) Un {(i, j). j : F & i : F2 j}")
apply (simp)
by (auto)

lemmas finite_pair_set2 = finite_pair_set1[simplified]

lemmas finite_pair_set = finite_pair_set1 finite_pair_set2




subsection \<open> finite set --> EX max \<close>

lemma nonempty_finite_set_exists_max_fun_subset:
  "[| finite I ; I ~= {} |]
    ==> EX J. J <= I & J ~= {} & (ALL j:J. ALL i:I. ~((f::'a => 'b::order) j < f i))"
(*
apply (induct set: Finites)     Isabelle 2005
*)
apply (induct set: finite)     (* Isabelle 2007 *)
apply (simp_all)

(* {} *)
 apply (case_tac "F = {}")
 apply (simp_all)

(* {x} *)
 apply (rule_tac x="{x}" in exI)
 apply (simp)

(* step case *)
 apply (elim conjE exE)
 apply (case_tac "EX j:J. (f j < f x)")
 apply (rule_tac x="(J - {j. f j < f x}) Un {x}" in exI)
 apply (simp)
 apply (rule conjI)
 apply (fast)
 apply (intro ballI)
 apply (elim bexE)
 apply (drule_tac x="j" in bspec, simp)
 apply (drule_tac x="i" in bspec, simp)
 apply (case_tac "~ f x < f i", simp)
 apply (simp)
 apply (rotate_tac -2)
 apply (erule contrapos_np)
 apply (clarsimp)
 apply (drule_tac x="J" in spec, fast)
done

lemma nonempty_finite_set_exists_max_fun:
  "[| finite I ; I ~= {} |]
    ==> EX j:I. ALL i:I. ~((f::'a => 'b::order) j < f i)"
apply (insert nonempty_finite_set_exists_max_fun_subset[of I f])
apply (simp)
apply (elim conjE exE)
apply (subgoal_tac "EX j. j:J")
apply (elim exE)
apply (rule_tac x="j" in bexI)
apply (auto)
done

(* finite set --> EX min *)

lemma nonempty_finite_set_exists_min_fun_subset:
  "[| finite I ; I ~= {} |]
    ==> EX J. J <= I & J ~= {} & (ALL j:J. ALL i:I. ~((f::'a => 'b::order) i < f j))"
(*
apply (induct set: Finites)     Isabelle 2005
*)
apply (induct set: finite)     (* Isabelle 2007 *)
apply (simp_all)

(* {} *)
 apply (case_tac "F = {}")
 apply (simp_all)

(* {x} *)
 apply (rule_tac x="{x}" in exI)
 apply (simp)

(* step case *)
 apply (elim conjE exE)
 apply (case_tac "EX j:J. (f x < f j)")
 apply (rule_tac x="(J - {j. f x < f j}) Un {x}" in exI)
 apply (simp)
 apply (rule conjI)
 apply (fast)
 apply (intro ballI)
 apply (elim bexE)
 apply (drule_tac x="j" in bspec, simp)
 apply (drule_tac x="i" in bspec, simp)
 apply (case_tac "~ f i < f x", simp)
 apply (simp)
 apply (rotate_tac -2)
 apply (erule contrapos_np)
 apply (clarsimp)
 apply (drule_tac x="J" in spec, fast)
done

lemma nonempty_finite_set_exists_min_fun:
  "[| finite I ; I ~= {} |]
    ==> EX j:I. ALL i:I. ~((f::'a => 'b::order) i < f j)"
apply (insert nonempty_finite_set_exists_min_fun_subset[of I f])
apply (simp)
apply (elim conjE exE)
apply (subgoal_tac "EX j. j:J")
apply (elim exE)
apply (rule_tac x="j" in bexI)
apply (auto)
done



subsection \<open> cardinality of the set of a list \<close>

lemma card_set_eq_length:
  "(card (set s) = length s) =
   (ALL i. i < length s --> (ALL j. j < length s & s!i = s!j --> i = j))"
apply (induct_tac s)
apply (auto)

apply (insert nat_zero_or_Suc)
apply (rotate_tac -1)
apply (frule_tac x="i" in spec)
apply (drule_tac x="j" in spec)
apply (elim disjE exE)
apply (simp_all)
apply (simp add: card_insert_if)
apply (simp add: card_insert_if)
apply (force)

apply (case_tac "a ~: set list")
apply (simp)
apply (simp)
apply (simp add: in_set_conv_nth)
apply (elim conjE exE)
apply (rotate_tac 2)
apply (drule_tac x="0" in spec)
apply (simp)
apply (rotate_tac -1)
apply (drule_tac x="Suc i" in spec)
apply (simp)

apply (case_tac "a ~: set list")
apply (simp)
apply (simp add: card_insert_if)
apply (subgoal_tac "card (set list) <= (length list)")
apply (simp)
apply (simp (no_asm_use) add: card_length)

apply (drule_tac x="Suc i" in spec)
apply (simp)
apply (rotate_tac -1)
apply (drule_tac x="Suc j" in spec)
apply (simp)
done



(*****************************************************
   Small lemmas for isListOf (Finite Set <--> List)
 *****************************************************)
subsection \<open> isListOf \<close>

 (* Isabelle 2013
consts
  isListOf :: "'a list => 'a set => bool"       ("_ isListOf _" [55,55] 55)

defs
  isListOf_def : 
    "s isListOf X  == 
     X = set s & (card (set s) = length s)"
*)

definition
  isListOf :: "'a list => 'a set => bool"       ("_ isListOf _" [55,55] 55)

  where
  isListOf_def : 
    "s isListOf X  == 
     X = set s & (card (set s) = length s)"



lemma isListOf_EX: "(finite X) ==> EX s. s isListOf X"
apply (simp add: isListOf_def)
apply (rule finite_induct[of _ "(%X. EX s. X = set s & card (set s) = length s)"])
                        (* for Isabelle 2008 *)
apply (simp_all)

apply (elim conjE exE)
apply (simp)
apply (rule_tac x="x # s" in exI)
apply (simp)
done

(* finite_list: "finite A ==> EX l. set l = A" *)
(* finite_set : "finite (set xs)" *)

lemma isListOf_set_eq:
  "x isListOf X ==> set x = X"
by (simp add: isListOf_def)

lemma isListOf_distinct:
  "x isListOf X \<Longrightarrow> distinct x"
by (simp only: isListOf_def card_distinct)

lemma set_SOME_isListOf: "(finite S) ==> set (SOME t. t isListOf S) = S"
apply (insert isListOf_EX[of S])
apply (simp)
apply (erule exE)
apply (rule someI2)
apply (simp)
apply (simp add: isListOf_set_eq)
done

lemma isListOf_nonemptyset:
  "[| X ~= {} ; x isListOf X |] ==> x ~= []"
by (simp add: isListOf_def)

lemma isListOf_index_to_nth:
  "Is isListOf I ==> ALL i:I. EX n. n<length Is & i = Is ! n"
apply (rule ballI)
apply (simp add: isListOf_def)
apply (elim conjE)
apply (simp add: set_nth)
done

lemma isListOf_nth_in_index:
  "[| Is isListOf I ; n<length Is |] ==> Is ! n : I"
by (simp add: isListOf_def)

lemma isListOf_index_to_nthE:
  "[| Is isListOf I ; 
   [| Is isListOf I ; ALL i:I. EX n. n<length Is & i = Is ! n |] ==> R |]
   ==> R"
by (simp add: isListOf_index_to_nth)

lemma isListOf_nth_in_indexE:
  "[| Is isListOf I ; [| Is isListOf I ; ALL n. n<length Is --> Is ! n : I |] ==> R |]
   ==> R"
by (simp add: isListOf_def)

lemma isListOf_THE_nth:
  "[| Is isListOf I ; n < length Is|]
   ==> (THE m. Is ! m = Is ! n & m < length Is) = n"
apply (rule the_equality)
apply (simp)
apply (simp add: isListOf_def)
apply (simp add: card_set_eq_length)
done

(*** nil ***)

lemma isListOf_emptyset_to_nil[simp]: "(Is isListOf {}) = (Is = [])"
apply (auto simp add: isListOf_def)
done

lemma isListOf_nil_to_emptyset[simp]: "([] isListOf X) = (X = {})"
by (simp add: isListOf_def)

(*** one ***)

lemma isListOf_oneset_to_onelist_ALL: "ALL t a. t isListOf {a} --> t = [a]"
apply (rule allI)
apply (induct_tac t)
apply (simp add: isListOf_def)

apply (simp add: isListOf_def)
apply (elim allE disjE)
apply (auto)
apply (drule subset_singletonD, elim disjE, simp_all)
apply (drule subset_singletonD, elim disjE, simp_all)
done

lemma isListOf_oneset_to_onelist[simp]: "(t isListOf {a}) = (t = [a])"
apply (auto simp add: isListOf_oneset_to_onelist_ALL)
apply (simp add: isListOf_def)
done

lemma isListOf_onelist_to_oneset[simp]: "([a] isListOf X) = (X = {a})"
apply (simp add: isListOf_def)
done


(* SOME isListOf *)

lemma some_isListOf_Empty :
    "I = {} \<Longrightarrow> (SOME x. x isListOf I) = []"
by (auto)

lemma some_isListOf_nonEmpty :
    "I \<noteq> {} \<Longrightarrow> x isListOf I \<Longrightarrow> x \<noteq> []"
by (auto)

lemma some_isListOf_finite :
    "I \<noteq> {} \<and> finite I \<Longrightarrow> (SOME Is. Is isListOf I) \<noteq> []"
by (rule someI2_ex, rule isListOf_EX, auto)

lemmas some_isListOf = some_isListOf_Empty some_isListOf_finite


(* ListMem lemmas *)

lemma ListMem_tail :
    "i \<noteq> a \<and> l \<noteq> [] \<Longrightarrow> ListMem i l \<Longrightarrow> ListMem i (a # l)"
  apply (induct l)
  apply (simp add: ListMem_iff)
  apply (simp add: ListMem_iff)
done


(* =================================================== *
 |             addition for CSP-Prover 6               |
 * =================================================== *)

subsection \<open> asList \<close>

definition asList :: "'a set \<Rightarrow> 'a list"
where
  "asList (s::'a set) == SOME x . x isListOf s"

(*declare [[coercion asList]]*)


lemma set_asList [simp]: "finite X \<Longrightarrow> set (asList X) = X"
  by (simp add: set_SOME_isListOf asList_def)


lemma asList_empty [simp]: "asList {} = []"
  by (simp add: asList_def)


lemma asList_nil : "finite x \<Longrightarrow> asList x = [] \<longleftrightarrow> x = {}"
  apply (simp add: asList_def)
  apply (rule someI2_ex, rule isListOf_EX, simp)
  by (simp add: isListOf_def)


lemma distinct_asList : "finite x \<Longrightarrow> distinct (asList (x::'a set))"
  apply (simp add: asList_def)
  by (rule someI2_ex, rule isListOf_EX, simp, simp add: isListOf_distinct)


lemma set_remove1_asList_eq :
    "finite y \<Longrightarrow>
     set (remove1 x (asList y)) = y - {x}"
  apply (frule distinct_asList)
  by (simp only: set_remove1_eq set_asList)


lemma in_set_remove1D:
      "a \<in> set(remove1 b xs) \<Longrightarrow> a \<noteq> b \<longrightarrow> a \<in> set xs"
  by (rule, simp)

lemma in_set_remove1_distinctD:
      "distinct xs \<Longrightarrow> a \<in> set(remove1 b xs) \<Longrightarrow> a \<noteq> b \<and> a \<in> set xs"
  by (rule, auto)




(* --------------------------------------------------- *
               addition for CSP-Prover 5
 * --------------------------------------------------- *)

subsection \<open> convenient lemmas for practical verification in CSP \<close>


subsubsection \<open> event (not)in channel \<close>

lemma event_notin_channel_map: 
   "ALL x:X. a ~= c x ==> a ~: c ` X"
by (auto)

lemma event_in_channel_map_inj: 
   "inj c ==> (c v : c ` X) = (v:X)"
by (auto simp add: inj_on_def)

lemma event_in_channel_map: 
   "v:X ==> c v : c ` X"
by (simp)

lemma event_notin_channel_range: 
   "ALL x. a ~= c x ==> a ~: range c"
by (auto)

lemma event_in_channel_range: 
   "c v : range c"
by (simp)

lemmas event_notin_channel = 
       event_in_channel_map_inj
       event_notin_channel_map
       event_notin_channel_range



subsubsection \<open> channel Int event \<close>

(* channel_Int_event_eq *)

lemma channel_Int_event_eq_map_left:
  "inj c ==> (c ` X) Int {c v} = (c ` (X Int {v}))"
by (auto simp add: inj_on_def)

lemma channel_Int_event_eq_map_right:
  "inj c ==> {c v} Int (c ` X) = (c ` (X Int {v}))"
by (auto simp add: inj_on_def)

lemma set_Int_single_in_left:
  "a:A ==> A Int {a} = {a}"
by (auto)

lemma set_Int_single_in_right:
  "a:A ==> {a} Int A = {a}"
by (auto)

(* channel_Int_event_not *)

lemma set_Int_single_notin_left:
  "a~:A ==> A Int {a} = {}"
by (simp)

lemma set_Int_single_notin_right:
  "a~:A ==> {a} Int A = {}"
by (simp)

(* ------------------------- *
      channel_Int_event
 * ------------------------- *)

lemmas channel_Int_event =
       channel_Int_event_eq_map_right
       channel_Int_event_eq_map_left
       set_Int_single_in_left
       set_Int_single_in_right




subsubsection \<open> channel Int channel \<close>


lemma channel_Int_channel_eq:
  "inj c ==> (c ` X) Int (c ` Y) = (c ` (X Int Y))"
by (auto simp: inj_on_def)

(* channel_Int_channel_neq *)

lemma channel_Int_channel_neq_map:
  "[| ALL x:X. ALL y:Y. a x ~= b y |] ==> (a ` X) Int (b ` Y) = {}"
by (auto)

lemma channel_Int_channel_neq_range:
  "[| ALL x y. a x ~= b y |] ==> (range a) Int (range b) = {}"
by (auto)

lemmas channel_Int_channel_neq =
       channel_Int_channel_neq_map
       channel_Int_channel_neq_range

(* ------------------------- *
      channel_Int_channel
 * ------------------------- *)

lemmas channel_Int_channel =
       channel_Int_channel_eq
       channel_Int_channel_neq




subsubsection \<open> channel Un channel \<close>

lemma channel_Un_channel:
  "inj c ==> (c ` X) Un (c ` Y) = (c ` (X Un Y))"
by (auto simp: inj_on_def)




subsubsection \<open> event insert Int \<close>

(* event_insert_Int *)

lemma event_insert_Int_event_left:
  "a ~= b | b ~= a ==> (insert a A) Int {b} = A Int {b}"
by (auto)

lemma event_insert_Int_event_right:
  "a ~= b | b ~= a ==> {b} Int (insert a A) = {b} Int A"
by (auto)

lemma event_insert_Int_channel_notin_left:
  "a ~: B ==> (insert a A) Int B = A Int B"
by (auto)

lemma event_insert_Int_channel_notin_right:
  "a ~: B ==> B Int (insert a A) = B Int A"
by (auto)

lemma event_insert_Int_channel_in_left:
  "a : B ==> (insert a A) Int B = insert a (A Int B)"
by (auto)

lemma event_insert_Int_channel_in_right:
  "a : B ==> B Int (insert a A) = insert a (B Int A)"
by (auto)

lemma event_insert_Int_insert_channel_in:
  "a:B ==>
   (insert a A) Int (insert b B) =
    insert a (A Int (insert b B))"
by (auto)

lemma event_insert_Int_insert_channel_notin:
  "[| a~= b | b~=a ; a~:B |] ==>
   (insert a A) Int (insert b B) =
    (A Int (insert b B))"
by (auto)

lemmas event_insert_Int =
       event_insert_Int_event_left
       event_insert_Int_event_right
       event_insert_Int_channel_notin_left
       event_insert_Int_channel_notin_right
       event_insert_Int_channel_in_left
       event_insert_Int_channel_in_right
       event_insert_Int_insert_channel_in
       event_insert_Int_insert_channel_notin



subsubsection \<open> event insert Un \<close>

(* event_insert_Un *)

lemma event_insert_in:
  "a : A ==> (insert a A) = A"
by (auto)

(* lemma subset_insertI: "A <= insert a A" *)



subsubsection \<open> event insert diff \<close>

(* event_insert_diff *)

lemma event_diff_in:
  "a : A ==> {a} - A = {}"
by (simp)

lemma event_diff_notin:
  "a ~: A ==> {a} - A = {a}"
by (auto)

lemma event_diff_notin_map:
  "[| inj c ; v ~: X |] ==> {c v} - (c ` X) = {c v}"
by (auto simp add: inj_on_def)

lemmas event_diff = 
       event_diff_notin
       event_diff_notin_map



subsubsection \<open> channel diff \<close>

lemma channel_diff_eq_map:
  "inj c ==> (c ` X) - (c ` Y) = c ` (X-Y)"
by (auto simp add: inj_on_def)

lemma channel_diff_neq_map:
  "ALL x:X. ALL y:Y. a x ~= b y ==> (a ` X) - (b ` Y) = (a ` X)"
by (auto)

lemma channel_diff_neq_range:
  "ALL x. ALL y. a x ~= b y ==> range a - range b = range a"
by (auto)

lemmas channel_diff = 
       channel_diff_eq_map
       channel_diff_neq_map
       channel_diff_neq_range




subsubsection \<open> set of events - distribution \<close>

lemma Un_diff_dist_right: "(A Un B) - C = (A-C) Un (B-C)"
apply (auto)
done

lemma Un_diff_dist_left: "C - (A Un B) = (C-A) Int (C-B)"
apply (auto)
done

lemma insert_diff_dist_right_in: 
  "a:C ==> (insert a A) - C = A-C"
by (simp)

lemma insert_diff_dist_right_notin: 
  "a~:C ==> (insert a A) - C = {a} Un (A-C)"
by (auto)

lemma insert_diff_dist_left_eq_event: 
  "{a} - (insert a A) = {}"
by (simp)

lemma insert_diff_dist_left_eq_map: 
  "inj c ==> (c ` X) - (insert (c v) A) = (c ` (X-{v})) Int ((c ` X)-A)"
by (auto simp add: inj_on_def)

lemma insert_diff_dist_left_eq_range: 
 "inj c ==> (range c) - (insert (c v) A) = (c ` (UNIV-{v})) Int ((range c)-A)"
by (auto simp add: inj_on_def)

lemma insert_diff_dist_left_neq_event: 
  "a ~= b | b ~= a ==> {a} - (insert b A) = {a}-A"
by (auto)

lemma insert_diff_dist_left_neq: 
  "a ~: X ==> X - (insert a A) = X - A"
by (auto)

lemmas event_insert_diff_dist =
      Un_diff_dist_right
      Un_diff_dist_left
      insert_diff_dist_right_in
      insert_diff_dist_right_notin
      insert_diff_dist_left_eq_event
      insert_diff_dist_left_eq_map
      insert_diff_dist_left_eq_range
      insert_diff_dist_left_neq_event
      insert_diff_dist_left_neq
      event_diff
      channel_diff



subsubsection \<open> csp simp set \<close>


lemmas dist_event_set = Int_Un_distrib Int_Un_distrib2
                        event_insert_diff_dist

lemmas simp_event_set = event_insert_in
                        channel_Int_event
                        channel_Int_channel
                        channel_Un_channel
                        event_insert_Int
                        event_notin_channel
                        dist_event_set

(*                      Un_assoc     (A Un B) Un C = A Un(B Un C) *)

end
