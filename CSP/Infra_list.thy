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
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Infra_list
imports Infra_nat
begin

(*****************************************************
               Small lemmas for List 
 *****************************************************)

(*** list of the empty set ***)

primrec
  Emptyset_list :: "nat => 'a set list"    ("{}::_" [1000] 1000 )
where
  "{}::0 = []"
 |"{}::(Suc n) = {} # {}::n"

lemma not_emptyset_EX: "A ~= {} = (EX a. a:A)"
by (auto)

lemma one_list_decompo: 
   "([a] = s @ t) = ((s =[] & t = [a]) | (s = [a] & t = []))"
by (induct_tac s, auto)

lemma list_nil_or_unnil: "ALL t. (t = []) | (EX a s. t = a # s)"
apply (intro allI)
by (induct_tac t, auto)

lemma list_last_nil_or_unnil: "ALL t. (t = []) | (EX s a. t =s @ [a])"
apply (intro allI)
by (induct_tac t, auto)

(*** unnil ***)

lemma unnil_ex_ALL: "ALL s. s ~= [] --> (EX a. a : set s)"
apply (rule allI)
apply (induct_tac s)
apply (auto)
done

lemma unnil_ex: "s ~= [] ==> (EX a. a : set s)"
by (simp add: unnil_ex_ALL)

(*** nil ***)

lemma emptyset_to_nil: "({} = set t) = (t = [])"
by (auto)

lemma nil_to_emptyset: "(X = set []) = (X = {})"
by (auto)

(****** butlast ******)

lemma notin_butlast_decompo:
  "e ~: set (butlast (s @ t))
      = ((e ~: set s & e ~: set (butlast t)) | (e ~: set (butlast s) & t = []))"
apply (induct_tac s)
by (auto)

lemma in_butlast_decompo:
  "e : set (butlast (s @ t))
      = ((e : set s | e : set (butlast t)) & (e : set (butlast s) | t ~= []))"
apply (induct_tac s)
by (auto)

lemma butlast_subseteq : "set (butlast s) <= set s"
apply (induct_tac s)
by (auto)

(*** length s = 1 ***)

lemma list_length_one: "(length s = Suc 0) = (EX a. s =[a])"
apply (induct_tac s)
by (auto)

(****** list app app ******)

(*** lm ***)

lemma list_app_app_only_if:
  "ALL s1 s2 t1 t2. (s1 @ s2 = t1 @ t2)
       --> ((EX u. s1 = t1 @ u & t2 = u @ s2) |
            (EX u. t1 = s1 @ u & s2 = u @ t2)   )"
apply (rule allI)
apply (induct_tac s1)
apply (intro allI impI)
apply (rule disjI2)
apply (rule_tac x="t1" in exI)
apply (simp)

 (* step *)

apply (intro allI impI)
apply (insert list_nil_or_unnil)
apply (rotate_tac -1)
apply (drule_tac x="t1" in spec)
apply (erule disjE)

  (* t1 = [] *)
 apply (simp)

  (* t1 ~= [] *)
 apply (elim exE)
 apply (simp)
done

(*** list app app ***)

lemma list_app_app:
  "(s1 @ s2 = t1 @ t2) =
      ((EX u. s1 = t1 @ u & t2 = u @ s2) |
       (EX u. t1 = s1 @ u & s2 = u @ t2))"
apply (rule iffI)
apply (simp add: list_app_app_only_if)
apply (auto)
done

(*** list app [a] ***)

lemma list_app_decompo_one:
  "(s @ t = [a]) = ((s = [a] & t = []) | (s = [] & t = [a]))"
apply (induct_tac s)
by (auto)

(*** map ***)

lemma divide_map_fst_ALL: 
  "ALL ss s2 s1. map fst (ss::('a * 'b) list) = s1 @ s2
       --> (EX (ss1::('a * 'b) list) (ss2::('a * 'b) list).
            ss = ss1 @ ss2 & map fst ss1 = s1 & map fst ss2 = s2)"
apply (rule allI)
apply (rule allI)
apply (induct_tac s2)
apply (simp_all)

apply (intro allI impI)
apply (drule_tac x="s1 @ [a]" in spec)
apply (simp)
apply (elim conjE exE)
apply (insert list_last_nil_or_unnil)
apply (drule_tac x="ss1" in spec)
apply (erule disjE)
apply (simp)
apply (elim conjE exE)
apply (simp)
apply (rule_tac x="s" in exI, simp)
done

lemma divide_map_fst: 
  "map fst (ss::('a * 'b) list) = s1 @ s2
       ==> (EX (ss1::('a * 'b) list) (ss2::('a * 'b) list).
            ss = ss1 @ ss2 & map fst ss1 = s1 & map fst ss2 = s2)"
by (simp add: divide_map_fst_ALL)

(*** zip ***)

lemma map_fst_zip_eq_lm: 
  "ALL t. length s <= length t --> map fst (zip s t) = s"
apply (induct_tac s)
apply (simp_all)
apply (intro allI impI)
apply (insert list_nil_or_unnil)
apply (rotate_tac -1)
apply (drule_tac x="t" in spec)
by (auto)

lemma map_fst_zip_eq: 
  "length s <= length t ==> map fst (zip s t) = s"
by (simp add: map_fst_zip_eq_lm)

lemma fst_set_zip_eq_lm: 
  "ALL t. length s <= length t --> fst ` set (zip s t) = set s"
apply (induct_tac s)
apply (simp_all)
apply (intro allI impI)
apply (insert list_nil_or_unnil)
apply (rotate_tac -1)
apply (drule_tac x="t" in spec)
apply (erule disjE, simp)
apply (elim conjE exE, simp)
done

lemma fst_set_zip_eq: 
  "length s <= length t ==> fst ` set (zip s t) = set s"
by (simp add: fst_set_zip_eq_lm)

lemma zip_map_fst_snd: "zip (map fst s) (map snd s) = s"
apply (induct_tac s)
by (auto)

lemma set_nth: "(a : set s) = (EX i. i < length s & a = s!i)"
apply (induct_tac s)
apply (simp_all)
apply (rule iffI)

(* => *)
 apply (force)

(* <= *)
 apply (elim conjE exE)
 apply (drule sym)
 apply (simp)
 apply (insert nat_zero_or_Suc)
 apply (drule_tac x="i" in spec)
 apply (erule disjE, simp)
 apply (elim exE, simp)
done

lemma nth_pair_zip_in_ALL:
      "ALL s t i. (length s = length t & i < length t)
       --> (s!i,t!i) : set (zip s t)"
apply (rule allI)
apply (induct_tac s)
apply (auto)
apply (insert list_nil_or_unnil)
apply (rotate_tac -1)
apply (drule_tac x="t" in spec)
apply (erule disjE, simp)
apply (elim conjE exE, simp)

apply (insert nat_zero_or_Suc)
apply (drule_tac x="i" in spec)
apply (erule disjE, simp)
apply (elim conjE exE, simp)
done

lemma nth_pair_zip_in:
      "[| length s = length t ; i < length t |]
       ==> (s!i,t!i) : set (zip s t)"
by (simp add: nth_pair_zip_in_ALL)

(*** emptyset list ***)

lemma length_Emptyset_list[simp]: "length({}::n) = n"
apply (induct_tac n)
by (simp_all)


(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)

(* --------------------------------------------------- *
             convenient lemmas for proofs
 * --------------------------------------------------- *)

(* -----------
      list
 * ----------- *)

lemma not_nil: "(s ~= []) = (EX a t. s=a#t)"
apply (induct_tac s)
apply (auto)
done

lemma tl_nil: "(tl s = []) = (s=[] | (EX a. s=[a]))"
apply (induct_tac s)
by (auto)

lemma tl_not_nil: "(tl s ~= []) = (EX a1 a2 t. s=a1#a2#t)"
apply (induct_tac s)
apply (auto simp add: tl_nil)
done


end
