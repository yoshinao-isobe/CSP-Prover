           (*-------------------------------------------*
            |       Uniform Candy Distribution          |
            |                                           |
            |           November 2007 for Isabelle 2005 |
            |           November 2008 for Isabelle 2008 |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory UCD_data1
imports CSP_F
begin

(*****************************************************************

         1. Data part

 *****************************************************************)

(* line and circ *)

definition
  fill       :: "nat => nat"
  where
  fill_def     : "fill n == if even n then n else n+1"
    
definition  
  allEven    :: "nat list => bool"
  where
  allEven_def  : "allEven s == (ALL s:set s. even s)"

primrec
  lineNext   :: "nat list => nat => nat list"
where
  "lineNext  ([]) = (%x. [])"
 |"lineNext (n#s) = (%x. if (s=[]) then [fill(n div 2 + x)]
                         else (fill(n div 2 + hd(s) div 2))#(lineNext s x))"

definition
  circNext   :: "nat list => nat list"
where
  circNext_def : "circNext s == (if s=[] then [] else lineNext s (hd s div 2))"

primrec
  circNexts  :: "nat => nat list => nat list"
where
  "circNexts      0  = (%s. s)"
 |"circNexts (Suc N) = (%s. circNexts N (circNext s))"



(* max and min *)

primrec
  maxList        :: "nat list => nat"
where
  "maxList ([])  = 0"
 |"maxList (n#s) = (if (maxList(s) < n) then n else maxList(s))"

primrec
  minList        :: "nat list => nat"
where
  "minList ([])  = 0"
 |"minList (n#s) = (if (s=[]) then n
                    else if (n < minList(s)) then n else minList(s))"

primrec
  howMany        :: "nat => nat list => nat"
where
  "howMany m ([])  = 0"
 |"howMany m (n#s) = (if (m=n) then (Suc (howMany m s)) else howMany m s)"

definition
  stableList     :: "nat list => bool"
where
  stableList_def: "stableList s == ALL n:set s. n = minList s"

primrec
  makeStableList :: "nat => nat => nat list"
where
  "makeStableList 0 = (%n. [])"
 |"makeStableList (Suc l) = (%n. n#makeStableList l n)"

(* ------ test ------ *)

lemma lineNext_test: 
  "lineNext [4, 2, 10] 2 = [4, 6, 8]"
by (simp add: fill_def)

lemma circNext_test: 
  "circNext [4, 2, 10] = [4, 6, 8]"
by (simp add: circNext_def fill_def)

lemma maxList_test: 
  "maxList [4, 2, 10, 1, 5] = 10"
by (simp)

lemma minList_test: 
  "minList [4, 2, 10, 1, 5] = 1"
by (simp)

lemma howMany_test: 
  "howMany 2 [4, 2, 10, 2, 5, 2] = 3"
by (simp)

lemma makeStableList_test: 
  "makeStableList (Suc (Suc (Suc 0))) 5 = [5, 5, 5]"
by (simp)

(* ------------------------------------------------- *
                convenient lemmas 
 * ------------------------------------------------- *)

lemma not_nil_EX: "(s ~= []) = (EX a t. s=a#t)"
by (induct_tac s, auto)

lemma hd_in_list[simp]: "s ~= [] --> hd s : set s"
by (induct_tac s, auto)

lemma nth_hd: "s ~= [] --> s!0 = hd s"
by (induct_tac s, auto)

lemma nth_last: "Suc i = length s ==> (s ! i = last s)"
apply (insert list_last_nil_or_unnil)
apply (drule_tac x="s" in spec)
apply (auto)
done

lemma list_not_nil: "(s ~= []) = (EX a t. s = a#t)"
by (induct_tac s, auto)

lemma even_EX: "(even n) = (EX m. n = (2::nat)*m)"
apply (auto elim: evenE)
(* for Isabelle 2013
apply (simp add: even_nat_equiv_def2)
apply (auto)
apply (rule_tac x="y" in exI, simp)
apply (rule_tac x="m" in exI, simp)
*)
done

lemma less_Suc: "(n < Suc N) = (n=0 | (EX m. n = Suc m & m < N))"
by (induct_tac n, auto)

lemma zero_less_EX: "(0 < n) = (EX m. n = Suc m)"
by (induct_tac n, auto)

lemma in_set_nth: "n:set s = (EX i. i<length s & n = s!i)"
apply (induct_tac s, auto)
apply (auto simp add: less_Suc)
done

lemma list_length_more_one: "(Suc 0 < length s) = (s ~= [] & tl s ~= [])"
by (induct_tac s, auto)

(* ------------------------------------------------- *
               lemmas on line and circ
 * ------------------------------------------------- *)

(* [] *)

lemma allEven_nil[simp]: "allEven []"
by (simp add: allEven_def)

lemma lineNext_nil_iff[simp]: "(lineNext s x = []) = (s = [])"
by (induct_tac s, auto)

lemma circNext_nil_iff[simp]: "(circNext s = []) = (s = [])"
by (simp add: circNext_def)

lemma tl_lineNext_nil_iff[simp]: "(tl (lineNext s x) = []) = (tl s = [])"
by (induct_tac s, auto)

lemma tl_circNext_nil_iff[simp]: "(tl (circNext s) = []) = (tl s = [])"
by (simp add: circNext_def)

lemma circNext_nil[simp]: "circNext [] = []"
by (simp)

lemma circNexts_nil_iff[simp]: "ALL s. (circNexts N s = []) = (s = [])"
by (induct_tac N, auto)

lemma circNexts_nil[simp]: "ALL s. (circNexts N [] = [])"
by (induct_tac N, auto)

(* length *)

lemma length_lineNext[simp]: "length (lineNext s x) = length s"
by (induct_tac s, auto)

lemma length_circNext[simp]: "length (circNext s) = length s"
by (simp add: circNext_def)

lemma length_circNexts[simp]: "ALL s. length (circNexts N s) = length s"
by (induct_tac N, auto)

(* even *)

lemma even_fill: "even (fill n)"
by (auto simp add: allEven_def fill_def)

lemma fill_div_times[simp]: "fill n div 2 * 2 = fill n"
apply (insert even_fill[of n])
apply (simp add: even_EX)
(* apply (force) *)
done

lemma lineNext_even[simp]: "allEven (lineNext s nn)"
apply (induct_tac s)
apply (auto simp add: allEven_def fill_def)
done

lemma circNext_even[simp]: "allEven (circNext s)"
by (simp add: circNext_def)

lemma circNexts_even_lm: "ALL s. allEven s --> allEven (circNexts N s)"
by (induct_tac N, auto)

lemma circNexts_even[simp]: "allEven s ==> allEven (circNexts N s)"
by (simp add: circNexts_even_lm)

(* sum *)

lemma circNexts_sum:
   "ALL s. circNexts (N1 + N2) s = circNexts N1 (circNexts N2 s)"
by (induct_tac N2, auto)

(* ------------------------------------------------- *
               lemmas on min and max
 * ------------------------------------------------- *)

(* max and min *)

lemma maxList_max[simp]: "ALL n:set s. n <= maxList s"
by (induct_tac s, auto)

lemma maxList_max_nth[simp]: "ALL i. i<length s --> s!i <= maxList s"
by (induct_tac s, auto)

lemma minList_min[simp]: "ALL n:set s. minList s <= n"
by (induct_tac s, auto)

lemma maxList_min_nth[simp]: "ALL i. i<length s --> minList s <= s!i"
by (induct_tac s, auto)

(* exist *)

lemma maxList_exist: "s ~= [] --> (maxList s : set s)"
by (induct_tac s, auto)

lemma maxList_exist_nth: "s ~= [] --> (EX i. i<length s & s!i = maxList s)"
by (induct_tac s, auto)

lemma minList_exist: "s ~= [] --> (minList s : set s)"
by (induct_tac s, auto)

lemma minList_exist_nth: "s ~= [] --> (EX i. i<length s & s!i = minList s)"
by (induct_tac s, auto)

(* basic *)

lemma minList_le_maxList: "minList s <= maxList s"
by (induct_tac s, auto)

lemma maxList_single[simp]: "maxList[n] = n"
by (simp)

lemma minList_single[simp]: "minList[n] = n"
by (simp)

lemma minList_le_forall: 
  "t ~= [] --> ((m <= minList t) = (ALL n:(set t). m<=n))"
by (induct_tac t, auto)

lemma minList_less_forall: 
  "t ~= [] --> ((m < minList t) = (ALL n:(set t). m<n))"
by (induct_tac t, auto)

lemma maxList_le_forall:
  "(maxList t <= m) = (ALL n:set t. n <= m)"
by (induct_tac t, auto)

lemma maxList_less_forall:
  "t ~= [] --> (maxList t < m) = (ALL n:set t. n < m)"
by (induct_tac t, auto)

(* fill *)

lemma even_le_fill[simp]: "even n ==> (fill m <= n) = (m <= n)"
apply (simp add: fill_def)
apply (simp add: even_EX)
apply (elim conjE exE)
apply (auto)
apply (drule_tac x="ma" in spec)
apply (auto)
done

lemma even_fill_le: "n <= m ==> (n <= fill m)"
by (simp add: fill_def)

lemma even_fill_less[simp]: "even n ==> (n < fill m) = (n < m)"
apply (simp add: fill_def)
apply (simp add: even_EX)
apply (elim conjE exE)
apply (auto)
apply (drule_tac x="ma" in spec)
apply (auto)
done

(* even *)

lemma allEven_maxList[simp]: "(ALL s:set s. even s) ==> even (maxList s)"
apply (case_tac "s=[]", simp)
apply (insert maxList_exist[of s], simp)
done

lemma allEven_minList[simp]: "(ALL s:set s. even s) ==> even (minList s)"
apply (case_tac "s=[]", simp)
apply (insert minList_exist[of s], simp)
done

lemma alleven_hd: "allEven (n#s) = (even n & allEven(s))"
by (simp add: allEven_def)

lemma allEven_div[simp]: "[| s ~= [] ; allEven s |] ==> 2 * (hd s div 2) = hd s"
apply (simp add: allEven_def even_EX)
(*
apply (drule_tac x="hd s" in bspec)
apply (auto)
*)
done

lemma allEven_hd: "[| s ~= [] ; allEven s |] ==> even (hd s)"
by (auto simp add: allEven_def)

(* stable *)

lemma stable_min_max:
  "stableList s = (minList s = maxList s)"
apply (simp add: stableList_def)
apply (rule)

 (* => *)
 apply (rule order_antisym)
 apply (simp add: minList_le_maxList)
 apply (simp only: maxList_le_forall)
 apply (force)

 (* <= *)
 apply (intro ballI)
 apply (erule order_antisymE)
  apply (simp only: maxList_le_forall)
  apply (drule_tac x="n" in bspec)
  apply (simp)
  apply (rule order_antisym)
  apply (simp_all)
done

lemma stable_lineNext_lm:
  "(ALL n:set s. n=2*N) --> (lineNext s N = s)"
apply (induct_tac s)
apply (simp)
apply (simp add: allEven_def)
apply (auto simp add: even_EX)
apply (simp add: fill_def)
apply (drule_tac x="hd list" in bspec)
apply (simp_all add: fill_def)
done                          

lemma stable_lineNext:
  "[| allEven s ; stableList s |] ==> lineNext s (hd s div 2) = s"
apply (case_tac "s=[]", simp)
apply (insert stable_lineNext_lm[of s "(minList s) div 2"])
(* modified for Isabelle 2016 *)
apply (drule mp)
apply (simp add: allEven_def stableList_def)
apply (simp add: allEven_def stableList_def)
apply (auto simp add: even_EX)
apply (rotate_tac 1)
apply (drule_tac x="hd s" in bspec, simp)
apply (simp)
done

lemma stable_circNext:
  "[| allEven s ; stableList s |] ==> circNext s = s"
by (simp add: circNext_def stable_lineNext)

lemma stable_circNexts:
  "[| allEven s ; stableList s |] ==> circNexts N s = s"
apply (induct_tac N)
by (simp_all add: stable_circNext)

(* howMany *)

lemma howMany_zero:
   "(howMany m s = 0) = (ALL n:(set s). m ~= n)"
by (induct_tac s, auto)

lemma less_minList_howMany_zero:
   "[| s ~= [] ; M < minList s |] ==> howMany M s = 0"
apply (simp add: howMany_zero)
apply (simp add: minList_less_forall)
apply (auto)
done

(* makeStableList *)

lemma makeStableList_nil[simp]: "(makeStableList l n = []) = (l=0)"
by (induct_tac l, auto)

lemma tl_makeStableList_nil[simp]: "(tl (makeStableList l n) = []) = (l <= Suc 0)"
by (induct_tac l, auto)

lemma makeStableList_hd[simp]: "0<l --> hd (makeStableList l n) = n"
by (induct_tac l, auto)

lemma set_makeStableList[simp]: "0<l --> set (makeStableList l n) = {n}"
by (induct_tac l, auto)

lemma stableList_makeStableList_lm: "stableList (makeStableList l n)"
by (induct_tac l, auto simp add: stableList_def)

lemma stableList_makeStableList[simp]: 
  "s = makeStableList l n ==> stableList s"
by (simp add: stableList_makeStableList_lm)

lemma allEven_makeStableList[simp]: "even n ==> allEven (makeStableList l n)"
by (induct_tac l, auto simp add: allEven_def)

lemma makeStableList_hd_stableList_if:
   "ALL s. (length s = l & stableList s) --> s = makeStableList l (hd s)"
apply (induct_tac l, auto)
apply (case_tac "s=[]", simp)
apply (auto simp add: not_nil_EX)
apply (case_tac "t=[]", simp)
apply (auto simp add: not_nil_EX stableList_def)
apply (drule_tac x="a # ta" in spec)
apply (auto simp add: stableList_def)
done

lemma makeStableList_hd_stableList_only_if:
   "ALL s. s=makeStableList l (hd s) --> length s = l"
apply (induct_tac l)
apply (simp)
apply (intro allI impI)
apply (simp)
apply (case_tac "s=[]", simp)
apply (simp add: not_nil_EX)
apply (elim conjE exE)
apply (drule_tac x="t" in spec)
apply (simp)
apply (drule mp)
apply (case_tac "n=0", simp)
apply (simp_all)
done

lemma makeStableList_hd_stableList:
   "(s=makeStableList l (hd s)) = (length s = l & stableList s)"
apply (rule)
apply (simp add: makeStableList_hd_stableList_only_if)
apply (simp add: makeStableList_hd_stableList_if)
done

(* ------------------------------------------------- *
             lemmas on line, min and max
 * ------------------------------------------------- *)

(* line max <= *)

lemma lineNext_max_le_lm:
  "ALL n. 
   (s ~= [] & allEven s & even M & (ALL n:set s. n <= M) & 2*nn <= M & 
    n:set (lineNext s nn))
    --> n <= M"
apply (induct_tac s)
apply (simp)

apply (intro allI ballI impI)
apply (simp)
apply (case_tac "list = []")
 apply (simp)
 apply (simp add: even_EX allEven_def)
 apply (force)

 apply (simp add: allEven_def even_EX)
 apply (elim disjE conjE exE)
  apply (rotate_tac 1)
  apply (drule_tac x="hd list" in bspec, simp)
  apply (drule_tac x="hd list" in bspec, simp)
  apply (auto)
done

lemma lineNext_max_le:
   "[| s ~= [] ; allEven s ; even M ; ALL n:set s. n <= M ; 2*nn <= M ;
       n:set (lineNext s nn) |]
    ==> n <= M"
apply (insert lineNext_max_le_lm[of s M nn])
apply (drule_tac x="n" in spec)
apply (drule mp)
apply (simp_all)
done

lemma lineNext_maxList_le:
   "[| s ~= [] ; allEven s ; 2*nn <= maxList s ; n:set (lineNext s nn) |]
    ==> n <= maxList s"
apply (rule lineNext_max_le)
apply (simp_all add: allEven_def)
done

(* line min <= *)

lemma lineNext_min_le_lm:
  "ALL n. 
   (s ~= [] & allEven s & even M & (ALL n:set s. M <= n) & M <= 2*nn &
    n:set (lineNext s nn)) 
   --> M <= n"
apply (induct_tac s)
apply (simp)

apply (intro allI ballI impI)
apply (simp)
apply (case_tac "list = []")
 apply (simp)
 apply (simp add: even_EX allEven_def)
 apply (elim conjE exE)
 apply (simp add: fill_def)

 apply (simp add: allEven_def even_EX)
 apply (elim disjE conjE exE)
  apply (rotate_tac 1)
  apply (drule_tac x="hd list" in bspec, simp)
  apply (drule_tac x="hd list" in bspec, simp)
  apply (auto)
  apply (simp add: fill_def)
done

lemma lineNext_min_le:
   "[| s ~= [] ; allEven s ; even M ; ALL n:set s. M <= n ; M <= 2*nn ; 
       n:set (lineNext s nn) |]
    ==> M <= n"
apply (insert lineNext_min_le_lm[of s M nn])
apply (drule_tac x="n" in spec)
apply (drule mp)
apply (simp_all)
done

lemma lineNext_minList_le:
   "[| s ~= [] ; allEven s ; minList s <= 2*nn ;
       n:set (lineNext s nn) |]
    ==> minList s <= n"
apply (rule lineNext_min_le)
apply (simp_all add: allEven_def)
done

(* line min < *)

lemma lineNext_min_less_lm:
  "ALL i. 
   (s ~= [] & allEven s & even M & (ALL n:set s. M <= n) & M <= 2*nn &
    Suc i < length s & s!i = M & M < s!(Suc i))
    --> M < (lineNext s nn) ! i"
apply (induct_tac s)
apply (simp)
apply (intro ballI allI impI)
apply (elim conjE exE)
apply (simp)
apply (insert nat_zero_or_Suc)
apply (rotate_tac -1)
apply (drule_tac x="i" in spec)
apply (elim disjE conjE exE)
apply (simp add: nth_hd)
apply (simp add: allEven_def even_EX)
apply (elim conjE exE)
apply (simp)
apply (rotate_tac -2)
apply (drule_tac x="hd list" in bspec, simp)
apply (elim conjE exE)
apply (simp)

apply (auto simp add: allEven_def)
done

lemma lineNext_min_less:
  "[| s ~= [] ; allEven s ; even M ; ALL n:set s. M <= n ; M <= 2*nn ;
      Suc i < length s ; s!i = M ; M < s!(Suc i) |]
    ==> M < (lineNext s nn) ! i"
by (insert lineNext_min_less_lm[of s M nn], simp)

lemma lineNext_minList_less:
  "[| s ~= [] ; allEven s ; minList s <= 2*nn ;
      Suc i < length s ; s!i = minList s ; minList s < s!(Suc i) |]
    ==> minList s < (lineNext s nn) ! i"
apply (rule lineNext_min_less)
apply (simp_all add: allEven_def)
done

(* last *)

lemma lineNext_min_less_last_sublm:
  "s ~= [] & last s < a --> last s < last (lineNext s a)"
by (induct_tac s, auto simp add: fill_def)

lemma lineNext_min_less_last_lm:
  "(s ~= [] & allEven s & (ALL n:set s. M <= n) 
    & M = last s & M < 2*nn )
        --> last s < last (lineNext s nn)"
apply (induct_tac s)
apply (simp_all add: lineNext_min_less_last_sublm)
apply (intro conjI impI)
apply (simp_all)
apply (simp add: allEven_def even_EX)
apply (elim conjE exE)
apply (simp add: fill_def)
apply (auto simp add: allEven_def)
done

lemma lineNext_min_less_last:
  "[| s ~= [] ; allEven s ; ALL n:set s. M <= n ;
      last s = M ; M < 2*nn |]
   ==> M < last (lineNext s nn)"
by (insert lineNext_min_less_last_lm[of s M nn], simp)

lemma lineNext_minList_less_last:
  "[| s ~= [] ; allEven s ; last s = minList s ; minList s < 2*nn |]
   ==> minList s < last (lineNext s nn)"
by (simp add: lineNext_min_less_last)

(* other less *)

lemma lineNext_min_other_less_lm:
  "ALL i. 
   (s ~= [] & allEven s & even M & (ALL n:set s. M <= n) & M <= 2*nn &
    i < length s & M < s!i)
    --> M < (lineNext s nn) ! i"
apply (induct_tac s)
apply (simp_all)
apply (intro conjI impI)
apply (simp add: fill_def)
apply (simp add: allEven_def even_EX)
apply (elim conjE exE)
apply (simp)

apply (intro allI impI)
apply (simp)
apply (insert nat_zero_or_Suc)
apply (rotate_tac -1)
apply (drule_tac x="i" in spec)
apply (elim disjE conjE exE)
apply (simp)
apply (simp add: allEven_def even_EX)
apply (elim conjE exE)
apply (rotate_tac -3)
apply (drule_tac x="hd list" in bspec, simp)
apply (drule_tac x="hd list" in bspec, simp)
apply (elim conjE exE)
apply (simp)

apply (simp add: allEven_def)
done

lemma lineNext_min_other_less:
  "[| s ~= [] ; allEven s ; even M ; ALL n:set s. M <= n ; M <= 2*nn ;
      i < length s ; M < s!i |]
   ==> M < (lineNext s nn) ! i"
by (simp add: lineNext_min_other_less_lm)

lemma lineNext_minList_other_less:
  "[| s ~= [] ; allEven s ; minList s <= 2*nn ;
      i < length s ; minList s < s!i |]
   ==> minList s < (lineNext s nn) ! i"
apply (rule lineNext_min_other_less)
apply (simp_all add: allEven_def)
done

(* ------------------------------------------------- *
              lemmas on circ, min and max
 * ------------------------------------------------- *)

(* max le *)

lemma circNext_maxList_le:
  "[| s ~= [] ; allEven s ; n:set (circNext s) |]
   ==> n <= maxList s"
apply (simp add: circNext_def)
apply (rule lineNext_maxList_le[of _ "(hd s div 2)"])
apply (simp_all)
done

lemma maxList_circNext_le:
  "[| s ~= [] ; allEven s |]
   ==> maxList (circNext s) <= maxList s"
apply (simp add: maxList_le_forall)
apply (auto simp add: circNext_maxList_le)
done

(* min le *)

lemma circNext_minList_le:
  "[| s ~= [] ; allEven s ; n:set (circNext s) |]
   ==> minList s <= n"
apply (simp add: circNext_def)
apply (rule lineNext_minList_le[of _ "(hd s div 2)"])
apply (simp_all)
done

lemma minList_circNext_le:
  "[| s ~= [] ; allEven s |]
   ==> minList s <= minList (circNext s)"
apply (simp add: minList_le_forall)
apply (auto simp add: circNext_minList_le)
done

(* min less *)

lemma circNext_minList_less:
  "[| s ~= [] ; allEven s ; 
      i<length s ; s!i=minList s ; 
      (Suc i = length s & minList s < hd s) | 
      (Suc i < length s & minList s < s ! Suc i) |]
   ==> minList s < (circNext s)!i"
apply (simp add: circNext_def)
apply (case_tac "Suc i < length s")
apply (insert lineNext_minList_less[of s "(hd s div 2)" i])
apply (simp add: allEven_def even_EX)

apply (case_tac "Suc i = length s")
apply (insert lineNext_minList_less_last[of s "(hd s div 2)"])
apply (simp add: nth_last)

apply (auto)
done

lemma circNext_minList_other_less:
  "[| s ~= [] ; allEven s ; i<length s ; minList s < s!i |]
   ==> minList s < (circNext s)!i"
apply (simp add: circNext_def)
apply (rule lineNext_minList_other_less)
apply (auto)
done

(* ------------------------------------------------- *
            lemmas on circNexts, min, and max
 * ------------------------------------------------- *)

lemma maxList_circNexts_le_lm:
  "ALL s. (s ~= [] & allEven s)
    --> maxList (circNexts N s) <= maxList s"
apply (induct_tac N)
apply (auto)
apply (drule_tac x="circNext s" in spec)
apply (simp)
apply (rule order_trans)
apply (simp)
apply (simp add: maxList_circNext_le)
done

lemma maxList_circNexts_le:
  "[| s ~= [] ; allEven s |]
   ==> maxList (circNexts N s) <= maxList s"
by (simp add: maxList_circNexts_le_lm)

lemma minList_circNexts_le_lm:
  "ALL s. (s ~= [] & allEven s)
    --> minList s <= minList (circNexts N s)"
apply (induct_tac N)
apply (auto)
apply (drule_tac x="circNext s" in spec)
apply (simp)
apply (rule order_trans)
apply (simp_all)
apply (simp add: minList_circNext_le)
done

lemma minList_circNexts_le:
  "[| s ~= [] ; allEven s |]
   ==> minList s <= minList (circNexts N s)"
by (simp add: minList_circNexts_le_lm)

(* ----------------------------------------------------------- *
           to get the assumption of circ_minList_less
 * ----------------------------------------------------------- *)

declare minList.simps [simp del]

lemma unstable_exists_diff_one_lm:
  "ALL j. (j<length s & minList s < s!j) -->
   (EX i. i<length s & s ! i = minList s & 
         ((Suc i = length s & minList s < hd s) | 
          (Suc i < length s & minList s < s ! Suc i)))"
apply (induct_tac s)
apply (simp)

apply (intro allI impI)
apply (simp add: less_Suc)
apply (elim disjE conjE exE)

 (* 1 *)
 apply (subgoal_tac "minList (a # list) = minList list")      (* sub1 *)
  apply (simp)
  apply (case_tac "EX j. j<length list & minList list < list ! j")
   apply (simp)
   apply (elim exE)
   apply (rule_tac x="Suc i" in exI)
   apply (simp)
   apply (case_tac "list=[]")
    apply (force)
    apply (force)

   (* ~ EX j. j<length list & minList list < list ! j *)

   apply (rule_tac x="length list " in exI)
   apply (simp)
   apply (case_tac "list=[]", simp)
   apply (rule conjI)
    apply (rule disjI2)
    apply (rule_tac x="length list - 1" in exI)
    apply (force)
    apply (subgoal_tac "EX i. length list = Suc i")   (* sub2 *)
    apply (elim exE)
     apply (simp)
     apply (drule_tac x="i" in spec)
     apply (simp)

     apply (simp add: not_less)           (* <--- Isabelle 2008 *)
     (* apply (fold le_def)                  <--- Isabelle 2005 *)
     apply (rule le_antisym)              (* <--- Isabelle 2009-1 *)
     (* apply (rule le_anti_sym)             <--- Isabelle 2009 *)
     apply (simp)
     apply (simp)
   (* sub2 *)
    apply (rule_tac x="length list - 1" in exI)
    apply (simp)
 (* sub1 *)
  apply (case_tac "list=[]")
  apply (simp add: minList.simps)
  apply (simp add: minList.simps)
  apply (force)

 (* 2 *)
 apply (case_tac "minList list < a")
  apply (subgoal_tac "minList (a # list) = minList list")      (* sub3 *)
   apply (drule mp, force)
   apply (elim conjE exE)
   apply (rule_tac x="Suc i" in exI)
   apply (force)

 (* sub3 *)
  apply (case_tac "list=[]")
  apply (simp add: minList.simps)
  apply (simp add: minList.simps)

 apply (case_tac "minList list = a")
  apply (subgoal_tac "minList (a # list) = minList list")      (* sub4 *)
   apply (drule mp, force)
   apply (elim disjE conjE exE)
    apply (rule_tac x="0" in exI)
    apply (case_tac "list=[]")
    apply (simp)
    apply (simp add: nth_hd)

    apply (rule_tac x="Suc i" in exI)
    apply (simp)

 (* sub4 *)
  apply (case_tac "list=[]")
  apply (simp add: minList.simps)
  apply (simp add: minList.simps)

 apply (case_tac "a < minList list")
  apply (subgoal_tac "minList (a # list) = a")      (* sub5 *)
   apply (rule_tac x="0" in exI)
   apply (case_tac "list=[]")
   apply (simp)
   apply (simp add: nth_hd)
   apply (rotate_tac -3)
   apply (erule contrapos_pp)
   apply (simp add: not_less)           (* <--- Isabelle 2008 *)
 (* apply (fold le_def)                  <--- Isabelle 2005 *)
   apply (subgoal_tac "minList list <= hd list")
   apply (rule order_trans)
   apply (simp (no_asm_simp))
   apply (simp)
   apply (simp)

 (* sub5 *)
  apply (case_tac "list=[]")
  apply (simp add: minList.simps)
  apply (simp add: minList.simps)

apply (simp)
done

declare minList.simps [simp add]

lemma unstable_exists_diff_one:
  "[| j<length s ; minList s < s!j |] ==>
   EX i. i<length s & s ! i = minList s & 
         ((Suc i = length s & minList s < hd s) | 
          (Suc i < length s & minList s < s ! Suc i))"
apply (insert unstable_exists_diff_one_lm[of s])
apply (drule_tac x="j" in spec)
apply (simp)
done

(* --- to increase the minList --- *)

lemma unstable_circNext_minList_less:
  "[| s ~= [] ; allEven s ; j < length s & minList s < s!j |]
   ==> EX i. i < length s & s!i=minList s & minList s < (circNext s)!i"
apply (insert unstable_exists_diff_one[of j s])
apply (simp)
apply (elim conjE exE)
apply (rule_tac x="i" in exI)
apply (simp add: circNext_minList_less)
done

(* ----------------------------------------------------------- *
                to decrease howMany (minList s)
 * ----------------------------------------------------------- *)

lemma Suc_length_list_EX:
 "(Suc (length s) = length t) = (EX b u. t = b#u & length s = length u)"
apply (induct_tac t)
apply (auto)
done

(*** howMany <= ***)

lemma howMany_le_lm:
  "ALL s t j. (length s = length t &
              (ALL i. (i<length t & M ~= s!i) --> M ~= t!i))
   --> howMany M t <= howMany M s"
apply (rule)
apply (induct_tac s)
apply (simp)
apply (intro allI impI)
apply (simp add: Suc_length_list_EX)
apply (elim conjE exE)
apply (drule_tac x="u" in spec)
apply (auto)
done

lemma howMany_le:
  "[| length s = length t ;
      !!i. [| i<length t ; M ~= s!i |] ==> M ~= t!i |]
   ==> howMany M t <= howMany M s"
by (simp add: howMany_le_lm)

(*** howMany < ***)

lemma howMany_less_lm:
  "ALL s t j. (length s = length t &
              (ALL i. (i<length t & M ~= s!i) --> M ~= t!i) &
               j < length t & s!j=M & M<t!j)
   --> howMany M t < howMany M s"
apply (rule)
apply (induct_tac s)
apply (simp)
apply (intro allI impI)
 apply (simp add: Suc_length_list_EX)
 apply (elim conjE exE)
 apply (intro conjI impI)

 (* new hd s = M *)
  apply (case_tac "j=0")
   apply (simp add: less_Suc_eq_le)
   apply (rule howMany_le)
   apply (simp)
   apply (drule_tac x="Suc i" in spec)
   apply (simp)
 
  (* j~=0 *)
   apply (drule_tac x="u" in spec)
   apply (drule mp)
    apply (simp)
    apply (intro conjI allI impI)
     apply (drule_tac x="Suc i" in spec)
     apply (simp)

     apply (simp add: zero_less_EX)
     apply (elim exE)
     apply (rule_tac x="m" in exI)
     apply (simp)
    apply (force)

 (* new hd s ~= M *)
 apply (simp add: less_Suc)
 apply (elim disjE conjE exE, simp)
 apply (drule_tac x="u" in spec)

 apply (drule mp)
  apply (simp)
   apply (intro conjI allI impI)
   apply (drule_tac x="Suc i" in spec)
   apply (simp)

   apply (rule_tac x="m" in exI)
   apply (simp)
  apply (force)
done

lemma howMany_less:
  "[| length s = length t ;
      ALL i. (i<length t & M ~= s!i) --> M ~= t!i ;
      EX j. j < length t & s!j=M & M<t!j |]
   ==> howMany M t < howMany M s"
apply (insert howMany_less_lm[of M])
apply (drule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
apply (erule exE)
apply (rotate_tac -2)
apply (drule_tac x="j" in spec)
apply (simp)
done

(*** howMany circNext ***)

lemma howMany_circNext_less:
  "[| s ~= [] ; allEven s ; j < length s ; minList s < s!j |]
   ==> howMany (minList s) (circNext s) < howMany (minList s) s"
apply (rule howMany_less)
apply (simp_all)
apply (intro allI impI)
 apply (elim conjE)
 apply (subgoal_tac "minList s < circNext s ! i", simp)
 apply (rule circNext_minList_other_less)
 apply (simp_all)
 apply (simp add: order_less_le)
 apply (rule unstable_circNext_minList_less[of s j])
 apply (simp_all)
done

(* ----------------------------------------------------------- *
                     to increase minList
 * ----------------------------------------------------------- *)

lemma minList_circNext_less_lm:
  "ALL k s. (s ~= [] & allEven s & i < length s & minList s < s!i &
           howMany (minList s) s <= k)
   --> (EX N. minList s < minList (circNexts N s))"
apply (rule)
apply (induct_tac k)
apply (intro allI impI)

(* k=0 *)
 apply (rule_tac x="0" in exI)
 apply (simp add: howMany_zero)
 apply (elim conjE)
 apply (drule_tac x="minList s" in bspec)
 apply (simp_all add: minList_exist)

(* step *)
apply (intro allI impI)
apply (drule_tac x="circNext s" in spec)
apply (simp)

 apply (case_tac "minList (circNext s) = minList s ")
 apply (drule mp)
  apply (simp)
  apply (elim conjE exE)
  apply (simp add: circNext_minList_other_less)
  apply (subgoal_tac "howMany (minList s) (circNext s) < howMany (minList s) s")
   apply (force)
  apply (simp add: howMany_circNext_less)
 apply (simp)
 apply (elim conjE exE)
 apply (rule_tac x="Suc N" in exI)
 apply (simp)

 (* minList (circNext s) ~= minList s *)
apply (rule_tac x="Suc 0" in exI)
apply (simp add: order_less_le minList_circNext_le)
done

lemma minList_circNext_less:
  "[| s ~= [] ; allEven s ; i < length s ; minList s < s!i |]
   ==> (EX N. minList s < minList (circNexts N s))"
apply (insert minList_circNext_less_lm[of i])
apply (erule exchange_forall_orderE)
apply (drule_tac x="s" in spec)
apply (drule_tac x="howMany (minList s) s" in spec)
apply (simp)
done

(* ----------------------------------------------------------- *
                    eventually stable
 * ----------------------------------------------------------- *)

lemma circNexts_eventually_stable_lm:
  "ALL k s i.
   (s ~= [] & allEven s & i < length s & minList s < s!i &
    maxList s <= minList s + k)
   --> (EX N. stableList(circNexts N s))"
apply (simp add: stable_min_max)
apply (rule)
apply (induct_tac k)

(* base *)
 apply (intro allI impI)
 apply (rule_tac x="0" in exI)
 apply (rule order_antisym)
 apply (simp add: minList_le_maxList)
 apply (force)

(* step *)
 apply (intro allI impI)
 apply (subgoal_tac "(EX N. minList s < minList (circNexts N s))")
 apply (elim exE conjE)
 apply (case_tac "N=0", simp)
 apply (case_tac "EX i. i < length s & minList (circNexts N s) < circNexts N s ! i")
  apply (elim exE conjE)
  apply (drule_tac x="circNexts N s" in spec)
  apply (simp)

  apply (drule mp)
   apply (rule_tac x="ia" in exI)
   apply (simp)
   apply (rule order_trans)
    apply (rule maxList_circNexts_le)
    apply (simp_all)
  apply (erule exE)
  apply (rule_tac x="Na + N" in exI)
  apply (simp add: circNexts_sum)

 (* ~ EX i. i < length s & minList (circNexts N s) < circNexts N s ! i *)
 apply (simp add: not_less)           (* <--- Isabelle 2008 *)
(* apply (fold le_def)                  <--- Isabelle 2005 *)
 apply (rule_tac x="N" in exI)
 apply (rule order_antisym)
  apply (simp add: minList_le_maxList)
  apply (simp add: maxList_le_forall)
  apply (intro ballI impI)
  apply (simp add: in_set_nth)
  apply (elim conjE exE)
  apply (rotate_tac -3)
  apply (drule_tac x="ia" in spec)
  apply (simp)

apply (elim conjE exE)
apply (simp add: minList_circNext_less)
done

lemma circNexts_eventually_stable:
  "[| s ~= [] ; allEven s |] ==> EX N. stableList(circNexts N s)"

apply (case_tac "ALL i. i < length s --> minList s = s!i")
 apply (rule_tac x="0" in exI)
 apply (simp add: stable_min_max)
 apply (rule order_antisym)
  apply (simp add: minList_le_maxList)
  apply (simp add: maxList_le_forall)
  apply (intro ballI impI)
  apply (simp add: in_set_nth)
  apply (force)

 (* ~ (ALL i. i < length s --> minList s = s!i) *)
apply (simp)
apply (elim conjE exE)
apply (insert circNexts_eventually_stable_lm)
apply (erule exchange_forall_orderE)
apply (drule_tac x="s" in spec)
apply (drule_tac x="maxList s - minList s" in spec)
apply (drule_tac x="i" in spec)
apply (simp add: minList_le_maxList)
apply (simp add: order_less_le)
done

end
