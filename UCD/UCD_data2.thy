           (*-------------------------------------------*
            |       Uniform Candy Distribution          |
            |                                           |
            |           November 2007 for Isabelle 2005 |
            |           November 2008 for Isabelle 2008 |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory UCD_data2
imports UCD_data1
begin

(*****************************************************************

         1. 

 *****************************************************************)

(*********************************************************
          preliminary (functions for updates)
 *********************************************************)

datatype Att = AttL "nat*nat" | AttC nat | AttR nat

lemma inj_Att[simp]: "inj AttL" "inj AttC" "inj AttR"
by (simp_all add: inj_on_def)

lemma Att_or:
  "ALL a. (EX n x. a = AttL (n, x)) | (EX n. a = AttC n) | (EX n. a = AttR n)"
apply (rule)
apply (induct_tac a)
apply (auto)
done

lemma AttR_EX[simp]:
  "((ALL n x. a ~= AttL (n, x)) & (ALL n. a ~= AttC n)) = (EX n. a = AttR n)"
apply (induct_tac a)
apply (auto)
done

(* functions *)


primrec
  getNat   :: "Att => nat"
where
  "getNat (AttL nx) = fst(nx)"
 |"getNat (AttC n) = n"
 |"getNat (AttR n) = n"

(*
consts
  updateR  :: "(Att list * nat) => Att list"
recdef updateR "measure (%sx. length (fst(sx)))"
  "updateR ([],x) = []"
  "updateR ((AttL (n,y))#s,x) = [AttR 0, AttC 0]"
  "updateR ((AttC n)#s,x) = [AttR 0, AttC 0]"
  "updateR ([AttR n],x) = [AttR (fill(n + x) div 2)]"
  "updateR ((AttR n)#s,x) = 
     (AttR (fill(n + getNat(hd(updateR(s,x)))) div 2)) # updateR(s,x)"
*)

fun
  updateR  :: "(Att list * nat) => Att list"
where
  "updateR ([],x) = []"
 |"updateR ((AttL (n,y))#s,x) = [AttR 0, AttC 0]"
 |"updateR ((AttC n)#s,x) = [AttR 0, AttC 0]"
 |"updateR ([AttR n],x) = [AttR (fill(n + x) div 2)]"
 |"updateR ((AttR n)#s,x) = 
     (AttR (fill(n + getNat(hd(updateR(s,x)))) div 2)) # updateR(s,x)"

fun
  nextR    :: "(Att list * nat) => Att list"
where
  "nextR ([],x) = []"
 |"nextR ([AttL (n,y)],x) = [AttR 0, AttC 0]"
 |"nextR ((AttL (n,y))#s,x) = (AttL (n,y))# nextR(s,x)"
 |"nextR ([AttC n],x) = [AttL (n,x)]"
 |"nextR ((AttC n)#s,x) = (AttL (n, getNat(hd(updateR(s,x))) ))#updateR(s,x)"
 |"nextR ([AttR n],x) = [AttC (fill(n + x))]"
 |"nextR ((AttR n)#s,x) = 
     (AttC (fill(n + getNat(hd(updateR(s,x))) ))) # updateR(s,x)"

fun
  nextLhd :: "(nat*(Att list)) => Att"
where
  "nextLhd (nz,[])        = (AttC nz)"
 |"nextLhd (nz,(AttR m)#s) = (AttC nz)"
 |"nextLhd (nz,(AttC m)#s)     = (AttL (nz,(m div 2)))"
 |"nextLhd (nz,(AttL (m,y))#s) = (AttL (nz,(m div 2)))"

fun
  nextL    :: "Att list => Att list"
where
  "nextL ([]) = []"
 |"nextL ((AttR n)#s) = [AttR 0, AttC 0]"
 |"nextL ((AttC n)#s) = (AttR (n div 2))#s"
 |"nextL ([AttL (n,z)]) = [AttC (fill(n div 2 + z))]"
 |"nextL ((AttL (n,z))#(AttL (m,y))#s) = AttL (fill(n div 2 + z), m div 2)#nextL((AttL (m,y))#s)"
 |"nextL ((AttL (n,z))#(AttC m)#s) = AttL (fill(n div 2 + z), m div 2)#(AttR (m div 2))#s"
 |"nextL ((AttL (n,z))#(AttR m)#s) = AttC (fill(n div 2 + z)) # (AttR m)#s"

primrec
  guardL   :: "Att list => bool"
where
 "guardL([]) = False"
|"guardL(a#s) = ((EX n x. a=AttL (n,x)) | (EX n. a=AttC n))"

fun
  guardR   :: "Att list => bool"
where
  "guardR([]) = False"
 |"guardR([a]) = ((EX n. a=AttC n) | (EX n. a=AttR n))"
 |"guardR(a#s) = guardR(s)"

definition
  nextLR   :: "Att list => Att list"
where
 nextLR_def: "nextLR(s) == nextL(nextR(s,getNat(hd(s)) div 2))"

fun
  toStbOne :: "Att list => Att list"

where
  "toStbOne ([]) = []"
 |"toStbOne ([a]) = [a]"
 |"toStbOne ((AttL (n,z))#s) = (AttL (n,z))#s"
 |"toStbOne ((AttC n)#(AttL (m,z))#s) = (AttL (n, m div 2)) # nextL((AttL (m,z))#s)"
 |"toStbOne ((AttC n)#(AttC m)#s)     = (AttL (n, m div 2)) # nextL((AttC m)#s)"
 |"toStbOne ((AttC n)#(AttR m)#s)     = (AttC n)#(AttR m)#s"

 |"toStbOne ([AttR n, AttL (m,z)]) = 
        [AttL (fill (n + m div 2), fill (m div 2 + z) div 2),
         AttR (fill (m div 2 + z) div 2)]"

 |"toStbOne ((AttR n)#(AttL (m,z))#(AttL (na, x))#sa) = 
        AttL (fill (n + m div 2), fill (m div 2 + z) div 2) #
        nextL (AttL (fill (m div 2 + z), na div 2) # nextL (AttL (na, x) # sa))"

 |"toStbOne ((AttR n)#(AttL (m,z))#(AttC na)#sa) = 
        AttL (fill (n + m div 2), fill (m div 2 + z) div 2) #
        AttC (fill (fill (m div 2 + z) div 2 + na div 2)) # AttR (na div 2) # sa"

 |"toStbOne ((AttR n)#(AttL (m,z))#(AttR na)#sa) = 
        AttL (fill (n + m div 2), fill (m div 2 + z) div 2) #
        AttR (fill (m div 2 + z) div 2) # AttR na # sa"

 |"toStbOne ((AttR n)#(AttC m)#s) = (AttC (fill(n + m div 2))) # nextL((AttC m)#s)"
 |"toStbOne ((AttR n)#(AttR m)#s) = (AttR n)#(AttR m)#s"

primrec
  toStb    :: "Att list => Att list"
where
  "toStb  ([]) = []"
 |"toStb (a#s) = toStbOne(a#(toStb(s)))"

(* --- test --- *)

lemma test_updateR: 
 "updateR ([AttR 2, AttR 4, AttR 0],8) = [AttR 3, AttR 4, AttR 4]"
by (simp add: fill_def)

lemma test_toStbOne:
  "toStbOne ([AttR 2, AttL (4,2), AttC 0, AttR 6]) = 
            [AttL (4,2), AttC 2, AttR 0, AttR 6]"
by (simp  add: fill_def)

(*   lemmas    *)

lemma guardR_last: 
  "guardR s = (s~=[] & ((EX n. last s =AttC n) | (EX n. last s =AttR n)))"
apply (induct_tac s)
apply (simp)
apply (insert list_nil_or_unnil)
apply (drule_tac x="list" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma guardL_hd:
  "guardL s = (s~=[] & ((EX n x. hd s =AttL (n,x)) | (EX n. hd s =AttC n)))"
apply (induct_tac s)
apply (simp_all)
done

lemma guardR_AttL[simp]: "guardR (AttL sx # t) = guardR t"
apply (induct_tac t)
by (simp_all)

(*********************************************************
                       L C R
 *********************************************************)

primrec
 ChkL    :: "Att list => bool"
where
 "ChkL    [] = True"
|"ChkL (c#t) = ((EX x. c = AttL x) & ChkL t)"

primrec
 ChkC    :: "Att list => bool"
where
 "ChkC    [] = True"
|"ChkC (c#t) = ((EX x. c = AttC x) & ChkC t)"

primrec
 ChkR    :: "Att list => bool"
where
 "ChkR    [] = True"
|"ChkR (c#t) = ((EX x. c = AttR x) & ChkR t)"

primrec
 ChkCR   :: "Att list => bool"
where
 "ChkCR   []  = True"
|"ChkCR (c#t) = (((EX x. c = AttC x) & ChkR t) | ChkR (c#t))"

primrec
 ChkLCR  :: "Att list => bool"
where
 "ChkLCR   []  = True"
|"ChkLCR (c#t) = (((EX x. c = AttL x) & ChkLCR t) | ChkCR (c#t))"

(* ---------- sub 1 ---------- *)

lemma nextL_one_not_nil[simp]: "nextL ([a]) ~= []"
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (auto)
done

lemma nextL_not_nil[simp]: "nextL (a#s) ~= []"
apply (induct_tac s)
apply (auto)
apply (insert Att_or)
apply (frule_tac x="a" in spec)
apply (drule_tac x="aa" in spec)
apply (auto)
done

lemma nextR_not_nil[simp]: "nextR (a#s,x) ~= []"
apply (induct_tac s)
apply (auto)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (auto)

apply (frule_tac x="a" in spec)
apply (drule_tac x="aa" in spec)
apply (auto)
done

lemma tl_toStbOne_not_nil:
 "(tl (toStbOne s) ~= []) = (EX a1 a2 t. s=a1#a2#t)"
apply (insert list_nil_or_unnil)
apply (drule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert list_nil_or_unnil)
apply (drule_tac x="sa" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
apply (insert Att_or)
apply (frule_tac x="a" in spec)
apply (drule_tac x="aa" in spec)
apply (elim disjE conjE exE)
apply (simp_all)
apply (insert list_nil_or_unnil)
apply (drule_tac x="saa" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="ab" in spec)
apply (elim disjE conjE exE)
apply (simp_all)
done

lemma ChkLCR_nextL[simp]: "guardL s --> ChkLCR (nextL s) = ChkLCR s"
apply (induct_tac s)
apply (simp)
apply (insert list_nil_or_unnil)
apply (drule_tac x="list" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE exE)
apply (simp_all)

apply (frule_tac x="a" in spec)
apply (drule_tac x="aa" in spec)
apply (elim disjE conjE exE)
apply (simp_all)
done

lemma ChkLCR_nextR[simp]: "guardR s --> ChkLCR (nextR (s,x)) = ChkLCR s"
apply (induct_tac s)
apply (simp)
apply (insert list_nil_or_unnil)
apply (drule_tac x="list" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE exE)
apply (simp_all)

apply (frule_tac x="a" in spec)
apply (drule_tac x="aa" in spec)
apply (elim disjE conjE exE)
apply (simp_all)

apply (insert list_nil_or_unnil)
apply (drule_tac x="s" in spec)
apply (elim disjE conjE exE)
apply (simp_all)
apply (drule_tac x="s" in spec)
apply (elim disjE conjE exE)
apply (simp_all)
done

lemma ChkLCR_AttL[simp]: "ChkLCR (AttL (n, x) # s) = ChkLCR s"
apply (insert list_nil_or_unnil)
apply (drule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma toStbOne_AttL[simp]: "toStbOne (AttL (n, x) # s) = AttL (n, x) # s"
apply (insert list_nil_or_unnil)
apply (drule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
done

lemma nextL_nextR_order[rule_format]: 
   "(t = [] | (guardL t & guardR t & ChkLCR t)) -->
    nextL (nextR (t, x)) = nextR (nextL t, x)"
apply (induct_tac t)
apply (simp)
apply (intro allI impI)
apply (simp)

apply (insert list_nil_or_unnil)
apply (drule_tac x="list" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE exE)
apply (simp_all)

apply (frule_tac x="a" in spec)
apply (drule_tac x="aa" in spec)
apply (insert list_nil_or_unnil)
apply (drule_tac x="s" in spec)
apply (auto)
done

lemma ChkR_ChkCR: "ChkR t --> ChkLCR t"
apply (induct_tac t)
apply (auto)
done

lemma guardR_hd: "guardR t --> guardR (a#t)"
apply (induct_tac t)
apply (simp_all)
done

lemma ChkR_guardR_AttR[simp]: "ALL n. ChkR s --> guardR (AttR n # s)"
apply (induct_tac s)
apply (auto)
done

lemma ChkR_guardR_AttC[simp]: "ALL n. ChkR s --> guardR (AttC n # s)"
apply (induct_tac s)
apply (auto)
done

lemma ChkLCR_guardR_next[simp]: "(ChkLCR t & t ~= []) --> guardR (nextL t)"
apply (induct_tac t)
apply (simp_all)
apply (insert list_nil_or_unnil)
apply (drule_tac x="list" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE exE)
apply (simp_all)
apply (frule_tac x="a" in spec)
apply (drule_tac x="aa" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma guardR_nextR_AttL[simp]:
 "guardR t ==> nextR (AttL (n, x) # t, z) = (AttL (n,x))# nextR(t,z)"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma nextL_AttL_nextR_AttC[simp]:
   "nextL (AttL (n, x) # nextR (AttC m # t, y))
    = AttL (fill(n div 2 + x), m div 2) # nextL(nextR (AttC m # t, y))"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma nextL_AttL_nextR_AttR[simp]:
   "nextL (AttL (n, x) # nextR (AttR m # t, y)) =
       AttL (fill (n div 2 + x), getNat (hd (updateR (AttR m # t, y))) ) #
       updateR (AttR m # t, y)"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma nextL_AttL_updateR[simp]:
   "nextL (AttL (n, x) # updateR (AttR m # t, y)) =
    AttC (fill (n div 2 + x)) # updateR (AttR m # t, y)"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE exE)
apply (simp_all)
done

(* --------------------lemma ------------------*)

lemma guardL_nextL_AttL[simp]: "guardL (nextL (AttL (n,x) # t))"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma nextL_AttL_nextL_AttL[simp]:
  "nextL (AttL (n,x) # nextL (AttL (m,y) # t)) =
   AttL (fill(n div 2 + x), fill(m div 2 + y) div 2) # nextL (nextL (AttL (m,y) # t))"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma ChkLCR_guardL_guardR_nextL[simp]:
  "[| ChkLCR t ; guardL t |] ==> guardR (nextL t)"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma ChkLCR_guardR_guardL_nextR[simp]:
  "[| ChkLCR t ; guardR t |] ==> guardL (nextR (t, x))"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE exE)
apply (simp_all)
apply (insert list_nil_or_unnil)
apply (drule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="aa" in spec)
apply (elim disjE exE)
apply (simp_all)
apply (drule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp)
apply (drule_tac x="aa" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma nextR_nextL_nextL_order_AttL: 
   "[| ChkLCR t ; guardR t |] ==> 
    nextR (nextL (nextL (AttL (n, x) # t)), y) =
    nextL (nextR (nextL (AttL (n, x) # t), y))"
apply (simp add: nextL_nextR_order[THEN sym])
done

lemma nextL_AttL_nextR_guardR[simp]:
  "[| ChkLCR t ; guardR t |] ==> 
   nextL (AttL (n, x) # nextR (t, y)) = 
   AttL (fill (n div 2 + x), getNat (hd (nextR (t, y))) div 2) # nextL (nextR (t, y))"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
apply (elim disjE conjE exE)
apply (simp_all)
apply (insert list_nil_or_unnil)
apply (drule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp_all)
apply (drule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma ChkR_ChkLCR_updateR[simp]: "ChkR s --> ChkLCR (updateR (s,x)) = ChkLCR s"
apply (induct_tac s)
apply (simp)
apply (insert list_nil_or_unnil)
apply (drule_tac x="list" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE exE)
apply (simp_all)

apply (frule_tac x="a" in spec)
apply (drule_tac x="aa" in spec)
apply (elim disjE conjE exE)
apply (simp_all)

apply (insert list_nil_or_unnil)
apply (drule_tac x="s" in spec)
apply (elim disjE conjE exE)
apply (simp_all)
done

lemma ChkR_ChkR_updateR[simp]: "ChkR s --> ChkR (updateR (s,x)) = ChkR s"
apply (induct_tac s)
apply (simp)
apply (insert list_nil_or_unnil)
apply (drule_tac x="list" in spec)
apply (auto)
done

(* ---- basic ---- *)

lemma ChkLCR_toStbOne_id: "ChkLCR t --> toStbOne t = t"
apply (induct_tac t)
apply (simp_all)
apply (auto)
apply (simp_all add: ChkR_ChkCR)
apply (insert list_nil_or_unnil)
apply (drule_tac x="list" in spec)
apply (auto)
apply (drule_tac x="list" in spec)
apply (auto)
done

(* ---- basic ---- *)

lemma ChkLCR_toStbOne: "ChkLCR t --> ChkLCR (toStbOne (a#t))"
apply (induct_tac t)
apply (simp_all)
apply (simp add: Att_or)

apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (intro conjI impI)
apply (elim disjE conjE exE)
apply (simp_all)

apply (insert list_nil_or_unnil)
apply (drule_tac x="list" in spec)
apply (insert Att_or)
apply (elim disjE conjE exE)
apply (simp)
apply (drule_tac x="ab" in spec)
apply (elim disjE conjE exE)
apply (simp_all)

apply (drule_tac x="list" in spec)
apply (frule_tac x="a" in spec)
apply (elim disjE conjE exE)
apply (simp_all)

apply (drule_tac x="list" in spec)
apply (frule_tac x="a" in spec)
apply (elim disjE conjE exE)
apply (simp_all)
done

lemma ChkLCR_tl[rule_format]: "ChkLCR (a#t) --> ChkLCR t"
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE conjE exE)
apply (simp_all add: ChkR_ChkCR)
done

lemma ChkLCR_toStb: "ChkLCR (toStb t)"
apply (induct_tac t)
apply (simp_all)
apply (simp add: ChkLCR_toStbOne)
done

lemma ChkLCR_toStb_id[rule_format]: "ChkLCR t --> toStb t = t"
apply (induct_tac t)
apply (simp_all)
apply (auto)
apply (simp_all add: ChkR_ChkCR)
apply (insert list_nil_or_unnil)
apply (drule_tac x="list" in spec)
apply (auto)
apply (drule_tac x="list" in spec)
apply (auto)
done


(* basic *)

lemma nextL_one_EX:
 "[| ChkLCR t ; nextL t = [a] |] ==> (EX a. t = [a])"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (elim disjE conjE exE)
apply (simp_all)
apply (elim disjE conjE exE)
apply (simp_all)
apply (insert list_nil_or_unnil)
apply (drule_tac x="s" in spec)
apply (elim disjE conjE exE)
apply (simp_all)
apply (elim disjE conjE exE)
apply (simp_all)
done

lemma nextR_one_EX:
 "[| ChkLCR t ; nextR (t,x) = [a] |] ==> (EX a. t = [a])"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (elim disjE conjE exE)
apply (simp_all)
apply (elim disjE conjE exE)
apply (simp_all)
apply (insert list_nil_or_unnil)
apply (drule_tac x="s" in spec)
apply (elim disjE conjE exE)
apply (simp_all)

apply (frule_tac x="s" in spec)
apply (elim disjE conjE exE)
apply (simp_all)
apply (elim conjE exE)
apply (simp)
apply (drule_tac x="sa" in spec)
apply (elim disjE conjE exE)
apply (simp_all)

apply (frule_tac x="s" in spec)
apply (elim disjE conjE exE)
apply (simp_all)
apply (elim conjE exE)
apply (simp)
apply (drule_tac x="sa" in spec)
apply (elim disjE conjE exE)
apply (simp_all)
done

(*  ----  basic ---- *)

lemma toStbOne_nil[simp]: "(toStbOne t = []) = (t = [])"
apply (induct_tac t)
apply (simp_all)

apply (insert list_nil_or_unnil)
apply (frule_tac x="list" in spec)
apply (elim disjE conjE exE)
apply (simp)
apply (drule_tac x="s" in spec)
apply (elim disjE conjE exE)
apply (simp)

apply (insert Att_or)
apply (frule_tac x="a" in spec)
apply (drule_tac x="aa" in spec)
apply (elim disjE conjE exE)
apply (simp_all)

apply (frule_tac x="a" in spec)
apply (frule_tac x="aa" in spec)
apply (drule_tac x="ab" in spec)
apply (elim disjE conjE exE)
apply (simp_all)
done

lemma toStb_nil[simp]: "(toStb t = []) = (t = [])"
apply (induct_tac t)
apply (simp_all)
done

lemma toStbOne_one[simp]: "(toStbOne t = [a]) = (t = [a])"
apply (induct_tac t)
apply (simp_all)

apply (insert list_nil_or_unnil)
apply (frule_tac x="list" in spec)
apply (elim disjE conjE exE)
apply (simp)
apply (drule_tac x="s" in spec)
apply (elim disjE conjE exE)
apply (simp)

apply (insert Att_or)
apply (frule_tac x="aa" in spec)
apply (drule_tac x="aaa" in spec)
apply (elim disjE conjE exE)
apply (simp_all)

apply (frule_tac x="aa" in spec)
apply (frule_tac x="aaa" in spec)
apply (drule_tac x="ab" in spec)
apply (elim disjE conjE exE)
apply (simp_all)
done

lemma toStb_one[simp]: "(toStb t = [a]) = (t = [a])"
apply (induct_tac t)
apply (simp_all)
done

lemma length_nextL: "(guardL t & ChkLCR t) --> length (nextL t) = length t"
apply (induct_tac t)
apply (simp)

apply (simp)
apply (intro conjI impI)
apply (auto)

apply (insert list_nil_or_unnil)
apply (drule_tac x="list" in spec)
apply (elim disjE exE)
apply (simp_all)
apply (elim disjE exE conjE)
apply (simp_all)

apply (drule_tac x="list" in spec)
apply (elim disjE conjE exE)
apply (simp)
apply (simp)
apply (elim disjE exE conjE)
apply (simp_all)
done

lemma toStbOne_length[rule_format]: 
  "ALL a. ChkLCR t --> length (toStbOne (a#t)) = Suc (length t)"
apply (induct_tac t)
apply (simp_all)

apply (rule allI)
apply (insert list_nil_or_unnil)
apply (frule_tac x="list" in spec)
apply (elim disjE conjE exE)
apply (simp)

apply (insert Att_or)
apply (frule_tac x="a" in spec)
apply (drule_tac x="aa" in spec)
apply (elim disjE conjE exE)
apply (simp_all)

apply (frule_tac x="a" in spec)
apply (frule_tac x="aa" in spec)
apply (drule_tac x="ab" in spec)
apply (elim disjE conjE exE)
apply (simp_all)
apply (simp add: length_nextL)
apply (simp add: length_nextL)
done

lemma ChkLCR_toStbOne_if[rule_format]: 
  "ALL a. ChkLCR (toStbOne (a#s)) --> ChkLCR s"
apply (induct_tac s)
apply (simp_all)

apply (intro conjI impI)
apply (elim conjE exE)
apply (insert Att_or)
apply (frule_tac x="a" in spec)
apply (drule_tac x="aa" in spec)
apply (elim disjE conjE exE)
apply (simp_all)

apply (insert list_nil_or_unnil)
apply (drule_tac x="list" in spec)
apply (elim disjE conjE exE)
apply (simp)
apply (drule mp)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="ab" in spec)
apply (elim disjE conjE exE)
apply (simp_all)
apply (rule_tac x="AttL (0, 0)" in exI)
apply (simp)
apply (rule_tac x="AttL (0, 0)" in exI)
apply (simp)
apply (rule_tac x="AttL (0, 0)" in exI)
apply (simp)
done

lemma ChkLCR_toStbOne_iff: 
  "ChkLCR (toStbOne (a#s)) = ChkLCR s"
apply (rule iffI)
apply (rule ChkLCR_toStbOne_if)
apply (simp)
apply (simp add: ChkLCR_toStbOne)
done

lemma EX_toStbOne_toStb: "EX t. toStbOne t = toStb s"
apply (induct_tac s)
apply (rule_tac x="[]" in exI)
apply (auto)
done

(* -------------------------------------------------------------------- *)

lemma nextL_AttL_EX: "EX a s. nextL (AttL (n, x) # t) = a#s"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma nextR_AttC_EX: "EX a s. nextR (AttC n # t,x) = a#s"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma nextR_AttR_EX: "EX a s. nextR (AttR n # t,x) = a#s"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma hd_nextR_AttC_EX:
  "EX x s. nextR (AttC n # t, y) = AttL (n,x)#s"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma getNat_hd_nextR_AttC:
  "getNat (hd (nextR (AttC n # t, y))) = n"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma guardR_nextR_nextL_lm: 
  "ALL t z. (length t = n & ChkLCR t & guardL t & guardR t) 
   --> guardR (nextR ((nextL t), z))"
apply (induct_tac n)
apply (simp)
apply (intro allI impI)
apply (simp)
apply (elim disjE exE conjE)

apply (insert list_nil_or_unnil)
apply (rotate_tac -1)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
apply (elim disjE exE)
apply (simp_all)
apply (insert list_nil_or_unnil)
apply (rotate_tac -1)
apply (frule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
apply (elim disjE exE conjE)
apply (simp_all)
apply (frule_tac x="sa" in spec)
apply (elim disjE exE)
apply (simp_all)
apply (drule_tac x="sa" in spec)
apply (elim disjE exE)
apply (simp_all)
apply (rotate_tac -1)
apply (drule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma guardR_nextR_nextL: 
  "[| ChkLCR t ; guardL t ; guardR t |]
   ==> guardR (nextR ((nextL t), z))"
apply (insert guardR_nextR_nextL_lm[of "length t"])
apply (simp)
done

lemma guardL_nextL_nextR_lm: 
  "ALL t z. (length t = n & ChkLCR t & guardL t & guardR t) 
   --> guardL (nextL (nextR (t, z)))"
apply (induct_tac n)
apply (simp)
apply (intro allI impI)
apply (simp)
apply (elim disjE exE conjE)

apply (insert list_nil_or_unnil)
apply (rotate_tac -1)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
apply (elim disjE exE)
apply (simp_all)
apply (insert list_nil_or_unnil)
apply (rotate_tac -1)
apply (frule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
done

lemma guardL_nextL_nextR: 
  "[| ChkLCR t ; guardL t ; guardR t |]
   ==> guardL (nextL (nextR (t, z)))"
apply (insert guardL_nextL_nextR_lm[of "length t"])
apply (simp)
done

lemma guardR_nextR_AttR_lm:
  "ALL t m x. (length t = n & ChkLCR t)
   --> guardR (nextR (AttR m # t, x))"
apply (induct_tac n)
apply (simp)
apply (intro allI impI)
apply (simp)
apply (elim disjE exE conjE)

apply (insert list_nil_or_unnil)
apply (rotate_tac -1)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
apply (elim conjE disjE exE)
apply (simp_all)
done

lemma guardR_nextR_AttR:
  "ChkLCR t ==> guardR (nextR (AttR m # t, x))"
apply (insert guardR_nextR_AttR_lm[of "length t"])
apply (simp)
done

lemma not_nil_nextL_not_nil[simp]: "t ~= [] ==> nextL t ~= []"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (auto)
done

lemma not_nil_nextR_not_nil[simp]: "t ~= [] ==> nextR (t,x) ~= []"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (auto)
done


(* --------------------------------- *
               lemmas
 * --------------------------------- *)

lemma toStbOne_AttC_hd:
  "ALL n s. (EX m t. toStbOne ((AttC n)#s) = (AttC m)#t) |
            (EX m t. toStbOne ((AttC n)#s) = (AttL m)#t)"
apply (intro allI)
apply (insert list_nil_or_unnil)
apply (frule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp)
apply (frule_tac x="sa" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE exE)
apply (simp_all)

apply (frule_tac x="a" in spec)
apply (drule_tac x="aa" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma guardL_toStb_AttC:
   "s ~= [] ==> guardL (toStb (map AttC s))"
apply (insert list_nil_or_unnil)
apply (drule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
apply (insert toStbOne_AttC_hd)
apply (drule_tac x="a" in spec)
apply (drule_tac x="toStb (map AttC sa)" in spec)
apply (auto)
done

lemma guardR_toStbOne_map_AttC_lm:
   "ALL s. (length s = n & s ~= []) --> guardR (toStbOne (map AttC s))"
apply (induct_tac n)
apply (simp)
apply (intro allI impI)
apply (elim disjE exE conjE)

apply (insert list_nil_or_unnil)
apply (rotate_tac -1)
apply (frule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
apply (frule_tac x="sa" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
apply (drule_tac x="sb" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
apply (drule_tac x="sa" in spec)
apply (simp)
apply (simp add: guardR_last)
apply (auto)
done

lemma guardR_toStbOne_AttC:
   "ChkLCR t ==> guardR (toStbOne (AttC a # t))"
apply (insert list_nil_or_unnil)
apply (frule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp_all)
apply (elim disjE conjE exE)
apply (simp_all)
done

lemma guardR_toStb_AttC:
   "s ~= [] ==> guardR (toStb (map AttC s))"
apply (insert list_nil_or_unnil)
apply (drule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
apply (simp add: guardR_toStbOne_AttC ChkLCR_toStb)
done

(*********************************************************
              preliminary (stabilization)
 *********************************************************)

lemma toStbOne_AttC_hd2:
  "ALL n s. (EX t. toStbOne ((AttC n)#s) = (AttC n)#t) |
            (EX m t. toStbOne ((AttC n)#s) = (AttL (n,m))#t)"
apply (intro allI)
apply (insert list_nil_or_unnil)
apply (frule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp)
apply (frule_tac x="sa" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE exE)
apply (simp_all)

apply (frule_tac x="a" in spec)
apply (drule_tac x="aa" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma getNat_hd_toStbOne_AttC[simp]:
  "getNat (hd (toStbOne ((AttC n)#s))) = n"
apply (insert toStbOne_AttC_hd2)
apply (drule_tac x="n" in spec)
apply (drule_tac x="s" in spec)
apply (auto)
done

lemma nextR_nextL_AttL_EX:
  "ALL n x a s y.
   EX z t. (nextR (nextL (AttL (n, x) # a # s), y)) = 
            (AttL(fill (n div 2 + x),z)) # t"
apply (intro allI)
apply (insert list_nil_or_unnil)
apply (frule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE exE)
apply (simp_all)

apply (frule_tac x="a" in spec)
apply (drule_tac x="aa" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma getNat_hd_nextR_nextL_AttL[simp]:
  "getNat(hd (nextR (nextL (AttL (n, x) # a # s), y))) = fill (n div 2 + x)"
apply (insert nextR_nextL_AttL_EX)
apply (drule_tac x="n" in spec)
apply (drule_tac x="x" in spec)
apply (drule_tac x="a" in spec)
apply (drule_tac x="s" in spec)
apply (drule_tac x="y" in spec)
apply (auto)
done

(* ---------------------------------- *
      async version <--> lineNext
 * ---------------------------------- *)

lemmas toStb_simp = guardR_toStb_AttC
                    guardL_toStb_AttC
                    ChkLCR_toStb

lemma nextL_nextR_toStb_lineNext:
  "nextL (nextR (toStb (map AttC s), x)) = toStb (map AttC (lineNext s x))"
apply (induct_tac s)
apply (simp)
apply (simp)
apply (intro impI)
apply (drule sym)
apply (simp)   (* induction hypothesis *)

apply (subgoal_tac "ChkLCR (toStb (map AttC list))")  (* by ChkLCR_toStb *)
apply (subgoal_tac "guardL (toStb (map AttC list))")  (* by guardL_toStb_AttC *)
apply (subgoal_tac "guardR (toStb (map AttC list))")  (* by guardR_toStb_AttC *)
apply (simp add: nextL_nextR_order)
apply (simp add: not_nil_EX)
apply (elim exE)
apply (simp)
apply (insert toStbOne_AttC_hd2)
apply (drule_tac x="aa" in spec)
apply (drule_tac x="toStb (map AttC t)" in spec)
apply (elim disjE conjE exE)
 (* C *)
 apply (simp)
 apply (case_tac "ta=[]")
 apply (simp)
 apply (simp add: not_nil_EX)
 apply (elim exE)
 apply (simp)

 (* L *)
 apply (simp)
 apply (case_tac "ta=[]")
 apply (simp)
 apply (simp add: not_nil_EX)
 apply (elim exE)
 apply (simp)
 apply (insert nextR_nextL_AttL_EX)
  apply (drule_tac x="aa" in spec)
  apply (drule_tac x="m" in spec)
  apply (drule_tac x="ab" in spec)
  apply (drule_tac x="tb" in spec)
  apply (drule_tac x="x" in spec)
 apply (elim exE)
 apply (simp)

 apply (simp add: guardR_toStb_AttC)
 apply (simp add: guardL_toStb_AttC)
 apply (simp add: ChkLCR_toStb)
done

lemma nextR_nextL_toStb_nextR_nextL_toStb:
  "s ~= [] ==>
   nextR (nextL (toStb (map AttC s)), x) = nextL (nextR (toStb (map AttC s), x))"
apply (simp add: nextL_nextR_order toStb_simp)
done

lemma nextR_nextL_toStb_lineNext:
  "s ~= [] ==>
   nextR (nextL (toStb (map AttC s)), x) = toStb (map AttC (lineNext s x))"
apply (simp add: nextR_nextL_toStb_nextR_nextL_toStb
                 nextL_nextR_toStb_lineNext)
done

(* ----------- guard lemma ----------- *)

lemma guardL_nextL_toStb_AttC:
   "tl s ~= [] ==> guardL (nextL (toStb (map AttC s)))"
apply (insert list_nil_or_unnil)
apply (frule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
apply (drule_tac x="sa" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
apply (insert toStbOne_AttC_hd)
apply (drule_tac x="aa" in spec)
apply (drule_tac x="toStb (map AttC saa)" in spec)
apply (auto)
done

lemma toStbOne_AttC_AttC:
  "toStbOne ((AttC n)#(toStbOne ((AttC m)#s))) = 
   (AttL (n,m div 2))#(nextL (toStbOne((AttC m)#s)))"
apply (insert list_nil_or_unnil)
apply (frule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp)
apply (frule_tac x="sa" in spec)
apply (elim disjE exE)
apply (simp)
apply (insert Att_or)
apply (drule_tac x="a" in spec)
apply (elim disjE exE)
apply (simp_all)

apply (frule_tac x="a" in spec)
apply (drule_tac x="aa" in spec)
apply (elim disjE exE)
apply (simp_all)
done

lemma guardR_nextR_toStb_AttC_lm:
   "ALL s x. (length s = n & tl s ~= []) 
    --> guardR (nextR (toStb (map AttC s),x))"
apply (induct_tac n)
apply (simp)
apply (intro allI impI)
apply (insert list_nil_or_unnil)
apply (rotate_tac -1)
apply (frule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)

apply (subgoal_tac "ChkLCR (toStb (map AttC sa))")  (* by ChkLCR_toStb *)
apply (subgoal_tac "guardL (toStb (map AttC sa))")  (* by guardL_toStb_AttC *)
apply (subgoal_tac "guardR (toStb (map AttC sa))")  (* by guardR_toStb_AttC *)

apply (drule_tac x="sa" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
apply (simp add: toStbOne_AttC_AttC)

apply (insert list_nil_or_unnil)
apply (rotate_tac -1)
apply (drule_tac x="nextL (toStbOne (AttC aa # toStb (map AttC sb)))" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
apply (rotate_tac -1)
apply (drule sym)
apply (simp)
apply (subgoal_tac "nextR (nextL (toStbOne (AttC aa # toStb (map AttC sb))), x) =
                    nextL (nextR (toStbOne (AttC aa # toStb (map AttC sb)), x))")
apply (simp)
apply (simp add: nextL_nextR_order)

 apply (simp add: guardR_toStb_AttC)
 apply (simp add: guardL_toStb_AttC)
 apply (simp add: ChkLCR_toStb)
done


lemma guardR_nextR_toStb_AttC:
   "tl s ~= [] ==> guardR (nextR (toStb (map AttC s),x))"
apply (insert guardR_nextR_toStb_AttC_lm[of "length s"])
apply (simp)
done

(* ---------------------------------- *
                nextLR
 * ---------------------------------- *)

lemma nextLR_toStb_circNext:
  "nextLR (toStb (map AttC s)) = toStb (map AttC (circNext s))"
apply (simp add: nextLR_def)
apply (simp add: circNext_def)
apply (intro impI)
apply (simp add: nextL_nextR_toStb_lineNext)
apply (simp add: not_nil_EX)
apply (elim exE)
apply (simp)
done

(* ------------- lemma ------------- *)

lemma tl_lineNext:
 "tl t ~= [] ==> lineNext (tl t) x = tl (lineNext t x)"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
done

lemma hd_lineNext: 
  "tl t ~= [] ==> hd (lineNext t x) =  (fill (hd t div 2 + hd (tl t) div 2))"
apply (insert list_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
done


lemma hd_circNext: 
  "tl t ~= [] ==> hd (circNext t) =  (fill (hd t div 2 + hd (tl t) div 2))"
apply (simp add: circNext_def)
apply (auto)
apply (simp add: hd_lineNext)
done

lemma getNat_hd_toStb_map_AttC:
  "t ~= [] ==> getNat (hd (toStb (map AttC t))) = hd t"
apply (simp add: not_nil_EX)
apply (elim exE)
apply (simp)
done

end
