           (*-------------------------------------------*
            |       Uniform Candy Distribution          |
            |                                           |
            |           November 2007 for Isabelle 2005 |
            |                May 2008 (modified)        |
            |           November 2008 for Isabelle 2008 |
            |                May 2016 for Isabelle 2016 |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory UCD_proc1
imports UCD_data2
begin

(*****************************************************************

         1. 

 *****************************************************************)

(*=============================================================*
 |                                                             |
 |                           Process                           |
 |                                                             |
 *=============================================================*)

(*********************************************************
               process names and events
 *********************************************************)

datatype Event = left nat | right nat | mid nat | stlist "Att list"
datatype PN = Child nat | ChildL "nat*nat" | ChildR nat | 
              LineSpec "Att list"

lemma inj_stlist[simp]: "inj stlist"
by (simp add: inj_on_def)

lemma inj_event[simp]: "inj left" "inj right" "inj mid"
by (simp_all add: inj_on_def)

(*********************************************************
                  Recursivey Process
 *********************************************************)

primrec	
  PNdef :: "PN => (PN, Event) proc"
where
 "PNdef (Child c) = 
   (left ! (c div 2) -> $(ChildR (c div 2))) [+] (right ? x -> $(ChildL (c,x)))"

|"PNdef (ChildL cx) = 
    left ! ((fst cx) div 2) -> $(Child (fill((fst cx) div 2 + (snd cx))))"

|"PNdef (ChildR c) = 
    right ? x -> $(Child (fill(c + x)))"

|"PNdef (LineSpec s) =
    IF (ChkLCR s) THEN
     ((IF guardL(s) THEN 
         (left ! (getNat(hd(s)) div 2) -> $LineSpec(nextL(s))) ELSE STOP) [+]
      (IF guardR(s) THEN (right ? x -> $LineSpec(nextR(s,x))) ELSE STOP))
    ELSE STOP"
(*
defs (overloaded) Set_PNfun_def [simp]: "PNfun == PNdef"
*)

overloading Set_PNfun == 
  "PNfun :: (PN, Event) pnfun"
begin
  definition "PNfun == PNdef"
end
  
declare Set_PNfun_def [simp]

(* ------------------ *
      guardedness
 * ------------------ *)

lemma guardedfun_PN[simp]:
      "guardedfun PNdef"
by (simp add: guardedfun_def, rule allI, induct_tac p, simp_all)

(*
defs FPmode_def [simp]: "FPmode == CMSmode"
*)

overloading FPmode == 
  "FPmode :: fpmode"
begin
  definition "FPmode == CMSmode"
end

declare FPmode_def [simp]

(*********************************************************
                     Composition
 *********************************************************)

primrec
  ChildAtt :: "Att => (PN, Event) proc"
where
 "ChildAtt (AttL c) = ($ChildL c)"
|"ChildAtt (AttC c) = ($Child c)"
|"ChildAtt (AttR c) = ($ChildR c)"

abbreviation                            (* Isabelle 2008 *)
    LeftRight :: "Event set"
where "LeftRight == range left Un range right"

(* Isabelle 2005
syntax 
 LeftRight :: "Event set"
translations
 "LeftRight" == "range left Un range right"
*)

abbreviation                            (* Isabelle 2008 *)
    Line :: "(PN, Event) proc => (PN, Event) proc => (PN, Event) proc"
                                    ("(1_ /<---> _)" [76,77] 76)
where "P <---> Q == (P\<lbrakk>right<==>mid\<rbrakk> |[range mid]| 
                    Q\<lbrakk>left<==>mid\<rbrakk>) \<midarrow> (range mid)"

abbreviation                            (* Isabelle 2008 *)
    PreCirc :: "(PN, Event) proc => (PN, Event) proc => (PN, Event) proc"
                                    ("(1_ /<=-=> _)" [76,77] 76)
where "P <=-=> Q == (P |[LeftRight]| Q\<lbrakk>right<==>left\<rbrakk>)"

abbreviation                            (* Isabelle 2008 *)
    Circ :: "(PN, Event) proc => (PN, Event) proc => (PN, Event) proc"
                                    ("(1_ /<===> _)" [76,77] 76)
where "P <===> Q == (P <=-=> Q) \<midarrow> (range right)"

(*   Isabelle 2005
syntax
 "_Line" :: "(PN, Event) proc => (PN, Event) proc => (PN, Event) proc"
                                    ("(1_ /<---> _)" [76,77] 76)
 "_PreCirc" :: "(PN, Event) proc => (PN, Event) proc => (PN, Event) proc"
                                    ("(1_ /<=-=> _)" [76,77] 76)
 "_Circ" :: "(PN, Event) proc => (PN, Event) proc => (PN, Event) proc"
                                    ("(1_ /<===> _)" [76,77] 76)
translations
   "P <---> Q" == "(P\<lbrakk>right<==>mid\<rbrakk> |[range mid]| 
                    Q\<lbrakk>left<==>mid\<rbrakk>) \<midarrow> (range mid)"
   "P <=-=> Q" == "(P |[LeftRight]| Q\<lbrakk>right<==>left\<rbrakk>)"
   "P <===> Q" == "(P <=-=> Q) \<midarrow> (range right)"
*)

(*
2011
consts
 LineChild  :: "nat list => (PN, Event) proc"
 LineChildAtt :: "Att list => (PN, Event) proc"
*)
(*
primrec
 "LineChild (c#s) = (if (s=[]) then ($Child c)
                     else ($Child c) <---> (LineChild s))"
primrec
 "LineChildAtt (c#s) = (if (s=[]) then (ChildAtt c)
                       else (ChildAtt c) <---> (LineChildAtt s))"
*)

fun
 LineChild  :: "nat list => (PN, Event) proc"
where
 "LineChild ([c]) = $Child c"
|"LineChild (c#s) = ($Child c) <---> (LineChild s)"

fun
 LineChildAtt :: "Att list => (PN, Event) proc"
where
 "LineChildAtt ([c]) = ChildAtt c"
|"LineChildAtt (c#s) = (ChildAtt c) <---> (LineChildAtt s)"


(*
consts
 PreCircChild  :: "nat list => (PN, Event) proc"
 CircChild  :: "nat list => (PN, Event) proc"

defs
 PreCircChild_def:
 "PreCircChild s == (if (tl s = []) then STOP 
                  else ($Child (hd s)) <=-=> (LineChild (tl s)))"
 CircChild_def:
 "CircChild s == (if (tl s = []) then STOP 
                  else ($Child (hd s)) <===> (LineChild (tl s)))"
*)

fun
 PreCircChild  :: "nat list => (PN, Event) proc"
where
 "PreCircChild (c#s) = ($Child c) <=-=> (LineChild s)"

fun
 CircChild  :: "nat list => (PN, Event) proc"
where
 "CircChild (c#s) = ($Child c) <===> (LineChild s)"

(* --------------------------------- *
               lemmas
 * --------------------------------- *)

lemma LineChild_not_nil [simp]: 
  "s ~= [] ==> LineChild (c#s) = ($Child c) <---> (LineChild s)"
apply (simp add: not_nil_EX)
apply (elim conjE exE)
by (simp)

lemma LineChildAtt_not_nil [simp]: 
  "s ~= [] ==> LineChildAtt (c#s) = (ChildAtt c) <---> (LineChildAtt s)"
apply (simp add: not_nil_EX)
apply (elim conjE exE)
by (simp)

(*********************************************************
                  for convenience
 *********************************************************)

declare simp_event_set [simp]

lemma Line_cong: "Q =F R ==> P <---> Q =F P <---> R"
by (simp)

lemma PreCirc_cong: "Q =F R ==> P <=-=> Q =F P <=-=> R"
by (simp)

lemma Circ_cong: "Q =F R ==> P <===> Q =F P <===> R"
by (simp)

(*********************************************************
                  for induction (sub)
 *********************************************************)

primrec
  LineSpec_to_Step :: "PN => (PN, Event) proc"
where
  "LineSpec_to_Step (Child n)    = $(Child n)"
 |"LineSpec_to_Step (ChildL n)   = $(ChildL n)"
 |"LineSpec_to_Step (ChildR n)   = $(ChildR n)"

 |"LineSpec_to_Step (LineSpec s) = 
    (IF (ChkLCR s) THEN
       IF (tl s = []) THEN $LineSpec s
       ELSE (!<stlist> t:{t. toStbOne t = s} .. 
                (ChildAtt (hd t) <---> $LineSpec (tl t)))
     ELSE STOP)"

(* --------------------- LineSpec_Step (lemmas) --------------------- *)

lemma LineSpec_Step_ref1_AttL_AttL:
  "[| ChkLCR t; list = AttL (n, x) # AttL (na, xa) # t;
          a = AttL (n, x) # AttL (na, xa) # t; a1 = AttL (n, x); a2 = AttL (na, xa) |]
       ==> (IF True 
           THEN (left ! (n div 2) 
                 -> IF True 
                    THEN IF False 
                         THEN ($LineSpec
                                (AttL (fill (n div 2 + x), na div 2) #
                                 nextL (AttL (na, xa) # t))) 
                         ELSE (!<stlist> t:{ta. toStbOne ta =
  AttL (fill (n div 2 + x), na div 2) # nextL (AttL (na, xa) # t)} .. 
                               ChildAtt (hd t) <---> $LineSpec (tl t)) 
                    ELSE STOP) 
           ELSE STOP) 
            [+] (IF guardR t 
                THEN (right ? xb 
                      -> IF ChkLCR (nextR (AttL (na, xa) # t, xb)) 
                         THEN IF False 
                              THEN ($LineSpec
                                     (AttL (n, x) # nextR (AttL (na, xa) # t, xb))) 
                              ELSE (!<stlist> t:{ta.
   toStbOne ta = AttL (n, x) # nextR (AttL (na, xa) # t, xb)} .. 
                                    ChildAtt (hd t) <---> $LineSpec (tl t)) 
                         ELSE STOP) 
                ELSE STOP) 
           <=F $ChildL (n, x) <---> $LineSpec (AttL (na, xa) # t)"

apply (case_tac "guardR t ")

 apply (cspF_unwind)
 apply (cspF_hsf)+
 apply (rule)
 apply (simp)
 apply (simp)
 apply (elim disjE conjE exE)
 apply (simp)
 apply (cspF_simp)+
 apply (rule cspF_Rep_int_choice_left)
 apply (simp)
 apply (rule_tac x="AttC (fill (n div 2 + x)) # AttL (na, xa) # t" in exI)
 apply (simp)
 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_decompo)
 apply (simp)+
 apply (cspF_unwind)
 apply (cspF_hsf)+

 (* right *)
 apply (simp add: image_iff)
 apply (elim conjE exE)
 apply (simp)
 apply (cspF_simp)+
 apply (rule cspF_Rep_int_choice_left)
 apply (simp)
 apply (rule_tac x="AttL (n,x) # nextR (AttL (na, xa) # t, xb)" in exI)
 apply (simp)
 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_decompo)
 apply (simp)+
 apply (cspF_unwind)
 apply (cspF_hsf)+

(* ~ guardR t *)
 apply (cspF_unwind)
 apply (cspF_hsf)+
 apply (rule)
 apply (simp)
 apply (simp)
 apply (cspF_simp)+
 apply (rule cspF_Rep_int_choice_left)
 apply (simp)
 apply (rule_tac x="AttC (fill (n div 2 + x)) # AttL (na, xa) # t" in exI)
 apply (simp)
 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_decompo)
 apply (simp)+
 apply (cspF_unwind)
 apply (cspF_hsf)+
done

lemma LineSpec_Step_ref1_AttL_AttC:
      "[| ChkR t; list = AttL (n, x) # AttC na # t; a = AttL (n, x) # AttC na # t;
          a2 = AttC na; a1 = AttL (n, x) |]
       ==> (IF True 
           THEN (left ! (n div 2) 
                 -> IF True 
                    THEN IF False 
                         THEN ($LineSpec
                                (AttL (fill (n div 2 + x), na div 2) #
                                 AttR (na div 2) # t)) 
                         ELSE (!<stlist> t:{ta. toStbOne ta =
  AttL (fill (n div 2 + x), na div 2) # AttR (na div 2) # t} .. 
                               ChildAtt (hd t) <---> $LineSpec (tl t)) 
                    ELSE STOP) 
           ELSE STOP) 
            [+] (IF True 
                THEN (right ? xa 
                      -> IF True 
                         THEN IF False 
                              THEN ($LineSpec (AttL (n, x) # nextR (AttC na # t, xa))) 
                              ELSE (!<stlist> t:{ta.
   toStbOne ta = AttL (n, x) # nextR (AttC na # t, xa)} .. 
                                    ChildAtt (hd t) <---> $LineSpec (tl t)) 
                         ELSE STOP) 
                ELSE STOP) 
           <=F $ChildL (n, x) <---> $LineSpec (AttC na # t)"
 apply (cspF_unwind)
 apply (cspF_hsf)+
 apply (rule)
 apply (simp)
 apply (simp)
 apply (elim disjE conjE exE)

 (* left *)
 apply (simp)
 apply (cspF_simp)+
 apply (rule cspF_Rep_int_choice_left)
 apply (simp)
 apply (rule_tac x="AttC (fill (n div 2 + x)) # AttC na # t" in exI)
 apply (simp)
 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_decompo)
 apply (simp)+
 apply (cspF_unwind)
 apply (cspF_hsf)+

 (* right *)
 apply (simp add: image_iff)
 apply (elim conjE exE)
 apply (simp)
 apply (cspF_simp)+
 apply (rule cspF_Rep_int_choice_left)
 apply (simp)
 apply (rule_tac x="AttL (n,x) # nextR (AttC na # t, xa)" in exI)
 apply (simp)
 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_decompo)
 apply (simp)+
 apply (cspF_unwind)
 apply (cspF_hsf)+
done

lemma LineSpec_Step_ref1_AttL_AttR:
    "[| ChkR t; list = AttL (n, x) # AttR na # t; a = AttL (n, x) # AttR na # t;
          a2 = AttR na; a1 = AttL (n, x) |]
       ==> (IF True 
           THEN (left ! (n div 2) 
                 -> IF True 
                    THEN IF False 
                         THEN ($LineSpec (AttC (fill (n div 2 + x)) # AttR na # t)) 
                         ELSE (!<stlist> t:{ta. toStbOne ta =
  AttC (fill (n div 2 + x)) # AttR na # t} .. 
                               ChildAtt (hd t) <---> $LineSpec (tl t)) 
                    ELSE STOP) 
           ELSE STOP) 
            [+] (IF True 
                THEN (right ? xa 
                      -> IF True 
                         THEN IF False 
                              THEN ($LineSpec (AttL (n, x) # nextR (AttR na # t, xa))) 
                              ELSE (!<stlist> t:{ta.
   toStbOne ta = AttL (n, x) # nextR (AttR na # t, xa)} .. 
                                    ChildAtt (hd t) <---> $LineSpec (tl t)) 
                         ELSE STOP) 
                ELSE STOP) 
           <=F $ChildL (n, x) <---> $LineSpec (AttR na # t)"
  apply (cspF_unwind)
  apply (cspF_hsf)+
  apply (rule)
  apply (simp)
  apply (simp)
  apply (elim disjE conjE exE)
  apply (simp)
  apply (cspF_simp)+
  apply (rule cspF_Rep_int_choice_left)
  apply (simp)
  apply (rule_tac x="AttC (fill (n div 2 + x)) # AttR na # t" in exI)
  apply (simp)
  apply (rule cspF_decompo)
  apply (simp)
  apply (rule cspF_decompo)
  apply (simp)+
  apply (cspF_unwind)
  apply (cspF_hsf)+

  (* right *)
  apply (simp add: image_iff)
  apply (elim conjE exE)
  apply (simp)
  apply (cspF_simp)+
  apply (rule cspF_Rep_int_choice_left)
  apply (simp)
  apply (rule_tac x="AttL (n,x) # nextR (AttR na # t, xa)" in exI)
  apply (simp)
  apply (rule cspF_decompo)
  apply (simp)
  apply (rule cspF_decompo)
  apply (simp)+
  apply (cspF_unwind)
  apply (cspF_hsf)+
done

lemma LineSpec_Step_ref1_AttC_AttC:
   "[| ChkR t; list = AttL (n, na div 2) # AttR (na div 2) # t;
          a = AttC n # AttC na # t; a1 = AttC n; a2 = AttC na |]
       ==> (IF True 
           THEN (left ! (n div 2) 
                 -> IF True 
                    THEN IF False 
                         THEN ($LineSpec
                                (AttC (fill (n div 2 + na div 2)) # AttR (na div 2) # t)) 
                         ELSE (!<stlist> t:{ta. toStbOne ta =
  AttC (fill (n div 2 + na div 2)) # AttR (na div 2) # t} .. 
                               ChildAtt (hd t) <---> $LineSpec (tl t)) 
                    ELSE STOP) 
           ELSE STOP)
            [+] (IF True 
                THEN (right ? x 
                      -> IF True 
                         THEN IF False 
                              THEN ($LineSpec
                                     (AttL (n, na div 2) #
                                      nextR (AttR (na div 2) # t, x))) 
                              ELSE (!<stlist> t:{ta.
   toStbOne ta = AttL (n, na div 2) # nextR (AttR (na div 2) # t, x)} .. 
                                    ChildAtt (hd t) <---> $LineSpec (tl t)) 
                         ELSE STOP) 
                ELSE STOP) 
           <=F $Child n <---> $LineSpec (AttC na # t)"

  apply (case_tac "t=[]")
  apply (cspF_unwind)
  apply (cspF_hsf)+
  apply (rule)  (* 1i |~| 2i *)

  (* 1i *)

   apply (cspF_unwind)
   apply (cspF_hsf)+

   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    apply (elim disjE conjE exE)  (* left | right *)
   (* 1/2 *)(* left *)
    apply (simp)
    apply (cspF_simp)+
     apply (rule)  (* 1ii |~| 2ii *)

     (* 1ii *)
     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="AttR (n div 2) # AttC na # t" in exI)
     apply (simp)

     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

     (* 2ii *)
     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="AttC (fill (n div 2 + na div 2)) # AttR (na div 2) # t" in exI)
     apply (simp)
     apply (cspF_unwind)
     apply (cspF_hsf)+

   (* 2/2 *)(* right *)
     apply (simp add: image_iff)
     apply (elim conjE exE)
     apply (simp)
     apply (cspF_simp)+
      apply (rule)  (* 1iii |~| 2iii *)

      (* 1iii *)
      apply (rule cspF_Rep_int_choice_left)
      apply (simp)

      apply (rule_tac x="AttC n # AttL (na, x) # t" in exI)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)+
      apply (cspF_unwind)
      apply (cspF_hsf)+
      apply (simp add: image_iff)

      (* 2iii *)
      apply (rule cspF_Rep_int_choice_left)
      apply (simp)
      apply (rule_tac x="AttL (n,na div 2) # AttC (fill (na div 2 + x)) # t" in exI)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)+
      apply (cspF_unwind)
      apply (cspF_hsf)+

  (* 2i *)
   apply (cspF_unwind)
   apply (cspF_hsf)+

   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    apply (elim disjE conjE exE)  (* left | right *)
   (* 1/2 *)(* left *)
    apply (simp)
    apply (cspF_simp)+

     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="AttC (fill (n div 2 + na div 2)) # AttR (na div 2) # t" in exI)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

   (* 2/2 *)(* right *)
     apply (simp add: image_iff)
     apply (elim conjE exE)
     apply (simp)
     apply (cspF_simp)+

     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="AttL (n,na div 2) # AttC (fill (na div 2 + x)) # t" in exI)
     apply (simp)

     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

  (* "t~=[]" *)
  apply (simp add: not_nil)
  apply (elim conjE exE)
  apply (simp)
  apply (elim conjE exE)

  (* AttR *)
  apply (cspF_unwind | cspF_hsf)+

   apply (rule)  (* 1i |~| 2i *)

   (* 1i *)

   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    apply (elim disjE conjE exE)  (* left | right *)
   (* 1/2 *)(* left *)
    apply (simp)
    apply (cspF_simp)+

     apply (rule)  (* 1ii |~| 2ii *)

     (* 1ii *)
     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="AttR (n div 2) # AttC na # t" in exI)
     apply (simp)

     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

     (* 2ii *)
     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="AttC (fill (n div 2 + na div 2)) # AttR (na div 2) # t" in exI)
     apply (simp)
     apply (cspF_unwind)
     apply (cspF_hsf)+

   (* 2/2 *)(* right *)
     apply (simp add: image_iff)
     apply (elim conjE exE)
     apply (simp)
     apply (cspF_simp)+
      apply (rule)  (* 1iii |~| 2iii *)

      (* 1iii *)
      apply (rule cspF_Rep_int_choice_left)
      apply (simp)
      apply (rule_tac x=
        "AttC n # AttL (na, getNat (hd (updateR (AttR x # ta, xa))) ) #
         updateR (AttR x # ta, xa)" in exI)

      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)+
      apply (cspF_unwind)
      apply (cspF_hsf)+
      apply (simp add: image_iff)

      (* 2iii *)
      apply (rule cspF_Rep_int_choice_left)
      apply (simp)
      apply (rule_tac x="AttL (n,na div 2) # 
         AttC (fill (na div 2 + getNat (hd (updateR (AttR x # ta, xa))) )) #
         updateR (t, xa)" in exI)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)+
      apply (cspF_unwind)
      apply (cspF_hsf)+

   (* 2i *)
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    apply (elim disjE conjE exE)  (* left | right *)
   (* 1/2 *)(* left *)
    apply (simp)
    apply (cspF_simp)+

     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="AttC (fill (n div 2 + na div 2)) # AttR (na div 2) # t" in exI)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

   (* 2/2 *)(* right *)
     apply (simp add: image_iff)
     apply (elim conjE exE)
     apply (simp)
     apply (cspF_simp)+

      apply (rule cspF_Rep_int_choice_left)
      apply (simp)
      apply (rule_tac x="AttL (n,na div 2) # 
         AttC (fill (na div 2 + getNat (hd (updateR (AttR x # ta, xa))) )) #
         updateR (t, xa)" in exI)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)+
      apply (cspF_unwind | cspF_hsf)+
done

lemma LineSpec_Step_ref1_AttC_AttL:
     "[| ChkLCR t; list = AttL (na, n div 2) # nextL (AttL (n, x) # t);
          a = AttC na # AttL (n, x) # t; a1 = AttC na; a2 = AttL (n, x) |]
       ==> (IF True 
           THEN (left ! (na div 2) 
                 -> IF True 
                    THEN IF False 
                         THEN ($LineSpec
                                (AttL (fill (na div 2 + n div 2),
                                       fill (n div 2 + x) div 2) #
                                 nextL (nextL (AttL (n, x) # t)))) 
                         ELSE (!<stlist> t:{ta. toStbOne ta =
  AttL (fill (na div 2 + n div 2), fill (n div 2 + x) div 2) #
  nextL (nextL (AttL (n, x) # t))} .. 
                               ChildAtt (hd t) <---> $LineSpec (tl t)) 
                    ELSE STOP) 
           ELSE STOP) 
            [+] (IF True 
                THEN (right ? xa 
                      -> IF True 
                         THEN IF False 
                              THEN ($LineSpec
                                     (AttL (na, n div 2) #
                                      nextR (nextL (AttL (n, x) # t), xa))) 
                              ELSE (!<stlist> t:{ta.
   toStbOne ta = AttL (na, n div 2) # nextR (nextL (AttL (n, x) # t), xa)} .. 
                                    ChildAtt (hd t) <---> $LineSpec (tl t)) 
                         ELSE STOP) 
                ELSE STOP) 
           <=F $Child na <---> $LineSpec (AttL (n, x) # t)"

  apply (case_tac "t=[]")
  apply (cspF_unwind | cspF_hsf)+
  apply (rule)  (* 1i |~| 2i *)

  (* 1i *)
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    apply (elim disjE conjE exE)  (* left | right *)
   (* 1/2 *)(* left *)
    apply (simp)
    apply (cspF_simp)+
     apply (rule)  (* 1ii |~| 2ii *)

     (* 1ii *)
     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="AttR (na div 2) # AttL (n,x) # t" in exI)
     apply (simp)

     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+

     apply (cspF_unwind)
     apply (cspF_hsf)+

     (* 2ii *)
     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x=
       "AttC (fill (na div 2 + n div 2)) # AttC (fill (n div 2 + x)) # t" in exI)
     apply (simp)

     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

   (* 2/2 *)(* right *)
     apply (simp add: image_iff)
     apply (elim conjE exE)
     apply (simp)
     apply (cspF_simp)+

     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="AttL (na,n div 2) # AttL (fill (n div 2 + x), xa) # t" in exI)
     apply (simp)

     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

  (* 2i *)
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    apply (elim disjE conjE exE)  (* left | right *)
   (* 1/2 *)(* left *)
    apply (simp)
    apply (cspF_simp)+

     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x=
      "AttC (fill (na div 2 + n div 2)) # AttC (fill (n div 2 + x)) # t" in exI)
     apply (simp)

     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

   (* 2/2 *)(* right *)
     apply (simp add: image_iff)
     apply (elim conjE exE)
     apply (simp)
     apply (cspF_simp)+

     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="AttL (na,n div 2) # AttL (fill (n div 2 + x), xa) # t" in exI)
     apply (simp)

     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

  (* "t~=[]" *)
  apply (simp add: not_nil)
  apply (elim conjE exE)
  apply (simp)
  apply (elim disjE conjE exE)

  (* 3-AttL *)
  apply (simp)  (* guardR (nextL (AttL (n, x) # aa # ta)) *)
  apply (case_tac "guardR ta")
   apply (cspF_unwind)
   apply (cspF_hsf)+
   apply (rule)  (* 1i |~| 2i *)

   (* 1i *)
   apply (cspF_unwind)
   apply (cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    apply (elim disjE conjE exE)  (* left | right *)
   (* 1/2 *)(* left *)
    apply (simp)
    apply (cspF_simp)+
     apply (rule)  (* 1ii |~| 2ii *)

     (* 1ii *)
     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="AttR (na div 2) # AttL (n,x) # t" in exI)
     apply (simp)

     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

     (* 2ii *)
     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x=
        "AttC (fill (na div 2 + n div 2)) # 
         (AttL (fill (n div 2 + x), aaa div 2)) # nextL t" in exI)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

   (* 2/2 *)(* right *)
     apply (simp add: image_iff)
     apply (elim conjE exE)
     apply (simp)
     apply (cspF_simp)+

      apply (rule)  (* 1iii |~| 2iii *)

      (* 1iii *)
      apply (rule cspF_Rep_int_choice_left)
      apply (simp)
      apply (rule_tac x=
        "AttC na # AttL (n, x) # nextR (AttL (aaa, b) # ta, xa)" in exI)
      apply (simp)
      apply (simp add: nextL_nextR_order[THEN sym])

      apply (rule cspF_decompo)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)+
      apply (cspF_unwind)
      apply (cspF_hsf)+
      apply (simp add: image_iff)

      (* 2iii *)
      apply (rule cspF_Rep_int_choice_left)
      apply (simp)
      apply (rule_tac x="AttL (na, n div 2) # AttL (fill (n div 2 + x), aaa div 2) # 
                         nextR (nextL (AttL (aaa, b) # ta), xa)" in exI)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)+
      apply (cspF_unwind)
      apply (cspF_hsf)+

   (* 2i *)
   apply (cspF_unwind)
   apply (cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    apply (elim disjE conjE exE)  (* left | right *)
   (* 1/2 *)(* left *)
    apply (simp)
    apply (cspF_simp)+

     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x=
         "AttC (fill (na div 2 + n div 2)) # 
         (AttL (fill (n div 2 + x), aaa div 2)) # nextL t" in exI)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

   (* 2/2 *)(* right *)
     apply (simp add: image_iff)
     apply (elim conjE exE)
     apply (simp)
     apply (cspF_simp)+

      apply (rule cspF_Rep_int_choice_left)
      apply (simp)
      apply (rule_tac x=
         "AttL (na, n div 2) # AttL (fill (n div 2 + x), aaa div 2) # 
          nextR (nextL (AttL (aaa, b) # ta), xa)" in exI)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)+
      apply (cspF_unwind)
      apply (cspF_hsf)+

  (* "guardR ta" *)
   apply (cspF_unwind)
   apply (cspF_hsf)+
   apply (rule)  (* 1i |~| 2i *)

   (* 1i *)
   apply (cspF_unwind)
   apply (cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    apply (elim disjE conjE exE)  (* left | right *)
   (* 1/2 *)(* left *)
    apply (simp)
    apply (cspF_simp)+
     apply (rule)  (* 1ii |~| 2ii *)

     (* 1ii *)
     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="AttR (na div 2) # AttL (n,x) # t" in exI)
     apply (simp)

     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

     (* 2ii *)
     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x=
          "AttC (fill (na div 2 + n div 2)) # 
          (AttL (fill (n div 2 + x), aaa div 2)) # nextL t" in exI)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

   (* 2/2 *)(* right *)
     apply (simp add: image_iff)
     apply (elim conjE exE)
     apply (simp)
     apply (cspF_simp)+

      (* 2iii *)
      apply (rule cspF_Rep_int_choice_left)
      apply (simp)
      apply (rule_tac x=
         "AttL (na, n div 2) # AttL (fill (n div 2 + x), aaa div 2) # 
          nextR (nextL (AttL (aaa, b) # ta), xa)" in exI)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)+
      apply (cspF_unwind)
      apply (cspF_hsf)+

   (* 2i *)
   apply (cspF_unwind)
   apply (cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    apply (elim disjE conjE exE)  (* left | right *)
   (* 1/2 *)(* left *)
    apply (simp)
    apply (cspF_simp)+

     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x=
          "AttC (fill (na div 2 + n div 2)) # 
          (AttL (fill (n div 2 + x), aaa div 2)) # nextL t" in exI)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

   (* 2/2 *)(* right *)
     apply (simp add: image_iff)
     apply (elim conjE exE)
     apply (simp)
     apply (cspF_simp)+

      apply (rule cspF_Rep_int_choice_left)
      apply (simp)
      apply (rule_tac x="AttL (na, n div 2) # AttL (fill (n div 2 + x), aaa div 2) # 
                         nextR (nextL (AttL (aaa, b) # ta), xa)" in exI)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)+
      apply (cspF_unwind)
      apply (cspF_hsf)+

  (* 3-AttC *)
   apply (cspF_unwind)
   apply (cspF_hsf)+
   apply (rule)  (* 1i |~| 2i *)

   (* 1i *)
   apply (cspF_unwind)
   apply (cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    apply (elim disjE conjE exE)  (* left | right *)
   (* 1/2 *)(* left *)
    apply (simp)
    apply (cspF_simp)+
     apply (rule)  (* 1ii |~| 2ii *)

     (* 1ii *)
     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="AttR (na div 2) # AttL (n,x) # t" in exI)
     apply (simp)

     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

     (* 2ii *)
     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x=
        "AttC (fill (na div 2 + n div 2)) # 
        (AttL (fill (n div 2 + x), xa div 2)) # nextL t" in exI)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

   (* 2/2 *)(* right *)
     apply (simp add: image_iff)
     apply (elim conjE exE)
     apply (simp)
     apply (cspF_simp)+
      apply (rule)  (* 1iii |~| 2iii *)

      (* 1iii *)
      apply (rule cspF_Rep_int_choice_left)
      apply (simp)
      apply (rule_tac x=
         "AttC na # AttL (n, x) # nextR (AttC xa # ta, xaa)" in exI)
      apply (simp)
      apply (simp add: nextL_nextR_order)

      apply (rule cspF_decompo)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)+
      apply (cspF_unwind)
      apply (cspF_hsf)+
      apply (simp add: image_iff)

      (* 2iii *)
      apply (rule cspF_Rep_int_choice_left)
      apply (simp)
      apply (rule_tac x=
        "AttL (na, n div 2) # AttL (fill (n div 2 + x), xa div 2) #
         nextR (AttR (xa div 2) # ta, xaa)" in exI)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)+
      apply (cspF_unwind)
      apply (cspF_hsf)+

   (* 2i *)
   apply (cspF_unwind)
   apply (cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    apply (elim disjE conjE exE)  (* left | right *)
   (* 1/2 *)(* left *)
    apply (simp)
    apply (cspF_simp)+

     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x=
          "AttC (fill (na div 2 + n div 2)) #
          (AttL (fill (n div 2 + x), xa div 2)) # nextL t" in exI)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

   (* 2/2 *)(* right *)
     apply (simp add: image_iff)
     apply (elim conjE exE)
     apply (simp)
     apply (cspF_simp)+

      apply (rule cspF_Rep_int_choice_left)
      apply (simp)
      apply (rule_tac x=
         "AttL (na, n div 2) # AttL (fill (n div 2 + x), xa div 2) # 
          nextR (AttR (xa div 2) # ta, xaa)" in exI)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)+
      apply (cspF_unwind)
      apply (cspF_hsf)+

  (* 3-AttR *)
   apply (cspF_unwind)
   apply (cspF_hsf)+
   apply (rule)  (* 1i |~| 2i *)

   (* 1i *)
   apply (cspF_unwind)
   apply (cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    apply (elim disjE conjE exE)  (* left | right *)
   (* 1/2 *)(* left *)
    apply (simp)
    apply (cspF_simp)+
     apply (rule)  (* 1ii |~| 2ii *)

     (* 1ii *)
     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="AttR (na div 2) # AttL (n,x) # AttR xa # ta" in exI)
     apply (simp)

     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

     (* 2ii *)
     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x=
       "AttC (fill (na div 2 + n div 2)) # 
       (AttC (fill (n div 2 + x))) # t" in exI)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

   (* 2/2 *)(* right *)
     apply (simp add: image_iff)
     apply (elim conjE exE)
     apply (simp)
     apply (cspF_simp)+
      apply (rule)  (* 1iii |~| 2iii *)

      (* 1iii *)
      apply (rule cspF_Rep_int_choice_left)
      apply (simp)
      apply (rule_tac x=
         "AttC na # AttL (n, x) # nextR (AttR xa # ta, xaa)" in exI)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)+
      apply (cspF_unwind)
      apply (cspF_hsf)+
      apply (simp add: image_iff)

      (* 2iii *)
      apply (rule cspF_Rep_int_choice_left)
      apply (simp)
      apply (rule_tac x=
              "AttL (na, n div 2) # 
               AttL (fill (n div 2 + x), getNat (hd (updateR (AttR xa # ta, xaa))) ) #
               updateR (AttR xa # ta, xaa)" in exI)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)+
      apply (cspF_unwind)
      apply (cspF_hsf)+

   (* 2i *)
   apply (cspF_unwind)
   apply (cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    apply (elim disjE conjE exE)  (* left | right *)
   (* 1/2 *)(* left *)
    apply (simp)
    apply (cspF_simp)+

     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="AttC (fill (na div 2 + n div 2)) # 
                       (AttC (fill (n div 2 + x)) # AttR xa # ta)" in exI)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

   (* 2/2 *)(* right *)
     apply (simp add: image_iff)
     apply (elim conjE exE)
     apply (simp)
     apply (cspF_simp)+

      apply (rule cspF_Rep_int_choice_left)
      apply (simp)
      apply (rule_tac x="AttL (na, n div 2) # 
            AttL (fill (n div 2 + x), getNat (hd (updateR (AttR xa # ta, xaa)))) # 
            updateR (AttR xa # ta, xaa)" in exI)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)
      apply (rule cspF_decompo)
      apply (simp)+
      apply (cspF_unwind)
      apply (cspF_hsf)+
done

lemma LineSpec_Step_ref1_AttR_AttL:
   "[| ChkLCR (toStbOne (AttR na # AttL (n, x) # t));
          list = toStbOne (AttR na # AttL (n, x) # t); a = AttR na # AttL (n, x) # t;
          a1 = AttR na; a2 = AttL (n, x) |]
       ==> (IF guardL (toStbOne (AttR na # AttL (n, x) # t)) 
           THEN (left ! (getNat (hd (toStbOne (AttR na # AttL (n, x) # t))) div 2) 
                 -> IF ChkLCR (nextL (toStbOne (AttR na # AttL (n, x) # t))) 
                    THEN IF (tl (nextL (toStbOne (AttR na # AttL (n, x) # t))) = []) 
                         THEN ($LineSpec (nextL (toStbOne (AttR na # AttL (n, x) # t)))) 
                         ELSE (!<stlist> t:{ta. toStbOne ta =
  nextL (toStbOne (AttR na # AttL (n, x) # t))} .. 
                               ChildAtt (hd t) <---> $LineSpec (tl t)) 
                    ELSE STOP) 
           ELSE STOP) 
            [+] (IF guardR (toStbOne (AttR na # AttL (n, x) # t)) 
                THEN (right ? xa 
                      -> IF ChkLCR (nextR (toStbOne (AttR na # AttL (n, x) # t), xa)) 
                         THEN IF (tl (nextR (toStbOne (AttR na # AttL (n, x) # t), xa)) =
                                  []) 
                              THEN ($LineSpec
                                     (nextR (toStbOne (AttR na # AttL (n, x) # t), xa))) 
                              ELSE (!<stlist> t:{ta.
   toStbOne ta = nextR (toStbOne (AttR na # AttL (n, x) # t), xa)} .. 
                                    ChildAtt (hd t) <---> $LineSpec (tl t)) 
                         ELSE STOP) 
                ELSE STOP) 
           <=F $ChildR na <---> $LineSpec (AttL (n, x) # t)"
  apply (case_tac "t=[]")
  apply (cspF_unwind)
  apply (cspF_simp)+
  apply (cspF_hsf_right)+
  apply (rule cspF_tr_right)
  apply (rule LineSpec_Step_ref1_AttC_AttC)
  apply (simp_all)
  apply (cspF_simp)+

  (* "t~=[]" *)
  apply (simp add: not_nil)
  apply (elim conjE exE)
  apply (simp)
  apply (insert Att_or)
  apply (drule_tac x="aa" in spec)
  apply (elim disjE exE)
  apply (simp_all)

  (* 3-AttL *)
   apply (case_tac "~ guardR ta")
   apply (cspF_unwind)
   apply (cspF_hsf_right)+
   apply (rule cspF_tr_right)
   apply (rule LineSpec_Step_ref1_AttC_AttL)
   apply (simp_all)
   apply (cspF_simp)+

   (* guardR ta *)
   apply (cspF_unwind)
   apply (cspF_hsf_right)+
   apply (rule)  (* 1i |~| 2i (C-L) *)

   (* 1i *)
   apply (cspF_unwind)
   apply (cspF_hsf)+  
    apply (rule)  (* 1ii |~| 2ii *)

    (* 1ii *)
    apply (cspF_unwind)
    apply (cspF_hsf_right)+ 

     (* rem head *)
     apply (rule)
     apply (simp)
     apply (simp)
      apply (elim disjE conjE exE)  (* left | right *)
     (* 1/2 *)(* left *)
      apply (simp)
      apply (cspF_simp)+
       apply (rule)  (* 1iii |~| 2iii *)

       (* 1iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)
       apply (subgoal_tac "ta ~=[]")
       apply (simp add: not_nil)
       apply (elim exE)
       apply (simp)
       apply (elim disjE conjE exE)
       apply (simp_all)

        (* AttL *)
        apply (rule_tac x=
                   "AttR (fill (na + n div 2) div 2) # 
                    AttL (fill (n div 2 + x),nb div 2) # 
                    AttL (fill (nb div 2 + xa), ac div 2) # 
                    nextL (AttL (ac, b) # taa)" in exI)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf)+

       (* AttC *)
        apply (rule_tac x=
                   "AttR (fill (na + n div 2) div 2) # 
                    AttL (fill (n div 2 + x),nb div 2) # 
                    AttL (fill (nb div 2 + xa), xaa div 2) #
                   (AttR (xaa div 2) # taa)" in exI)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind_left)
        apply (cspF_hsf_left)+

        (* AttR *)
        apply (rule_tac x=
                   "AttR (fill (na + n div 2) div 2) # 
                    AttL (fill (n div 2 + x),nb div 2) #
                    AttC (fill (nb div 2 + xa)) # 
                   (AttR xaa # taa)" in exI)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind_left)
        apply (cspF_hsf_left)+

        apply (simp add: guardR_last)

       (* 2iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)
       apply (subgoal_tac "ta ~=[]")
       apply (simp add: not_nil)
       apply (elim exE)
       apply (simp)
       apply (elim disjE conjE exE)
       apply (simp_all)

        (* AttL *)
        apply (rule_tac x=
    "AttC (fill (fill (na + n div 2) div 2 + fill (n div 2 + x) div 2)) #
     AttL (fill (fill (n div 2 + x) div 2 + nb div 2), fill (nb div 2 + xa) div 2) # 
     AttL (fill (fill (nb div 2 + xa) div 2 + ac div 2), fill (ac div 2 + b) div 2) # 
     nextL (nextL(AttL (ac, b) # taa))" in exI)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf_left)+

       (* AttC *)
        apply (rule_tac x=
     "AttC (fill (fill (na + n div 2) div 2 + fill (n div 2 + x) div 2)) # 
     (AttL (fill (fill (n div 2 + x) div 2 + nb div 2),fill (nb div 2 + xa) div 2)) # 
     (AttC (fill (fill (nb div 2 + xa) div 2 + xaa div 2))) # 
      AttR (xaa div 2) # taa" in exI)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind_left)
        apply (cspF_hsf_left)+

        (* AttR *)
        apply (rule_tac x=
    "AttC (fill (fill (na + n div 2) div 2 + fill (n div 2 + x) div 2)) # 
     AttL (fill (fill (n div 2 + x) div 2 + nb div 2),fill (nb div 2 + xa) div 2) #
     AttR (fill (nb div 2 + xa) div 2) #  AttR xaa # taa" in exI)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind_left)
        apply (cspF_hsf_left)+

        apply (simp add: guardR_last)

    (* 2/2 *)(* right *)
      apply (simp add: image_iff)
      apply (elim conjE exE)
      apply (simp)
      apply (cspF_simp)+

       apply (rule)  (* 1iii |~| 2iii |~| 3iii *)
       apply (rule)

       (* 1iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)

        apply (rule_tac x=
                   "AttR na # 
                    AttL (n,x) # 
                    AttL (nb, xa) # 
                    nextR (ta,xaa)" in exI)
        apply (simp)
        apply (simp add: nextR_nextL_nextL_order_AttL)
        apply (simp add: nextL_nextR_order[THEN sym])
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf)+

       (* 2iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)

        apply (rule_tac x=
                   "AttC (fill (na + n div 2)) # 
                    AttL (fill (n div 2 + x),nb div 2) # 
                    AttL (fill (nb div 2 + xa), getNat (hd (nextR (ta, xaa))) div 2) # 
                    nextL (nextR (ta,xaa))" in exI)
        apply (simp)
        apply (simp add: nextR_nextL_nextL_order_AttL)
        apply (simp add: nextL_nextR_order[THEN sym])

        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf)+
        apply (simp add: image_iff)

       (* 3iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)

        apply (rule_tac x=
          "AttL (fill (na + n div 2), fill (n div 2 + x) div 2) # 
           AttL (fill (fill (n div 2 + x) div 2 + nb div 2),fill (nb div 2 + xa) div 2) # 
           nextR (nextL (nextL (AttL (nb, xa) # ta)), xaa)" in exI)
        apply (simp)

        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf)+

    (* 2ii *)
    apply (cspF_unwind)
    apply (cspF_hsf_right)+ 

     (* rem head *)
     apply (rule)
     apply (simp)
     apply (simp)
      apply (elim disjE conjE exE)  (* left | right *)
     (* 1/2 *)(* left *)
      apply (simp)
      apply (cspF_simp)+

       (* 2iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)
       apply (subgoal_tac "ta ~=[]")
       apply (simp add: not_nil)
       apply (elim exE)
       apply (simp)
       apply (elim disjE conjE exE)
       apply (simp_all)

        (* AttL *)
        apply (rule_tac x=
   "AttC (fill (fill (na + n div 2) div 2 + fill (n div 2 + x) div 2)) #
    AttL (fill (fill (n div 2 + x) div 2 + nb div 2), fill (nb div 2 + xa) div 2) # 
    AttL (fill (fill (nb div 2 + xa) div 2 + ac div 2), fill (ac div 2 + b) div 2) # 
    nextL (nextL(AttL (ac, b) # taa))" in exI)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf_left)+

       (* AttC *)
        apply (rule_tac x=
    "AttC (fill (fill (na + n div 2) div 2 + fill (n div 2 + x) div 2)) # 
    (AttL (fill (fill (n div 2 + x) div 2 + nb div 2),fill (nb div 2 + xa) div 2)) # 
    (AttC (fill (fill (nb div 2 + xa) div 2 + xaa div 2))) # AttR (xaa div 2) # taa" in exI)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind_left)
        apply (cspF_hsf_left)+

        (* AttR *)
        apply (rule_tac x=
   "AttC (fill (fill (na + n div 2) div 2 + fill (n div 2 + x) div 2)) # 
    AttL (fill (fill (n div 2 + x) div 2 + nb div 2),fill (nb div 2 + xa) div 2) #
    AttR (fill (nb div 2 + xa) div 2) #  AttR xaa # taa" in exI)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind_left)
        apply (cspF_hsf_left)+

        apply (simp add: guardR_last)

    (* 2/2 *)(* right *)
      apply (simp add: image_iff)
      apply (elim conjE exE)
      apply (simp)
      apply (cspF_simp)+

       apply (rule)  (* 1iii |~| 3iii *)

       (* 1iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)

        apply (rule_tac x="AttR na # 
                    AttL (n,x) # 
                    AttL (nb, xa) # 
                    nextR (ta,xaa)" in exI)
        apply (simp)
        apply (simp add: nextR_nextL_nextL_order_AttL)
        apply (simp add: nextL_nextR_order[THEN sym])
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf)+

       (* 3iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)

        apply (rule_tac x=
     "AttL (fill (na + n div 2), fill (n div 2 + x) div 2) # 
      AttL (fill (fill (n div 2 + x) div 2 + nb div 2),fill (nb div 2 + xa) div 2) # 
      nextR (nextL (nextL (AttL (nb, xa) # ta)), xaa)" in exI)
        apply (simp)

        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf)+

   (* 2i (C-L) *)
   apply (rule cspF_tr_right)
   apply (rule LineSpec_Step_ref1_AttC_AttL)
   apply (simp_all)
   apply (cspF_simp)+
   apply (cspF_hsf)+

  (* 3-AttC *)
   apply (cspF_unwind)
   apply (cspF_hsf_right)+

   (* guardR ta (ChkR ta) *)
   apply (rule)  (* 1i |~| 2i (C-L) *)

   (* 1i *)
   apply (cspF_unwind)
   apply (cspF_hsf)+
    apply (rule)  (* 1ii |~| 2ii *)

    (* 1ii *)
    apply (cspF_unwind)
    apply (cspF_hsf_right)+ 

     (* rem head *)
     apply (rule)
     apply (simp)
     apply (simp)
      apply (elim disjE conjE exE)  (* left | right *)
     (* 1/2 *)(* left *)
      apply (simp)
      apply (cspF_simp)+
       apply (rule)  (* 1iii |~| 2iii *)

       (* 1iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)
        apply (rule_tac x="AttR (fill (na + n div 2) div 2) # 
                    AttL (fill (n div 2 + x),nb div 2) #
                    AttR (nb div 2) #
                    ta" in exI)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf)+

       (* 2iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)
        apply (rule_tac x=
          "AttC (fill (fill (na + n div 2) div 2 + fill (n div 2 + x) div 2)) #
           AttC (fill (fill (n div 2 + x) div 2 + nb div 2)) # 
           AttR (nb div 2) #
           ta" in exI)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf_left)+

    (* 2/2 *)(* right *)
      apply (simp add: image_iff)
      apply (elim conjE exE)
      apply (simp)
      apply (cspF_simp)+

       apply (rule)  (* 1iii |~| 2iii |~| 3iii *)
       apply (rule)

       (* 1iii *)
        apply (rule cspF_Rep_int_choice_left)
        apply (simp)

         apply (case_tac "ta=[]")
         apply (rule_tac x="AttR na # 
                    AttL (n,x) # 
                    AttL (nb, xa) # []" in exI)
         apply (simp)
         apply (rule cspF_decompo)
         apply (simp)
         apply (rule cspF_decompo)
         apply (simp)+
         apply (cspF_unwind)
         apply (cspF_hsf)+

         (* "ta ~= [] *)
         apply (simp add: not_nil)
         apply (elim exE conjE)
         apply (simp)
         apply (elim exE conjE)
         apply (simp)
         apply (rule_tac x=
            "AttR na # 
             AttL (n,x) # 
             AttL (nb, getNat (hd (updateR (ta, xa))) ) # updateR (ta, xa)" in exI)
         apply (simp)
         apply (rule cspF_decompo)
         apply (simp)
         apply (rule cspF_decompo)
         apply (simp)+
         apply (cspF_unwind)
         apply (cspF_hsf)+

       (* 2iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)

        apply (rule_tac x=
          "AttC (fill (na + n div 2)) # 
           AttL (fill (n div 2 + x),nb div 2) # 
           nextR (AttR (nb div 2) # ta, xa)" in exI)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf)+
        apply (simp add: image_iff)

       (* 3iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)

        apply (rule_tac x=
          "AttL (fill (na + n div 2), fill (n div 2 + x) div 2) # 
          (AttL (fill (fill (n div 2 + x) div 2 + nb div 2),
                 getNat (hd (updateR (AttR (nb div 2) # ta, xa))) ) #
           updateR (AttR (nb div 2) # ta, xa))" in exI)
        apply (simp)

        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf)+

    (* 2ii *)
    apply (cspF_unwind)
    apply (cspF_hsf_right)+ 

     (* rem head *)
     apply (rule)
     apply (simp)
     apply (simp)
      apply (elim disjE conjE exE)  (* left | right *)
     (* 1/2 *)(* left *)
      apply (simp)
      apply (cspF_simp)+

       (* 2iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)
        apply (rule_tac x=
     "AttC (fill (fill (na + n div 2) div 2 + fill (n div 2 + x) div 2)) #
      AttC (fill (fill (n div 2 + x) div 2 + nb div 2)) # 
      AttR (nb div 2) # ta" in exI)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf_left)+

    (* 2/2 *)(* right *)
      apply (simp add: image_iff)
      apply (elim conjE exE)
      apply (simp)
      apply (cspF_simp)+

       apply (rule)  (* 1iii |~| 3iii *)

       (* 1iii *)
        apply (rule cspF_Rep_int_choice_left)
        apply (simp)

         apply (case_tac "ta=[]")
         apply (rule_tac x="AttR na # 
                    AttL (n,x) # 
                    AttL (nb, xa) # []" in exI)
         apply (simp)
         apply (rule cspF_decompo)
         apply (simp)
         apply (rule cspF_decompo)
         apply (simp)+
         apply (cspF_unwind)
         apply (cspF_hsf)+

         (* "ta ~= [] *)
         apply (simp add: not_nil)
         apply (elim exE conjE)
         apply (simp)
         apply (elim exE conjE)
         apply (simp)
         apply (rule_tac x=
            "AttR na # 
             AttL (n,x) # 
             AttL (nb, getNat (hd (updateR (ta, xa))) ) # updateR (ta, xa)" in exI)
         apply (simp)
         apply (rule cspF_decompo)
         apply (simp)
         apply (rule cspF_decompo)
         apply (simp)+
         apply (cspF_unwind)
         apply (cspF_hsf)+

       (* 3iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)

        apply (rule_tac x=
           "AttL (fill (na + n div 2), fill (n div 2 + x) div 2) # 
           (AttL (fill (fill (n div 2 + x) div 2 + nb div 2),
                        getNat (hd (updateR (AttR (nb div 2) # ta, xa))) ) #
            updateR (AttR (nb div 2) # ta, xa))" in exI)
        apply (simp)

        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf)+

   (* 2i (C-L) *)
   apply (rule cspF_tr_right)
   apply (rule LineSpec_Step_ref1_AttC_AttL)
   apply (simp_all)
   apply (cspF_simp)+
   apply (cspF_hsf)+


  (* 3-AttR *)
   apply (cspF_unwind)
   apply (cspF_hsf_right)+

   apply (rule)  (* 1i |~| 2i (C-C) *)

   (* 1i *)
   apply (cspF_unwind)
   apply (cspF_hsf_right)+
    apply (rule)  (* 1ii |~| 2ii *)

    (* 1ii *)
    apply (cspF_unwind)
    apply (cspF_hsf_right)+ 

     (* rem head *)
     apply (rule)
     apply (simp)
     apply (simp)
      apply (elim disjE conjE exE)  (* left | right *)
     (* 1/2 *)(* left *)
      apply (simp)
      apply (cspF_simp)+
       apply (rule)  (* 1iii |~| 2iii *)

       (* 1iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)
        apply (rule_tac x=
            "AttR (fill (na + n div 2) div 2) #
            (AttC (fill (n div 2 + x)) #
            (AttR nb # ta))" in exI)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf)+

       (* 2iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)
        apply (rule_tac x=
          "AttC (fill (fill (na + n div 2) div 2 + fill (n div 2 + x) div 2)) #
          (AttR (fill (n div 2 + x) div 2) #
          (AttR nb # ta))" in exI)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf_left)+

    (* 2/2 *)(* right *)
      apply (simp add: image_iff)
      apply (elim conjE exE)
      apply (simp)
      apply (cspF_simp)+

       apply (rule)  (* 1iii |~| 2iii |~| 3iii *)
       apply (rule)

       (* 1iii *)
        apply (rule cspF_Rep_int_choice_left)
        apply (simp)
         apply (rule_tac x=
                   "AttR na # 
                    AttL (n,x) # 
                    AttC (getNat (hd (updateR (AttR nb # ta, xa))) * 2) # 
                    updateR (ta, xa)" in exI)
         apply (simp)

         apply (case_tac "ta=[]")
         apply (simp)
         apply (rule cspF_decompo)
         apply (simp)
         apply (rule cspF_decompo)
         apply (simp)+
         apply (cspF_unwind)
         apply (cspF_hsf)+

         (* "ta ~= [] *)
         apply (simp add: not_nil)
         apply (elim exE conjE)
         apply (simp)
         apply (elim exE conjE)
         apply (simp)
         apply (rule cspF_decompo)
         apply (simp)
         apply (rule cspF_decompo)
         apply (simp)+
         apply (cspF_unwind)
         apply (cspF_hsf)+

       (* 2iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)

        apply (rule_tac x=
          "AttC (fill (na + n div 2)) #
           AttL (fill (n div 2 + x),getNat (hd (updateR (AttR nb # ta, xa))) ) # 
           updateR (AttR nb # ta, xa)" in exI)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf)+
        apply (simp add: image_iff)

       (* 3iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)

        apply (rule_tac x=
          "AttL (fill (na + n div 2),fill (n div 2 + x) div 2) #
           AttC (fill (fill (n div 2 + x) div 2 + 
                       getNat (hd (updateR (AttR nb # ta, xa))) )) #
           updateR (AttR nb # ta, xa)" in exI)
        apply (simp)

        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf)+

    (* 2ii *)
    apply (cspF_unwind)
    apply (cspF_hsf_right)+ 

     (* rem head *)
     apply (rule)
     apply (simp)
     apply (simp)
      apply (elim disjE conjE exE)  (* left | right *)
     (* 1/2 *)(* left *)
      apply (simp)
      apply (cspF_simp)+

       (* 2iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)
        apply (rule_tac x=
          "AttC (fill (fill (na + n div 2) div 2 + fill (n div 2 + x) div 2)) #
          (AttR (fill (n div 2 + x) div 2) #
          (AttR nb # ta))" in exI)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf_left)+

    (* 2/2 *)(* right *)
      apply (simp add: image_iff)
      apply (elim conjE exE)
      apply (simp)
      apply (cspF_simp)+

       apply (rule)  (* 1iii |~| 3iii *)

       (* 1iii *)
        apply (rule cspF_Rep_int_choice_left)
        apply (simp)
         apply (rule_tac x=
             "AttR na # 
              AttL (n,x) # 
              AttC (getNat (hd (updateR (AttR nb # ta, xa))) * 2) # 
              updateR (ta, xa)" in exI)
         apply (simp)

         apply (case_tac "ta=[]")
         apply (simp)
         apply (rule cspF_decompo)
         apply (simp)
         apply (rule cspF_decompo)
         apply (simp)+
         apply (cspF_unwind)
         apply (cspF_hsf)+

         (* "ta ~= [] *)
         apply (simp add: not_nil)
         apply (elim exE conjE)
         apply (simp)
         apply (elim exE conjE)
         apply (simp)
         apply (rule cspF_decompo)
         apply (simp)
         apply (rule cspF_decompo)
         apply (simp)+
         apply (cspF_unwind)
         apply (cspF_hsf)+

       (* 3iii *)
       apply (rule cspF_Rep_int_choice_left)
       apply (simp)

        apply (rule_tac x=
          "AttL (fill (na + n div 2),fill (n div 2 + x) div 2) #
           AttC (fill (fill (n div 2 + x) div 2 + 
                       getNat (hd (updateR (AttR nb # ta, xa))) )) #
           updateR (AttR nb # ta, xa)" in exI)
        apply (simp)

        apply (rule cspF_decompo)
        apply (simp)
        apply (rule cspF_decompo)
        apply (simp)+
        apply (cspF_unwind)
        apply (cspF_hsf)+

   (* 2i (C-C) *)
   apply (rule cspF_tr_right)
   apply (rule LineSpec_Step_ref1_AttC_AttC)
   apply (simp_all)
   apply (cspF_simp)+
   apply (cspF_hsf)+
done


lemma LineSpec_Step_ref1_AttC_AttR:
      "[| ChkR t; list = AttC n # AttR na # t; a = AttC n # AttR na # t; a1 = AttC n;
          a2 = AttR na |]
       ==> (IF True 
           THEN (left ! (n div 2) 
                 -> IF True 
                    THEN IF False THEN ($LineSpec (AttR (n div 2) # AttR na # t)) 
                         ELSE (!<stlist> t:{ta. toStbOne ta =
  AttR (n div 2) # AttR na # t} .. 
                               ChildAtt (hd t) <---> $LineSpec (tl t)) 
                    ELSE STOP) 
           ELSE STOP) 
            [+] (IF True 
                THEN (right ? x 
                      -> IF True 
                         THEN IF (updateR (AttR na # t, x) = []) 
                              THEN ($LineSpec
                                     (AttL (n, getNat (hd (updateR (AttR na # t, x)))) #
                                      updateR (AttR na # t, x))) 
                              ELSE (!<stlist> t:{ta.
   toStbOne ta =
   AttL (n, getNat (hd (updateR (AttR na # t, x)))) # updateR (AttR na # t, x)} .. 
                                    ChildAtt (hd t) <---> $LineSpec (tl t)) 
                         ELSE STOP) 
                ELSE STOP) 
           <=F $Child n <---> $LineSpec (AttR na # t)"
 apply (cspF_unwind)
 apply (cspF_hsf)+
 apply (rule)
 apply (simp)
 apply (simp)
 apply (elim disjE conjE exE)

 (* left *)
 apply (simp)
 apply (cspF_simp)+
 apply (rule cspF_Rep_int_choice_left)
 apply (simp)
 apply (rule_tac x="AttR (n div 2) # AttR na # t" in exI)
 apply (simp)
 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_decompo)
 apply (simp)+
 apply (cspF_unwind)
 apply (cspF_hsf)+

 (* right *)
 apply (simp add: image_iff)
 apply (elim conjE exE)
 apply (simp)
 apply (cspF_simp)+
 apply (case_tac "t=[]")
  apply (simp)
  apply (cspF_simp)+
  apply (rule cspF_Rep_int_choice_left)
  apply (simp)
  apply (rule_tac x="AttC n # (AttC (fill (na + x)) # t)" in exI)
  apply (simp)
  apply (rule cspF_decompo)
  apply (simp)
  apply (rule cspF_decompo)
  apply (simp)+
  apply (cspF_unwind)
  apply (cspF_hsf)+
  apply (simp add: image_iff)

 (* t ~=[] *)
  apply (simp add: not_nil)
  apply (elim exE conjE)
  apply (simp)
  apply (elim exE conjE)
  apply (simp)
  apply (cspF_simp)+
  apply (rule cspF_Rep_int_choice_left)
  apply (simp)
  apply (rule_tac x="AttC n # 
   (AttC (fill (na + getNat (hd (updateR (AttR xa # ta, x))) )) # 
    updateR (t,x))" in exI)
  apply (simp)
  apply (rule cspF_decompo)
  apply (simp)
  apply (rule cspF_decompo)
  apply (simp)+
  apply (cspF_unwind)
  apply (cspF_hsf)+
  apply (simp add: image_iff)
done


lemma LineSpec_Step_ref1_AttR_AttC:
     "[| ChkR t; list = AttC (fill (n + na div 2)) # AttR (na div 2) # t;
          a = AttR n # AttC na # t; a1 = AttR n; a2 = AttC na |]
       ==> (IF True 
           THEN (left ! (fill (n + na div 2) div 2) 
                 -> IF True 
                    THEN IF False 
                         THEN ($LineSpec
                                (AttR (fill (n + na div 2) div 2) # AttR (na div 2) # t)) 
                         ELSE (!<stlist> t:{ta. toStbOne ta =
  AttR (fill (n + na div 2) div 2) # AttR (na div 2) # t} .. 
                               ChildAtt (hd t) <---> $LineSpec (tl t)) 
                    ELSE STOP) 
           ELSE STOP) 
            [+] (IF True 
                THEN (right ? x 
                      -> IF True 
                         THEN IF (updateR (AttR (na div 2) # t, x) = []) 
                              THEN ($LineSpec
                                     (AttL (fill (n + na div 2),
                                            getNat
                               (hd (updateR (AttR (na div 2) # t, x)))) #
                                      updateR (AttR (na div 2) # t, x))) 
                              ELSE (!<stlist> t:{ta.
        toStbOne ta =
        AttL (fill (n + na div 2), getNat (hd (updateR (AttR (na div 2) # t, x)))) #
        updateR (AttR (na div 2) # t, x)} .. 
                                    ChildAtt (hd t) <---> $LineSpec (tl t)) 
                         ELSE STOP) 
                ELSE STOP) 
           <=F $ChildR n <---> $LineSpec (AttC na # t)"

  apply (case_tac "t=[]")
  apply (cspF_unwind)
  apply (cspF_hsf)+
  apply (rule)  (* 1i |~| 2i (C-R) *)

  (* 1i *)
   apply (cspF_unwind)
   apply (cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    apply (elim disjE conjE exE)  (* left | right *)
   (* 1/2 *)(* left *)
    apply (simp)
    apply (cspF_simp)+

     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="AttR (fill (n + na div 2) div 2) # AttR (na div 2) # t" in exI)
     apply (simp)

     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

   (* 2/2 *)(* right *)
     apply (simp add: image_iff)
     apply (elim conjE exE)
     apply (simp)
     apply (cspF_simp)+
     apply (rule)  (* 1ii |~| 2ii *)

     (* 1ii *)
     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="AttR n # AttL (na, x) # t" in exI)
     apply (simp)

     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

     (* 2ii *)
     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="
          AttC (fill (n + na div 2)) #
          AttC (fill (na div 2 + x)) # t" in exI)
     apply (simp)

     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf_left)+
     apply (simp add: image_iff)

  (* 2i *)
   apply (rule cspF_tr_right)
   apply (rule LineSpec_Step_ref1_AttC_AttR)
   apply (simp_all)
   apply (cspF_simp)+
   apply (cspF_hsf)+

  (* "t~=[]" *)
  apply (simp add: not_nil)
  apply (elim conjE exE)
  apply (simp)
  apply (elim disjE conjE exE)

  (* 3-AttR *)
   apply (cspF_unwind)
   apply (cspF_hsf)+
   apply (rule)  (* 1i |~| 2i (C-R) *)

   (* 1i *)
   apply (cspF_unwind)
   apply (cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    apply (elim disjE conjE exE)  (* left | right *)
   (* 1/2 *)(* left *)
    apply (simp)
    apply (cspF_simp)+

     apply (rule cspF_Rep_int_choice_left)
     apply (simp)
     apply (rule_tac x="AttR (fill (n + na div 2) div 2) # AttR (na div 2) # t" in exI)
     apply (simp)

     apply (rule cspF_decompo)
     apply (simp)
     apply (rule cspF_decompo)
     apply (simp)+
     apply (cspF_unwind)
     apply (cspF_hsf)+

   (* 2/2 *)(* right *)
     apply (simp add: image_iff)
     apply (elim conjE exE)
     apply (simp)
     apply (cspF_simp)+
      apply (rule)  (* 1iii |~| 2iii *)

      (* 1iii *)
      apply (rule cspF_Rep_int_choice_left)
      apply (simp)
      apply (rule_tac x=
        "AttR n # AttL (na,getNat (hd (updateR (AttR x # ta, xa))) ) # 
         updateR (AttR x # ta, xa)" in exI)
      apply (simp)
       apply (case_tac "ta=[]")
       apply (simp)
       apply (rule cspF_decompo)
       apply (simp)
       apply (rule cspF_decompo)
       apply (simp)+
       apply (cspF_unwind)
       apply (cspF_hsf)+

       (* "t~=[]" *)
       apply (simp add: not_nil)
       apply (elim conjE exE)
       apply (simp)
       apply (elim disjE conjE exE)
       apply (rule cspF_decompo)
       apply (simp)
       apply (rule cspF_decompo)
       apply (simp)+
       apply (cspF_unwind)
       apply (cspF_hsf)+

      (* 2iii *)
      apply (rule cspF_Rep_int_choice_left)
      apply (simp)

       apply (case_tac "ta=[]")
       apply (rule_tac x="
           AttC (fill (n + na div 2)) # 
           AttC (fill (na div 2 + fill (x + xa) div 2)) # 
           AttR (fill (x + xa) div 2) # ta" in exI)
       apply (simp)
       apply (rule cspF_decompo)
       apply (simp)
       apply (rule cspF_decompo)
       apply (simp)+
       apply (cspF_unwind)
       apply (cspF_hsf)+
       apply (simp add: image_iff)

       (* "t~=[]" *)
       apply (simp add: not_nil)
       apply (elim conjE exE)
       apply (simp)
       apply (elim disjE conjE exE)
       apply (rule_tac x="
           AttC (fill (n + na div 2)) # 
           AttC (fill (na div 2 + 
                       fill (x + getNat (hd (updateR (AttR xb # taa, xa))) ) div 2)) # 
           AttR (fill (x + getNat (hd (updateR (AttR xb # taa, xa)))) div 2) # 
           updateR (AttR xb # taa, xa)" in exI)
       apply (simp)
       apply (rule cspF_decompo)
       apply (simp)
       apply (rule cspF_decompo)
       apply (simp)+
       apply (cspF_unwind)
       apply (cspF_hsf)+
       apply (simp add: image_iff)

   (* 2i *)
   apply (rule cspF_tr_right)
   apply (rule LineSpec_Step_ref1_AttC_AttR)
   apply (simp_all)
   apply (cspF_simp)+
   apply (cspF_hsf)+
done

lemma LineSpec_Step_ref1_AttR_AttR:
      "[| ChkR t; list = AttR n # AttR na # t; a = AttR n # AttR na # t; a1 = AttR n;
          a2 = AttR na |]
       ==> (IF False 
           THEN (left ! (n div 2) 
                 -> IF False 
                    THEN IF False THEN ($LineSpec [AttR 0, AttC 0]) 
                         ELSE (!<stlist> t:{t. toStbOne t = [AttR 0, AttC 0]} .. 
                               ChildAtt (hd t) <---> $LineSpec (tl t)) 
                    ELSE STOP) 
           ELSE STOP) 
            [+] (IF True 
                THEN (right ? x 
                      -> IF True 
                         THEN IF (updateR (AttR na # t, x) = []) 
                              THEN ($LineSpec
                                     (AttC (fill
                       (n + getNat (hd (updateR (AttR na # t, x))))) #
                                      updateR (AttR na # t, x))) 
                              ELSE (!<stlist> t:{ta.
   toStbOne ta =
   AttC (fill (n + getNat (hd (updateR (AttR na # t, x))))) #
   updateR (AttR na # t, x)} .. 
                                    ChildAtt (hd t) <---> $LineSpec (tl t)) 
                         ELSE STOP) 
                ELSE STOP) 
           <=F $ChildR n <---> $LineSpec (AttR na # t)"
 apply (cspF_unwind)
 apply (cspF_hsf)+
 apply (rule)
 apply (simp)
 apply (simp)

 (* right *)
 apply (simp add: image_iff)
 apply (elim conjE exE)
 apply (simp)
 apply (cspF_simp)+
 apply (case_tac "t=[]")
  apply (simp)
  apply (cspF_simp)+
  apply (rule cspF_Rep_int_choice_left)
  apply (simp)
  apply (rule_tac x="AttR n # (AttC (fill (na + x)) # t)" in exI)
  apply (simp)
  apply (rule cspF_decompo)
  apply (simp)
  apply (rule cspF_decompo)
  apply (simp)+
  apply (cspF_unwind)
  apply (cspF_hsf)+

 (* t ~=[] *)
  apply (simp add: not_nil)
  apply (elim exE conjE)
  apply (simp)
  apply (elim exE conjE)
  apply (simp)
  apply (cspF_simp)+
  apply (rule cspF_Rep_int_choice_left)
  apply (simp)
  apply (rule_tac x="AttR n # 
   (AttC (fill (na + getNat (hd (updateR (AttR xa # ta, x))) )) # 
    updateR (t,x))" in exI)
  apply (simp)
  apply (rule cspF_decompo)
  apply (simp)
  apply (rule cspF_decompo)
  apply (simp)+
  apply (cspF_unwind)
  apply (cspF_hsf)+
done

(* -------------------------- LineSpec_Step -------------------------- *)

lemma LineSpec_Step:
 "$LineSpec s <=F LineSpec_to_Step (LineSpec s)"
apply (rule cspF_fp_induct_left[of _ "LineSpec_to_Step"])
apply (auto)
 apply (induct_tac p)
 apply (cspF_unwind | cspF_hsf)+
 (* main *)
 apply (case_tac "~ ChkLCR x")
 apply (simp)
 apply (cspF_simp)+

 apply (case_tac "tl x ~= []")
  apply (cspF_simp)+
  apply (rule cspF_Rep_int_choice_right)
  apply (simp)
  apply (simp)
  apply (rotate_tac -1)
  apply (drule sym)
  apply (simp)
  apply (simp add: tl_toStbOne_not_nil)
  apply (elim exE)
  apply (simp)

  apply (insert Att_or)
  apply (frule_tac x="a1" in spec)
  apply (drule_tac x="a2" in spec)
  apply (elim disjE conjE exE)
  apply (simp_all)

   apply (simp add: LineSpec_Step_ref1_AttL_AttL)
   apply (simp add: LineSpec_Step_ref1_AttL_AttC)
   apply (simp add: LineSpec_Step_ref1_AttL_AttR)
   apply (simp add: LineSpec_Step_ref1_AttC_AttL)
   apply (simp add: LineSpec_Step_ref1_AttR_AttL)
   apply (simp add: LineSpec_Step_ref1_AttC_AttC)
   apply (simp add: LineSpec_Step_ref1_AttC_AttR)
   apply (simp add: LineSpec_Step_ref1_AttR_AttC)
   apply (simp add: LineSpec_Step_ref1_AttR_AttR)

 (* tl list = [] *)
 apply (simp add: tl_nil)
 apply (elim disjE conjE exE)
 apply (simp)
 apply (cspF_simp)+
 apply (cspF_unwind | cspF_hsf)+
 apply (drule_tac x="a" in spec)
 apply (elim disjE conjE exE)
 apply (simp_all)

  apply (cspF_simp)+
  apply (rule cspF_prefix_ss_mono)
  apply (simp)
  apply (cspF_simp)+

  apply (rule cspF_decompo)
  apply (rule cspF_prefix_ss_mono)
  apply (simp)
  apply (cspF_simp)+
  apply (rule cspF_prefix_ss_mono)
  apply (simp_all)
  apply (cspF_simp)+

  apply (rule cspF_prefix_ss_mono)
  apply (simp_all)
  apply (cspF_simp)+
done

(*********************************************************
                          one
 *********************************************************)

primrec
  LineSpec_to_One :: "PN => (PN, Event) proc"
where
  "LineSpec_to_One (Child n)    = $(Child n)"
 |"LineSpec_to_One (ChildL n)   = $(ChildL n)"
 |"LineSpec_to_One (ChildR n)   = $(ChildR n)"

 |"LineSpec_to_One (LineSpec s) = 
    (IF (EX a. s=[a]) THEN ChildAtt (hd s) ELSE $LineSpec s)"

(* ---------- LineSpec [a] <=F ChildAtt a ---------- *)

lemma LineSpec_One:
 "$LineSpec [a] <=F ChildAtt a"
apply (rule cspF_fp_induct_left[of _ "LineSpec_to_One"])
apply (auto)
 apply (cspF_simp)+

 apply (induct_tac p)
 apply (cspF_unwind | cspF_hsf)+

 (* main *)
 apply (case_tac "EX a. x = [a]")
 apply (elim conjE exE)
 apply (simp)
 apply (insert Att_or)
 apply (drule_tac x="a" in spec)
 apply (elim disjE conjE exE)
 apply (simp_all)
 apply (cspF_unwind | cspF_hsf)+

 apply (rule cspF_decompo)
 apply (simp)
 apply (cspF_simp)+

 apply (cspF_unwind)+
 apply (rule cspF_decompo)
 apply (rule cspF_prefix_ss_mono)
 apply (simp_all)
 apply (cspF_simp)+
 apply (rule cspF_prefix_ss_mono)
 apply (simp_all)
 apply (cspF_simp)+

 apply (cspF_unwind)+
 apply (rule cspF_prefix_ss_mono)
 apply (simp_all)
 apply (cspF_simp)+

 (* ~ (EX a. list = [a]) *)
 apply (cspF_unwind)+
 apply (case_tac "~ ChkLCR x")
 apply (cspF_simp)+

 apply (rule cspF_decompo)
 apply (case_tac "~ guardL x")
 apply (cspF_simp)+
 apply (rule cspF_prefix_ss_mono)
 apply (simp_all)
 apply (subgoal_tac "~(EX a. nextL x = [a])")
 apply (simp (no_asm_simp))
 apply (cspF_simp)+
 apply (erule contrapos_pp)
 apply (simp)
 apply (elim conjE exE)
 apply (rule nextL_one_EX)
 apply (simp_all)

 apply (case_tac "~ guardR x")
 apply (cspF_simp)+
 apply (rule cspF_prefix_ss_mono)
 apply (simp_all)
 apply (subgoal_tac "~(EX a. nextR (x,xa) = [a])")
 apply (simp (no_asm_simp))
 apply (cspF_simp)+
 apply (erule contrapos_pp)
 apply (simp)
 apply (elim conjE exE)
 apply (rule nextR_one_EX)
 apply (simp_all)
done


declare ChkLCR.simps [simp del]

lemma LineSpec_LineChild_toStbOne_lm:
 "ALL s. (length s = n & ChkLCR s & s~=[]) -->
  ($LineSpec s <=F !<stlist> t:{t. toStbOne t = s} .. LineChildAtt t)"
apply (induct_tac n)

(* 0 *)
apply (simp add: lengtht_zero)
(*
apply (intro allI impI)
apply (simp add: ChkLCR.simps)
apply (cspF_hsf_unwind)+
apply (simp add: ChkLCR.simps)
apply (cspF_hsf_unwind)+
*)

(* Suc *)
apply (intro allI impI)
apply (case_tac "s=[]")

 (* s=[] *)
 apply (simp)

 (* s~=[] *)
 apply (rule cspF_tr_left)
 apply (rule LineSpec_Step)
 apply (simp)
 apply (cspF_simp)+
 apply (rule cspF_Rep_int_choice_right)
 apply (simp)
 apply (simp)

 (* (tl s = []) *)
 apply (case_tac "tl s = []")
 apply (simp)
 apply (cspF_simp)+
 apply (simp add: tl_nil)
 apply (elim exE conjE)
 apply (simp)
 apply (rule LineSpec_One)

 (* (tl s ~= []) *)
 apply (cspF_simp)+
 apply (simp add: tl_not_nil)
 apply (elim exE conjE)
 apply (simp)

 apply (rule cspF_Rep_int_choice_left)
 apply (simp)
 apply (rule_tac x="a" in exI)
 apply (simp)

 apply (case_tac "a=[]", simp)
 apply (simp add: not_nil)
 apply (elim exE conjE)
 apply (simp)

 apply (case_tac "ta=[]", simp)
 apply (simp add: not_nil)
 apply (elim exE conjE)
 apply (simp)

 apply (rule cspF_decompo | simp)+

 apply (drule_tac x="ab#tb" in spec)
 apply (simp)
 apply (subgoal_tac "Suc (length tb) = n & ChkLCR (ab # tb)")
 apply (simp)

 apply (rule cspF_tr_left)
 apply (simp)

 apply (rule cspF_Rep_int_choice_left)
 apply (simp)
 apply (rule_tac x="ab#tb" in exI)
 apply (simp)
 apply (simp add: ChkLCR_toStbOne_id)

 apply (drule sym)
 apply (simp)
 apply (simp add: ChkLCR_toStbOne_iff)
apply (subgoal_tac "length(toStbOne (aa # ab # tb)) = (Suc n)")
 apply (simp add: toStbOne_length)
 apply (rotate_tac -1)
 apply (drule sym)
 apply (simp)
done

declare ChkLCR.simps [simp]

lemma LineSpec_LineChild_toStbOne:
 "[| ChkLCR s ; s ~= [] |] ==>
  $LineSpec s <=F !<stlist> t:{t. toStbOne t = s} .. LineChildAtt t"
apply (insert LineSpec_LineChild_toStbOne_lm[of "length s"])
apply (simp)
done

lemma LineSpec_LineChild_toStb_lm:
 "ALL t. (length t = n & t ~= []) --> $LineSpec (toStb t) <=F LineChildAtt t"
apply (induct_tac n)

(* 0 *)
apply (simp add: lengtht_zero)
(* 
apply (cspF_hsf_unwind)+
*)

(* Suc *)
apply (intro allI impI)
apply (case_tac "t=[]", simp)
apply (simp add: not_nil)
apply (elim exE conjE)
apply (simp)

apply (case_tac "ta=[]", simp)
apply (rule LineSpec_One)

 (* s~=[] *)
 apply (rule cspF_tr_left)
 apply (rule LineSpec_Step)
 apply (simp)
 apply (simp add: ChkLCR_toStbOne_iff)
 apply (simp add: ChkLCR_toStb)
 apply (subgoal_tac "tl (toStbOne (a # toStb ta)) ~= []")
 apply (cspF_simp)+
 apply (rule cspF_Rep_int_choice_left)
 apply (simp)
 apply (rule_tac x="a # toStb ta" in exI)
 apply (simp add: not_nil_EX)

 apply (rotate_tac -1)
 apply (erule contrapos_nn)
 apply (simp add: tl_nil)
done

(* --------------------------------- *
          LineSpec (main)
 * --------------------------------- *)

lemma LineSpec_LineChildAtt:
 "t ~= [] ==> $LineSpec (toStb t) <=F LineChildAtt t"
apply (simp add: LineSpec_LineChild_toStb_lm)
done

lemma LineChild_LineChildAtt:
 "s ~= [] --> LineChild s = LineChildAtt (map AttC s)"
apply (induct_tac s)
apply (simp)
apply (simp)
apply (case_tac "list=[]", simp)
apply (simp)
done

lemma LineSpec_LineChild:
 "t ~= [] ==> $LineSpec (toStb (map AttC t)) <=F LineChild t"
apply (simp add: LineChild_LineChildAtt)
apply (simp add: LineSpec_LineChildAtt)
done

end
