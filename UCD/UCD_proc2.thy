           (*-------------------------------------------*
            |       Uniform Candy Distribution          |
            |                                           |
            |           November 2007 for Isabelle 2005 |
            |           November 2008 for Isabelle 2008 |
            |           November 2012 for Isabelle 2012 |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory UCD_proc2
imports UCD_proc1
begin

(*****************************************************************

         1. 

 *****************************************************************)

(* ======================= Circ ======================= *)

datatype PNRC = PreCircSpecC "(nat * (Att list))"
              | PreCircSpecL "(nat * (Att list))" 
              | PreCircSpecR "(nat * (Att list))"

fun
  PNRCdef :: "PNRC => (PNRC, Event) proc"
where
 "PNRCdef (PreCircSpecC (n,s)) = 
   IF (ChkLCR s & s~=[] & guardL s & guardR s) THEN
   ((left ! (n div 2) -> $PreCircSpecR(n div 2,s)) [+]
    (right ! (getNat (hd s) div 2) -> $PreCircSpecL(n,s)))
   ELSE STOP"

|"PNRCdef (PreCircSpecL (n,s)) = 
   IF (ChkLCR s & s~=[] & guardL s & guardR s) THEN
   (left ! (n div 2) ->
      $PreCircSpecC (fill(n div 2 + getNat (hd s) div 2),nextR(nextL s, (n div 2))))
   ELSE STOP"

|"PNRCdef (PreCircSpecR (n,s)) = 
   IF (ChkLCR s & s~=[] & guardL s & guardR s) THEN
   (right ! (getNat (hd s) div 2) ->
      $PreCircSpecC (fill(n + (getNat (hd s) div 2)),nextL(nextR(s,n))))
   ELSE STOP"
(*
defs (overloaded) Set_PNRCfun_def [simp]: "PNfun == PNRCdef"
*)
overloading Set_PNRCdef == 
  "PNfun :: (PNRC, Event) pnfun"
begin
  definition "PNfun == PNRCdef"
end
  
declare Set_PNRCdef_def [simp]

(* ------------------ *
      guardedness
 * ------------------ *)

lemma guardedfun_PNRC[simp]:
      "guardedfun PNRCdef"
apply (simp add: guardedfun_def)
apply (rule allI)
apply (induct_tac p)
apply (auto)
done


(* -----------------------DF---------------------------------- *)

datatype DFtickName = DFtick

primrec
  DFtickfun ::
    "DFtickName => (DFtickName, 'a) proc"
where
  "DFtickfun (DFtick) = (! x ->  $(DFtick)) |~| SKIP "

(*
defs (overloaded)
Set_DFtickfun_def [simp]: "PNfun == DFtickfun"
*)

overloading Set_DFtickfun == 
  "PNfun :: (DFtickName, Event) pnfun"
begin
  definition "(PNfun :: (DFtickName, Event) pnfun) == DFtickfun"
end
  
declare Set_DFtickfun_def [simp]


lemma guardedfun_DFtick[simp]:
      "guardedfun DFtickfun"
by (simp add: guardedfun_def, rule allI, induct_tac p, simp_all)


primrec
  DF_to_PreCircSpecC :: "DFtickName => (PNRC, Event) proc"
where
  "DF_to_PreCircSpecC (DFtick) = 
     (!nat n .. !<stlist> s:{s. ChkLCR s & s~=[] & guardL s & guardR s} .. 
           $PreCircSpecC (n,s))
     |~|
     (!nat n .. !<stlist> s:{s. ChkLCR s & s~=[] & guardL s & guardR s} .. 
           $(PreCircSpecL (n,s)))
     |~|
     (!nat n .. !<stlist> s:{s. ChkLCR s & s~=[] & guardL s & guardR s} .. 
           $PreCircSpecR (n,s))"

(* --------------------------------------- *
            deadlock freeness
 * --------------------------------------- *)

theorem PreCircSpecC_DF: 
  "[| ChkLCR s ; s~=[] ; guardL s ; guardR s |]
   ==> (($DFtick)::(DFtickName, Event) proc) <=F $PreCircSpecC (n,s)"
apply (rule cspF_fp_induct_left[of _ "DF_to_PreCircSpecC"])
apply (auto)

(* base *)
 apply (rule cspF_Int_choice_left1)
 apply (rule cspF_Int_choice_left1)
 apply (rule cspF_Rep_int_choice_left)
 apply (rule_tac x="n" in exI)
 apply (simp)
 apply (rule cspF_Rep_int_choice_left)
 apply (simp)
 apply (rule_tac x="s" in exI)
 apply (simp)

(* step *)
 apply (induct_tac p, auto)

 (* 1 *)
 apply (rule cspF_Int_choice_left1)
 apply (simp add: Int_pre_choice_def)
 apply (cspF_unwind_right | cspF_hsf_right)+
 apply (rule cspF_decompo_ref)
 apply (simp_all)
  apply (elim disjE conjE exE)  (* right | left *)
  (* 1/2 *)(* right *)
  apply (simp)
  apply (cspF_simp)+
  apply (rule cspF_Int_choice_left1)
  apply (rule cspF_Int_choice_left2)
  apply (rule cspF_Rep_int_choice_left)
  apply (rule_tac x="n" in exI)
  apply (simp)
  apply (rule cspF_Rep_int_choice_left)
  apply (simp)
  apply (rule_tac x="a" in exI)
  apply (simp)

   (* 1/2 *)(* left *)
  apply (cspF_simp)+
  apply (rule cspF_Int_choice_left2)
  apply (rule cspF_Rep_int_choice_left)
  apply (rule_tac x="n div 2" in exI)
  apply (simp)
  apply (rule cspF_Rep_int_choice_left)
  apply (simp)
  apply (rule_tac x="a" in exI)
  apply (simp)

 (* 2 *)
 apply (rule cspF_Int_choice_left1)
 apply (simp add: Int_pre_choice_def)
 apply (cspF_unwind_right | cspF_hsf_right)+
 apply (rule cspF_decompo_ref)
 apply (simp_all)
  (* left *)
  apply (rule cspF_Int_choice_left1)
  apply (rule cspF_Int_choice_left1)
  apply (rule cspF_Rep_int_choice_left)
  apply (rule_tac x="fill (n div 2 + getNat (hd a) div 2)" in exI)
  apply (simp)
  apply (rule cspF_Rep_int_choice_left)
  apply (simp)
  apply (rule_tac x="nextR (nextL a, n div 2)" in exI)
  apply (simp)
  apply (simp add: guardR_nextR_nextL)

 (* 3 *)
 apply (rule cspF_Int_choice_left1)
 apply (simp add: Int_pre_choice_def)
 apply (cspF_unwind_right | cspF_hsf_right)+
 apply (rule cspF_decompo_ref)
 apply (simp_all)
  (* right *)
  apply (rule cspF_Int_choice_left1)
  apply (rule cspF_Int_choice_left1)
  apply (rule cspF_Rep_int_choice_left)
  apply (rule_tac x="fill (n + getNat (hd a) div 2)" in exI)
  apply (simp)
  apply (rule cspF_Rep_int_choice_left)
  apply (simp)
  apply (rule_tac x="nextL (nextR (a, n))" in exI)
  apply (simp)
  apply (simp add: guardL_nextL_nextR)
done


(* ------------------------------------------------------------ *)

fun
  PreCircSpecC_to_Step :: "PNRC => (PN, Event) proc"
where
  "PreCircSpecC_to_Step (PreCircSpecC (n,s)) = 
     IF (ChkLCR s & s~=[] & guardL s & guardR s) 
     THEN ($Child n <=-=> $LineSpec s) ELSE STOP"

 |"PreCircSpecC_to_Step (PreCircSpecL (n,s)) = 
     IF (ChkLCR s & s~=[] & guardL s & guardR s)
     THEN ($ChildL (n, getNat (hd s) div 2) <=-=> $LineSpec (nextL s)) ELSE STOP"

 |"PreCircSpecC_to_Step (PreCircSpecR (n,s)) = 
     IF (ChkLCR s & s~=[] & guardL s & guardR s)
     THEN ($ChildR n <=-=> $LineSpec (nextR (s, n))) ELSE STOP"

(* ----------------------------------- *
                 Circ
 * ----------------------------------- *)

lemma PreCircSpecC_Step_lm:
 "$PreCircSpecC (n,s) <=F PreCircSpecC_to_Step (PreCircSpecC (n,s))"
apply (rule cspF_fp_induct_left[of _ "PreCircSpecC_to_Step"])
apply (simp)+

 apply (induct_tac p)
 apply (auto)

(* PreCircSpecC *)
 apply (case_tac "~(ChkLCR b & b ~= [] & guardL b & guardR b)")
 apply (simp (no_asm_simp))
 apply (cspF_simp)+

 (* ChkLCR b & b ~= [] *)
  apply (simp add: not_nil_EX)
  apply (elim exE conjE)
  apply (simp)
  apply (elim conjE disjE exE)
  apply (simp_all)

  (* AttL *)
  apply (cspF_unwind | cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    apply (elim disjE conjE exE)  (* left | right *)
   (* 1/2 *)(* left *)
    apply (simp)
    apply (cspF_simp)+
   (* 1/2 *)(* right  done *)


  (* AttC *)
  apply (cspF_unwind | cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    apply (elim disjE conjE exE)  (* left | right *)
   (* 1/2 *)(* left *)
    apply (simp)
    apply (cspF_simp)+

(* PreCircSpecL *)
 apply (case_tac "~(ChkLCR b & b ~= [] & guardL b & guardR b)")
 apply (simp (no_asm_simp))
 apply (cspF_simp)+

 (* ChkLCR b & b ~= [] *)
  apply (simp add: not_nil_EX)
  apply (elim exE conjE)
  apply (simp)
  apply (elim conjE disjE exE)
  apply (simp_all)

  (* AttL *)
  apply (cspF_unwind | cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    (* left *)
    apply (cspF_simp)+
    apply (simp add: guardR_nextR_nextL)
    apply (cspF_simp)+

  (* AttC *)
  apply (cspF_unwind | cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
   (* left *)
    apply (cspF_simp)+
    apply (simp add: ChkR_ChkCR guardR_nextR_AttR)
    apply (cspF_simp)+

(* PreCircSpecR *)
 apply (case_tac "~(ChkLCR b & b ~= [] & guardL b & guardR b)")
 apply (simp (no_asm_simp))
 apply (cspF_simp)+

 (* ChkLCR b & b ~= [] *)
  apply (simp add: not_nil_EX)
  apply (elim exE conjE)
  apply (simp)
  apply (elim conjE disjE exE)
  apply (simp_all)

  (* AttL *)
  apply (cspF_unwind | cspF_hsf)+
  apply (case_tac "guardR (nextR (t, a))")
  apply (cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    (* right *)
    apply (cspF_simp)+

  (* ~guardR (nextR (t, a) *)
  apply (cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    (* right *)
    apply (cspF_simp)+

  (* AttC *)
  apply (cspF_unwind | cspF_hsf)+
  apply (case_tac "guardR (nextR (AttC n # t, a))")
  apply (cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp add: getNat_hd_nextR_AttC)
   apply (simp add: guardL_nextL_nextR)
   apply (cspF_simp)+
   apply (simp add: getNat_hd_nextR_AttC)

  apply (cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp add: getNat_hd_nextR_AttC)
   apply (simp add: guardL_nextL_nextR)
   apply (cspF_simp)+
   apply (simp add: getNat_hd_nextR_AttC)
done

(* --------------------------------- *
          PreCircSpecC (step main)
 * --------------------------------- *)

lemma cspF_tr_left_ref2:
   "[| P1 <=F[M1,M2] P2 ; P2 <=F[M2,M3] P3 |] ==> P1 <=F[M1,M3] P3"
by (simp add: refF_def eqF_def)

lemma PreCircSpecC_Step:
 "[| ChkLCR s ; s ~= [] ; guardL s ; guardR s |]
  ==> ($PreCircSpecC (n, s)::(PNRC,Event) proc) <=F $Child n <=-=> $LineSpec s"
apply (rule cspF_tr_left_ref2)
apply (rule PreCircSpecC_Step_lm)
apply (simp)
apply (cspF_simp)+
done

(* --------------------------------- *
               lemmas
 * --------------------------------- *)

(*
lemma PreCircChild_not_nil [simp]: 
  "s ~= [] ==> PreCircChild (n # s) = ($Child n) <=-=> (LineChild s)"
apply (simp add: not_nil_EX)
apply (elim conjE exE)
by (simp)

lemma CircChild_not_nil [simp]: 
  "s ~= [] ==> CircChild (n # s) = ($Child n) <===> (LineChild s)"
apply (simp add: not_nil_EX)
apply (elim conjE exE)
by (simp)
*)

(* ---------------------------------------------------- *
 |                                                      |
 |           Sequentialising PreCircChild s             |
 |                                                      |
 * ---------------------------------------------------- *)

theorem PreCircSpecC_PreCircChild:
 "s~=[] ==> $PreCircSpecC (n, toStb (map AttC s)) <=F PreCircChild (n#s)"
apply (rule cspF_tr_left_ref2)
apply (rule PreCircSpecC_Step)
apply (simp_all)
apply (simp add: ChkLCR_toStb)
apply (simp add: guardL_toStb_AttC)
apply (simp add: guardR_toStb_AttC)
apply (rule cspF_decompo | simp)+
apply (simp add: LineSpec_LineChild)
done

(* --------------------------------- *
 |       DF <= PreCircSpecC          |
 * --------------------------------- *)

lemma DF_PreCircSpecC_toStb:
 "s~=[] ==> (($DFtick)::(DFtickName, Event) proc) 
            <=F $PreCircSpecC (n, toStb (map AttC s))"
apply (rule PreCircSpecC_DF)
apply (simp add: ChkLCR_toStb)
apply (simp)
apply (simp add: guardL_toStb_AttC)
apply (simp add: guardR_toStb_AttC)
done

(* ---------------------------------------------------- *
 |                                                      |
 |          PreCircChild s is dealock-free.             |
 |                                                      |
 * ---------------------------------------------------- *)

theorem DF_PreCircChild:
 "s~=[] ==> $DFtick <=F PreCircChild (n#s)"
apply (rule cspF_tr_left_ref2)
apply (rule DF_PreCircSpecC_toStb)
apply (simp)
apply (rule PreCircSpecC_PreCircChild)
apply (simp)
done

(* ======================= CircSpec ======================= *)

datatype PNR = CircSpec "(nat list)"

primrec
  PNRdef :: "PNR => (PNR, Event) proc"
where
 "PNRdef (CircSpec s) = 
    IF (tl s~=[]) THEN 
    (left ! ((hd s) div 2) -> $(CircSpec (circNext s)))
    ELSE STOP"
(*
defs (overloaded) Set_PNRfun_def [simp]: "PNfun == PNRdef"
*)
overloading Set_PNRdef == 
  "PNfun :: (PNR, Event) pnfun"
begin
  definition "PNfun == PNRdef"
end
  
declare Set_PNRdef_def [simp]

(* ------------------ *
      guardedness
 * ------------------ *)

lemma guardedfun_PNR[simp]:
      "guardedfun PNRdef"
apply (simp add: guardedfun_def)
apply (rule allI)
apply (induct_tac p)
apply (auto)
done

(* ------------------------------------------------------------ *)

declare toStb_simp [simp]

fun
  CircSpec_to_PreCircSpecC :: "PNR => (PNRC, Event) proc"
where
  "CircSpec_to_PreCircSpecC (CircSpec s) = 
     IF (tl s~=[]) THEN
        ($PreCircSpecC (hd s, toStb (map AttC (tl s))) -- range right)
     ELSE STOP"

(* ------------- lemma ------------- *)

lemma CircSpec_PreCircSpecC_lm:
 "tl s ~= [] ==> $CircSpec s <=F CircSpec_to_PreCircSpecC (CircSpec s)"
apply (rule cspF_fp_induct_left[of _ "CircSpec_to_PreCircSpecC"])
apply (simp)+

 apply (induct_tac p)
 apply (auto)

 apply (case_tac "(tl xa = [])")
 apply (simp)
 apply (cspF_simp)+

 (* tl list ~= [] *)

  apply (cspF_unwind)
  apply (cspF_hsf)+

  apply (rule)  (* 1i |~| 2i *)

  (* 1i *)
   apply (cspF_unwind)
   apply (simp add: nextR_nextL_toStb_nextR_nextL_toStb)
   apply (cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    (* left *)
    apply (cspF_simp)+
    apply (rule)  (* 1ii |~| 2ii *)

     (* 1ii *)
     apply (cspF_unwind_right)
     apply (cspF_hsf)+
     apply (simp add: nextL_nextR_toStb_lineNext)
     apply (simp add: tl_lineNext)
     apply (simp add: getNat_hd_toStb_map_AttC)
     apply (simp add: hd_circNext)
     apply (simp add: circNext_def)

     (* 2ii *)
     apply (simp add: nextL_nextR_toStb_lineNext)
     apply (simp add: tl_lineNext)
     apply (simp add: getNat_hd_toStb_map_AttC)
     apply (simp add: hd_circNext)
     apply (simp add: circNext_def)

  (* 2i *)
   apply (cspF_unwind)
   apply (simp add: nextR_nextL_toStb_nextR_nextL_toStb)
   apply (cspF_hsf)+
   (* rem head *)
   apply (rule)
   apply (simp)
   apply (simp)
    (* left *)
    apply (cspF_simp)+

     apply (simp add: nextL_nextR_toStb_lineNext)
     apply (simp add: tl_lineNext)
     apply (simp add: getNat_hd_toStb_map_AttC)
     apply (simp add: hd_circNext)
     apply (simp add: circNext_def)
done

(* ---------------------------------------------------- *
 |                                                      |
 |     CircSpec s <=F PreCircSpecC s -- range right     |
 |                                                      |
 * ---------------------------------------------------- *)

lemma CircSpec_PreCircSpecC:
 "tl s ~= [] ==> $CircSpec s <=F $PreCircSpecC (hd s, toStb (map AttC (tl s))) -- range right"
apply (rule cspF_tr_left_ref2)
apply (rule CircSpec_PreCircSpecC_lm)
apply (simp)
apply (simp)
apply (cspF_simp)+
done

(* ---------------------------------------------------- *
 |                                                      |
 |               CircSpec s <=F CircChild s             |
 |                                                      |
 * ---------------------------------------------------- *)

theorem CircSpec_CircChild:
 "tl s ~= [] ==> $CircSpec s <=F CircChild s"
apply (insert list_nil_or_unnil)
apply (drule_tac x="s" in spec)
apply (elim disjE exE)
apply (simp)
apply (simp)
apply (rule cspF_tr_left_ref2)
apply (rule CircSpec_PreCircSpecC)
apply (simp)
apply (simp)

apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_tr_left_ref2)
apply (rule PreCircSpecC_PreCircChild)
apply (simp)
apply (simp)
done

(*********************************************************
               Eventually Stable spec
 *********************************************************)

datatype PNS = Stable "nat"

primrec
  PNSdef :: "PNS => (PNS, Event) proc"
where
 "PNSdef (Stable n) = left ! n -> $Stable n"
(*
defs (overloaded) Set_PNSfun_def [simp]: "PNfun == PNSdef"
*)

overloading Set_PNSdef == 
  "PNfun :: (PNS, Event) pnfun"
begin
  definition "PNfun == PNSdef"
end
  
declare Set_PNSdef_def [simp]

(* ------------------ *
      guardedness
 * ------------------ *)

lemma guardedfun_PNS[simp]:
      "guardedfun PNSdef"
by (simp add: guardedfun_def, rule allI, induct_tac p, auto)

primrec
  Unstable     :: "nat => (nat list) => (PNS, Event) proc"
where
  "Unstable      0  = (%s. SKIP)"
 |"Unstable (Suc n) = (%s. left ! (hd s div 2) -> Unstable n (circNext s))"

definition
  EventuallyStable :: "(nat list) => (PNS, Event) proc"
where
  EventuallyStable_def:
   "EventuallyStable s == (!nat N .. Unstable N s) ;; 
                          (!nat n .. $Stable n)"

(* ----------------------------------------------- *
          eventually stable specification
 * ----------------------------------------------- *)

primrec
  EventuallyStable_to_CircSpec :: "nat => PNS => (PNR, Event) proc"
where
  "EventuallyStable_to_CircSpec l (Stable n)   =  $CircSpec (makeStableList l (2 * n))"

(* ---------- lemmas ---------- *)

lemma Unstable_CircSpec_lm:
  "ALL s. (tl s ~= [] & P <=F $CircSpec (circNexts N s))
     --> Unstable N s ;; P <=F $CircSpec s"
apply (induct_tac N)
apply (auto | cspF_auto)+
done

lemma Unstable_CircSpec:
  "[| tl s ~= [] ; P <=F $CircSpec (circNexts N s) |]
   ==> Unstable N s ;; P <=F $CircSpec s"
by (simp add: Unstable_CircSpec_lm)


lemma Stable_CircSpec:
 "[| Suc 0 < l ; s=makeStableList l (2*n) |] ==> 
  $Stable n <=F (($CircSpec s)::(PNR, Event) proc)"
apply (rule cspF_fp_induct_left[of _ "EventuallyStable_to_CircSpec l"])
apply (simp)+

 apply (induct_tac p)
 apply (auto | cspF_auto)+
 apply (simp_all add: stable_circNext)
done

lemma EventuallyStable_CircSpec:
 "[| Suc 0 < length s ; allEven s |] ==> EventuallyStable s <=F $CircSpec s"
apply (subgoal_tac "s~=[] & tl s ~= []")
apply (simp add: EventuallyStable_def)
apply (cspF_hsf)+
apply (rule cspF_Rep_int_choice_left)
apply (insert circNexts_eventually_stable[of s], simp)
apply (erule exE)
apply (rule_tac x="N" in exI)
apply (rule Unstable_CircSpec)
apply (simp_all)

apply (rule cspF_Rep_int_choice_left)
apply (rule_tac x="hd (circNexts N s) div 2" in exI)
apply (simp)
apply (rule Stable_CircSpec[of "length s"])
apply (simp_all)
apply (simp add: makeStableList_hd_stableList)
apply (simp add: list_length_more_one)
done

(* -------------------------------------------- *

                  Finally ...

     for any number of children more than two 
     and any initial number of candies,

 * -------------------------------------------- *)

theorem EventuallyStable_CircChild:
 "[| 1 < length s ; allEven s |] 
  ==> EventuallyStable s <=F CircChild s"
apply (rule cspF_tr_left_ref2)
apply (rule EventuallyStable_CircSpec)
apply (simp_all)
apply (rule CircSpec_CircChild)
apply (simp add: list_length_more_one)
done

end
