           (*-------------------------------------------*
            |                N Buffers                  |
            |                                           |
            |                June 2009                  |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory NBuff
imports CSP_F
begin

(*=============================================================*
 |                                                             |
 |                           Process                           |
 |                                                             |
 *=============================================================*)

(*********************************************************
               process names and events
 *********************************************************)

datatype Event = inC | outC | midC
datatype PN = Buff1 | Buff1' | Buff "nat" "nat"

(*********************************************************
                  Recursivey Process
 *********************************************************)

primrec	
  PNdef :: "PN => (PN, Event) proc"
where
 "PNdef  (Buff1) = inC -> $Buff1'"
|"PNdef (Buff1') = outC -> $Buff1"

|"PNdef  (Buff N k) = 
    (IF (0 < N & k <= N)
     THEN ((IF (k < N) 
            THEN (inC -> $Buff N (Suc k)) ELSE STOP) [+]
           (IF (0 < k)
            THEN (outC -> $Buff N (k - 1)) ELSE STOP))
     ELSE STOP)"

(*     
defs (overloaded) Set_PNfun_def [simp]: "PNfun == PNdef"
*)

overloading Set_PNdef == 
  "PNfun :: (PN, Event) pnfun"
begin
  definition "PNfun == PNdef"
end
declare Set_PNdef_def [simp]

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

abbreviation
 Link :: "(PN, Event) proc => (PN, Event) proc => (PN, Event) proc"
        ("(1_ /<---> _)" [76,77] 76)
where "P <---> Q == (P[[outC<-->midC]] |[{midC}]| 
                     Q[[inC<-->midC]]) -- {midC}"

primrec
 LinkBuff :: "nat => nat => (PN, Event) proc"
where
 "LinkBuff      0  = (%k. STOP)"
|"LinkBuff (Suc n) = (%k.
    IF (n=0)
    THEN IF (0 < k) 
         THEN $Buff1'
         ELSE $Buff1
    ELSE IF (n < k) 
         THEN ($Buff1' <---> LinkBuff n (k - 1))
         ELSE ($Buff1 <---> LinkBuff n k))"

(*********************************************************
                  for automatising
 *********************************************************)

declare simp_event_set [simp]

lemma Link_cong: "Q =F R ==> P <---> Q =F P <---> R"
by (simp)

(*********************************************************
                  data tranfer
 *********************************************************)

lemma internal_data_transfer[rule_format]:
      "k < N -->
       ($Buff1' <---> $Buff N k) =F 
       ($Buff1 <---> $Buff N (Suc k))"
apply (induct_tac k)

(* base case k=0 *)
apply (intro impI)
apply (cspF_unwind_left)
apply (cspF_hsf_left)+

(* induction case *)
apply (intro impI)

apply (cspF_auto)+
apply (rule cspF_Int_choice_eq_left)
apply (simp_all)
apply (subgoal_tac
  "(? b:{midC} -> $Buff1 [[outC<-->midC]] |[{midC}]| $Buff N n [[inC<-->midC]]) -- {midC} =F
   $Buff1' <---> $Buff N n")

defer

 apply (erule cspF_symE)
 apply (cspF_unwind_right)+
 apply (cspF_ren_deep_right)+
 apply (rule cspF_decompo)
 apply (simp_all)
 apply (rule cspF_decompo)
 apply (simp_all)
 apply (cspF_unwind_left)+
 apply (cspF_ren_deep)+

 apply (case_tac "(Suc (Suc n)) < N")
 apply (cspF_hsf)+
 apply (auto)
 apply (cspF_simp)+
 apply (rule cspF_Int_choice_eq_left)
 apply (cspF_unwind)
 apply (cspF_ren)
 apply (cspF_simp_deep)+

 apply (cspF_auto)+
 apply (auto)
 apply (cspF_simp)+
 apply (rule cspF_Int_choice_eq_left)
 apply (simp_all)
 apply (rule cspF_decompo)
 apply (simp_all)
 apply (rule cspF_decompo)
 apply (simp_all)
 apply (cspF_unwind_left)+
 apply (cspF_ren_deep)+
done

(*********************************************************
                 one step concurrency
 *********************************************************)

primrec
  Buff_to_Link_Buff :: "PN => (PN, Event) proc"
where
  "Buff_to_Link_Buff (Buff1)   = $Buff1"
 |"Buff_to_Link_Buff (Buff1')  = $Buff1'"
 |"Buff_to_Link_Buff (Buff N k) = 
     (IF (0 < N & k <= N) 
      THEN IF (N=Suc 0) 
           THEN IF (k<N) THEN $Buff1
                         ELSE $Buff1'
           ELSE IF (k<N) THEN ($Buff1 <---> $Buff (N - 1) k)
                         ELSE ($Buff1' <---> $Buff (N - 1) (k - 1))
      ELSE STOP)"

theorem LinkBuff_eq_Buff_step_k:
   "[| 0 < N ; k <= (Suc N) |] ==> 
       $Buff N k =F Buff_to_Link_Buff (Buff N k)"
apply (rule cspF_fp_induct_left[of _ "Buff_to_Link_Buff"])
apply (simp)+
apply (induct_tac p)
apply (auto)
apply (cspF_unwind)+

apply (case_tac "~(0 < x1 & x2 <= x1)")
apply (auto)
apply (cspF_simp)+

apply (subgoal_tac "(x2 - Suc 0 < x1)")
apply (cspF_simp_deep)+

apply (erule rem_asmE)
apply (erule rem_asmE)
apply (rename_tac N k)

(* N=0 *)
apply (case_tac "N=0")
apply (simp)

(* N=Suc 0 *)
apply (case_tac "N= Suc 0")
 apply (cspF_simp)
 apply (case_tac "k=0")
  apply (cspF_simp_deep)+
  apply (cspF_hsf)+

(* N=Suc (Suc 0) *)
apply (case_tac "N = Suc (Suc 0)")
 apply (cspF_simp)
 apply (case_tac "k=0")
  apply (cspF_simp_deep)+
  apply (cspF_unwind | cspF_hsf)+

(* k < N *)
apply (case_tac "k < N")
 apply (cspF_simp)
 apply (case_tac "k=0")
  apply (cspF_simp_deep)+
  apply (cspF_unwind | cspF_hsf)+
  apply (auto)
  apply (cspF_simp_deep)+
  apply (cspF_unwind | cspF_hsf)+

 (* k < N - Suc 0 *)
  apply (case_tac "k < N - Suc 0")
  apply (cspF_simp_deep)+
  apply (cspF_hsf)+
  apply (auto)
  apply (cspF_simp_deep)+
 (* ok *)
  defer

  apply (cspF_simp_deep)+
  apply (case_tac "Suc k < N")
   apply (cspF_simp_deep)+
   (* by transfer *)
   defer

 (* ~ (k < N - Suc 0) *)
 (* i.e. k = N - Suc 0 *)
apply (subgoal_tac "k = N - Suc 0")
 apply (simp)
 apply (cspF_simp_deep)+
  apply (cspF_hsf)+
  apply (auto)
   apply (cspF_simp_deep)+
  (* ok *)
  defer

   apply (cspF_simp_deep)+
  (* ok *)
  defer

apply (cspF_simp_deep)+
apply (cspF_unwind | cspF_hsf)+
 apply (auto)
 apply (cspF_simp_deep)+
   (* by transfer *)
   defer

(* by decompo *)
  apply (rule cspF_decompo, auto)+
  defer

(* by transfer lemma *)
apply (rule cspF_rw_left)
apply (rule internal_data_transfer[THEN cspF_symE])
apply (subgoal_tac "k < (N - Suc 0)")
apply (rotate_tac -1)
apply (assumption)
apply (simp)
apply (assumption)
  apply (rule cspF_decompo, auto)+
  defer

(* by decompo *)
  apply (rule cspF_decompo, auto)+
  defer

(* by decompo *)
  apply (rule cspF_decompo, auto)+
  defer

(* by transfer lemma *)
apply (rule cspF_rw_left)
apply (rule internal_data_transfer[THEN cspF_symE])
apply (subgoal_tac "(N - (Suc (Suc 0))) < N - (Suc 0)")
apply (rotate_tac -1)
apply (assumption)
apply (simp)
apply (subgoal_tac "Suc (N - Suc (Suc 0)) = N - Suc 0")
apply (simp)
apply (simp)
  apply (rule cspF_decompo, auto)+
  defer

(* easy *)

  apply (cspF_auto)+
done

(* --------------------- *
 |        one step       |
 * --------------------- *)

theorem LinkBuff_eq_Buff_step:
   "$Buff (Suc N) 0 =F 
     IF (N=0) THEN ($Buff1)
     ELSE ($Buff1 <---> $Buff N 0)"
apply (cspF_simp LinkBuff_eq_Buff_step_k)+
done

(* --------------------- *
 |          main         |
 * --------------------- *)

theorem LinkBuff_eq_Buff:
   "ALL N. $Buff N 0 =F LinkBuff N 0"
apply (rule allI)
(* by induction on N *)
apply (induct_tac N)
(* N=0 *)
apply (cspF_unwind)
(* N+1 *)
apply (case_tac "n=0")
apply (cspF_simp LinkBuff_eq_Buff_step)+
done

end
