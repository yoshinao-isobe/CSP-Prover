           (*-------------------------------------------*
            |                DFP package                |
            |                   June 2005               |
            |               December 2005  (modified)   |
            |                                           |
            |   DFP on CSP-Prover ver.3.0               |
            |              September 2006  (modified)   |
            |                  April 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory DFP_Network
imports DFP_subseteqEX
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  Union (B ` A) = (UN x:A. B x)                      *)
(*                  Inter (B ` A) = (INT x:A. B x)                     *)

(*
declare Union_image_eq [simp del]
declare Inter_image_eq [simp del]
*)
(* no simp rules in Isabelle 2017 
declare Sup_image_eq [simp del]
declare Inf_image_eq [simp del]
*)

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite (notick | t = []t)                 *)
(*                                                                     *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*****************************************************************

         1. 
         2. 
         3. 
         4. 

 *****************************************************************)

(*********************************************************
                    definitions
 *********************************************************)

(*** network ***)

type_synonym ('i,'p,'a) Network  = "('i set * ('i => (('p,'a) proc * 'a set)))"

definition
  PAR  :: "('i,'p,'a) Network => ('p,'a) proc" ("(1PAR _)" [77] 77)
  where
  PAR_def :
    "PAR V == [||]i:(fst V) .. ((snd V) i)"

syntax
  "@Network" :: 
     "(('p,'a) proc * 'a set) => pttrn => 'i set
      => ('i,'p,'a) Network"  ("(1{ _ | /_:_ }net)" [77,900,90] 900)

translations
  "{ PX | i:I }net"  == "(I, (%i. PX))"


(*** failure set of network ***)

type_synonym ('i,'a) NetworkF = "('i set * ('i => (('a failure set) * 'a set)))"

syntax
  "@NetworkF" :: 
     "(('a failure set) * 'a set) => pttrn => 'i set
                      => ('i,'a) NetworkF"  ("(1{ _ | /_:_ }Fnet)" [77,900,90] 900)

translations
  "{ FX | i:I }Fnet"  == "(I, (%i. FX))"

(*** Network and NetworkF ***)

abbreviation
  Network_pro :: 
     "('i set * ('i => ('b * 'a set))) => 'i => 'b"
                          ("netElement _<_>" [900,0] 1000)
where
  "netElement V<i> == fst ((snd V) i)"

abbreviation
  Network_alp :: 
     "('i set * ('i => ('b * 'a set))) => 'i => 'a set"
                          ("netAlpha _<_>" [900,0] 1000)
where
  "netAlpha V<i>  == snd ((snd V) i)"

definition
  isFailureOf ::
   "('i,'a) NetworkF => ('i,'p,'a) Network => bool"
                                           ("(1_ /isFailureOf /_)" [55,55] 55)

  where
  isFailureOf_def : 
   "VF isFailureOf V == 
        fst V = fst VF &
       (ALL i : fst VF.
                fst (snd VF i) <=EX failures (fst (snd V i)) MF
                                    restRefusal (Ev ` snd (snd VF i)) &
                snd (snd V i) = snd (snd VF i))"

(*** short notations ***)

definition
  ALP  :: "('i set * ('i => ('b * 'a set))) => 'a set"
  where
  ALP_def  : "ALP V == {a. EX i:(fst V). a : snd((snd V) i)}"

(*** state ***)

type_synonym ('i,'a) net_state = "('a trace * ('i => 'a event set))"

definition
  isStateOf ::
   "('i,'a) net_state => ('i,'a) NetworkF => bool"
                                           ("(1_ /isStateOf /_)" [55,55] 55)
  where
  isStateOf_def : 
   "sigma isStateOf VF == 
     sett(fst sigma) <= Ev ` (ALP VF) &
    (ALL i: fst VF. (fst sigma rest-tr snd ((snd VF) i), (snd sigma) i) 
                     : fst ((snd VF) i) &
                    (snd sigma) i <= Ev ` snd ((snd VF) i))"

(*********************************************************
                    small lemmas
 *********************************************************)

lemma decompo_V:
  "EX I PXf. (V::('i,'p,'a) Network) = (I,PXf)"
apply (rule_tac x="fst V" in exI)
apply (rule_tac x="snd V" in exI)
by (simp)

lemma isFailureOf_subset_index:
   "[| (I, FXf) isFailureOf (I, PXf) ; J <= I |]
    ==> (J, FXf) isFailureOf (J, PXf)"
apply (simp add: isFailureOf_def)
by (auto)

lemma isFailureOf_subset_alpha1:
   "[| (I, FXf) isFailureOf (I, PXf) ; i : I ; (s, Y) : fst (FXf i) ; e : Y |]
    ==> e : Ev ` snd (PXf i)"
apply (simp add: isFailureOf_def)
apply (drule_tac x="i" in bspec, simp)
apply (simp add: subseteqEX_def restRefusal_def)
apply (auto)
done

lemma isFailureOf_subset_alpha2:
   "[| (I, FXf) isFailureOf (I, PXf) ; i : I ; (s, Y) : fst (FXf i) ; e : Y |]
    ==> e : Ev ` snd (FXf i)"
apply (simp add: isFailureOf_def)
apply (drule_tac x="i" in bspec, simp)
apply (simp add: subseteqEX_def restRefusal_def)
apply (auto)
done

lemmas isFailureOf_subset_alpha = isFailureOf_subset_alpha1
                                  isFailureOf_subset_alpha2

lemma isFailureOf_not_Tick[simp]:
   "[| (I, FXf) isFailureOf (I, PXf) ; i : I ; (s, Y) : fst (FXf i) |]
    ==> Tick ~: Y"
apply (simp add: isFailureOf_def)
apply (drule_tac x="i" in bspec, simp)
apply (simp add: subseteqEX_def restRefusal_def)
apply (auto)
done

lemma isFailureOf_same_alpha:
   "(I, FXf) isFailureOf (I, PXf)
    ==> ALL i:I. snd (PXf i) = snd (FXf i)"
by (simp add: isFailureOf_def)

(*********************************************************
                 StateOf subset
 *********************************************************)

lemma isStateOf_subset_alpha1:
   "[| (I, FXf) isFailureOf (I, PXf) ; 
       (t, Yf) isStateOf (I, FXf) ;
       i : I ; e : Yf i|]
    ==> e : (Ev ` (snd (PXf i)))"
apply (simp add: isStateOf_def)
apply (auto simp add: isFailureOf_same_alpha)
done

lemma isStateOf_subset_alpha2:
   "[| (I, FXf) isFailureOf (I, PXf) ; 
       (t, Yf) isStateOf (I, FXf) ;
       i : I ; e : Yf i|]
    ==> e : (Ev ` (snd (FXf i)))"
apply (simp add: isStateOf_def)
apply (auto)
done

lemmas isStateOf_subset_alpha = isStateOf_subset_alpha1 
                                isStateOf_subset_alpha2

lemma isStateOf_each_element:
   "[| (t, Yf) isStateOf (I, FXf) ; i : I |]
    ==> (t rest-tr snd (FXf i), Yf) isStateOf ({i}, FXf)"
apply (simp add: isStateOf_def)
apply (rule conjI)

 apply (simp add: ALP_def)
 apply (case_tac "Tick : sett t")
  apply (force)
  apply (subgoal_tac "sett (t rest-tr snd (FXf i)) <= sett (t rest-tr UNIV)")
  apply (case_tac "Tick : sett (t rest-tr snd (FXf i))", simp)

  apply (insert rest_tr_subset_event[of t "snd (FXf i)"])
  apply (blast)
  apply (rule rest_tr_sett_subseteq_sett)
  apply (simp)

apply (simp add: rest_tr_of_rest_tr_subset)
done

(*********************************************************
                        PAR
 *********************************************************)

(*---------------------------------*
 |           flattening            |
 *---------------------------------*)

(*** SF ***)

(* lemmas *)

lemma domSF_PAR_flattening_lm1:
   "ALP (V x) = Union (snd ` (%(i, j). snd (V j) i) ` {(i, x) |i. i : fst (V x)})"
by (auto simp add: ALP_def)

lemma domSF_PAR_flattening_lm2:
   "Union (snd ` (%i. ([||]:(fst (V i)) (snd (V i)), ALP (V i))) ` F) =
    Union (snd ` (%(i, j). snd (V j) i) ` {(i, j). j : F & i : fst (V j)})"
  apply (auto simp add: ALP_def)
(* not necessary for Isabelle 2017 
apply (rule_tac x="ia" in exI)
apply (rule_tac x="i" in exI)
apply (simp)
apply (rule_tac x="ba" in bexI)
apply (rule_tac x="aa" in bexI)
apply (simp_all)
*)
done

(* main *)

(*------------------*
 |      csp law     |
 *------------------*)

lemma cspF_PAR_flattening:
   "[| finite J ; ALL j:J. finite (fst (V j)) |] 
    ==> (PAR { (PAR (V j), ALP (V j)) | j:J }net) =F[M,M] 
        (PAR { ((snd (V j)) i) | (i,j):{(i, j). j : J & i : fst (V j)}}net)"
(*
apply (induct set: Finites)     Isabelle 2005
*)
apply (induct set: finite)     (* Isabelle 2007 *)
 
(* base *)
apply (simp add: PAR_def)

(* step *)
apply (simp add: PAR_def)
apply (rule cspF_rw_left)
apply (rule cspF_Rep_parallel_induct)
apply (simp_all)

apply (rule cspF_rw_left)
apply (rule cspF_Alpha_parallel_cong)
apply (simp)
apply (simp)
apply (rule cspF_reflex)

apply (subgoal_tac 
   "[||] i:F .. ([||]:(fst (V i)) (snd (V i)), ALP (V i))
  =F[M,M]
    [||] (i, j):{(i, j). j : F & i : (fst (V j))} .. (snd (V j)) i")
                                      (* ... sub 1 *)
apply (simp)
 (* sub 1 *)
 apply (simp add: eqF_semF[THEN sym])

apply (subgoal_tac 
   "{(i, j). (j = x | j : F) & i : fst (V j)} = 
    {(i,x) |i. i : fst (V x)} Un {(i, j). j : F & i : fst (V j)}")
                                      (* ... sub 2 *)
apply (simp)

apply (subgoal_tac "finite {(i, x)|i. i : fst (V x)}")
                                      (* ... sub 3 *)
apply (subgoal_tac "finite {(i, j). j : F & i : fst (V j)}")
                                      (* ... sub 4 *)
apply (rule cspF_rw_right)
apply (rule cspF_Rep_parallel_assoc)
apply (force)
apply (simp)+
apply (rule cspF_Alpha_parallel_cong)
apply (simp add: domSF_PAR_flattening_lm1)
(* for Isabelle 2017 *)
apply (simp add: domSF_PAR_flattening_lm2[simplified])
apply (rule cspF_Rep_parallel_index_eq)
 apply (simp)
 apply (rule_tac x="(%i. (i, x))" in exI)
 apply (simp)
 apply (simp add: inj_on_def)
 apply (force)
 apply (simp)

(* sub 4 *)
apply (simp add: finite_pair_set)

(* sub 3 *)
apply (subgoal_tac "{(i, x) |i. i : fst (V x)} = (%i. (i,x)) ` (fst (V x))")
apply (force)
apply (force)

(* sub 2 *)
apply (force)
done

(*** T and F ***)

lemma traces_PAR_flattening:
   "[| finite J ; ALL j:J. finite (fst (V j)) |] ==>
       traces (PAR { (PAR (V j), ALP (V j)) | j:J }net) M =
       traces (PAR { ((snd (V j)) i) | (i,j):{(i, j). j : J & i : fst (V j)} }net) M"
apply (insert cspF_PAR_flattening[of J V "(%p. (M p,,maxFof (M p)))"])
apply (simp add: cspF_eqF_semantics)
apply (subgoal_tac "(fstF o (%p. (M p ,, maxFof (M p)))) = M")
apply (simp)
apply (simp add: fun_eq_iff)
apply (rule allI)
apply (simp add: maxFof_domF pairF_fstF)
done

lemma failures_PAR_flattening:
   "[| finite J ; ALL j:J. finite (fst (V j)) |] ==>
       failures (PAR { (PAR (V j), ALP (V j)) | j:J }net) M =
       failures (PAR { ((snd (V j)) i) | (i,j):{(i, j). j : J & i : fst (V j)} }net) M"
apply (insert cspF_PAR_flattening[of J V M])
apply (simp add: cspF_eqF_semantics)
done

(*********************************************************
                      sub network
 *********************************************************)

(*** state ***)

lemma isStateOf_subset: 
  "[| (t,Yf) isStateOf (I,FXf) ; J <= I ; 
      X = {sY. EX i:J. sY : snd (FXf i)} |]
  ==> (t rest-tr X, Yf) isStateOf (J, FXf)"
apply (simp add: isStateOf_def ALP_def)
apply (rule conjI)
apply (insert rest_tr_subset_event[of t "X"])
apply (subgoal_tac "Tick ~: sett (t rest-tr X)")
apply (blast)
apply (force)

apply (rule ballI)
apply (elim conjE)
apply (drule_tac x="i" in bspec, fast)

apply (subgoal_tac "snd (FXf i) <= {sY. EX i:J. sY : snd (FXf i)}")
apply (simp add: rest_tr_of_rest_tr_subset)
by (auto)

lemma isStateOf_subsetI:
  "[| (t,Yf) isStateOf (I,FXf) ; 
      J <= I ; X = Union {(snd (FXf i))|i. i:J} |]
  ==> (t rest-tr X, Yf) isStateOf (J, FXf)"
apply (subgoal_tac "Union {(snd (FXf i))|i. i:J} = {sY. EX i:J. sY : snd (FXf i)}")
apply (simp add: isStateOf_subset)
by (auto)

(*********************************************************
                      isFailureOf
 *********************************************************)

lemma isFailureOf_largest:
   "{ ({(s,Y Int (Ev ` snd (PXf i)))|s Y. 
        (s,Y) :f failures (fst (PXf i)) MF}, snd (PXf i)) | i:I }Fnet 
     isFailureOf (I, PXf)"
apply (simp add: isFailureOf_def)
apply (simp add: subseteqEX_Int)
done

lemma isFailureOf_EX: "EX VF. VF isFailureOf V"
apply (rule_tac x=
  "{ ({(s,Y Int (Ev ` snd ((snd V) i))) |s Y. 
        (s,Y) :f failures (fst ((snd V) i)) MF}, 
      snd ((snd V) i)) | i: fst V }Fnet" in exI)
apply (insert decompo_V[of V])
apply (elim exE)
apply (simp add: isFailureOf_largest)
done

(****************** to add it again ******************)

declare disj_not1   [simp]
(*
declare Union_image_eq [simp]
declare Inter_image_eq [simp]
*)
(*
declare Sup_image_eq [simp]
declare Inf_image_eq [simp]
*)
end
