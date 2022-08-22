           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   | 
            |                 August 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2008         |
            |                   June 2008  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory CSP_T_semantics
imports CSP.Trace_op CSP.CSP_syntax Domain_T_cms

begin

(*****************************************************************

         1. semantic clause
         2. 
         3. 
         4. 

 *****************************************************************)

(*********************************************************
                    semantic clause
 *********************************************************)

primrec
  traces  :: "('p,'a) proc => ('p => 'a domT) => ('a domT)"
where
  "traces(STOP)   = (%M. {<>}t)"
 |"traces(SKIP)   = (%M. {<>, <Tick>}t)"
 |"traces(DIV)    = (%M. {<>}t)"
 |"traces(a -> P) = (%M. {t. t = <> | (EX s. t = <Ev a> ^^^ s & s :t traces(P) M) }t)"

 |"traces(? :X -> Pf) = (%M. {t. t = <> | 
                             (EX a s. t = <Ev a> ^^^ s & s :t traces(Pf a) M & a : X) }t)"

 |"traces(P [+] Q) = (%M. traces(P) M UnT traces(Q) M)"
 |"traces(P |~| Q) = (%M. traces(P) M UnT traces(Q) M)"
 |"traces(!! :C .. Pf) = (%M. {t. t = <> | 
                               (EX c : sumset C. t :t traces(Pf c) M) }t)"

 |"traces(IF b THEN P ELSE Q) = (%M. (if b then traces(P) M else traces(Q) M))"

 |"traces(P |[X]| Q) = (%M. {u. EX s t. u : s |[X]|tr t & 
                                  s :t traces(P) M & t :t traces(Q) M }t)"
 |"traces(P -- X)    = (%M. {t. EX s. t = s --tr X & s :t traces(P) M }t)"

 |"traces(P [[r]])   = (%M. {t. EX s. s [[r]]* t & s :t traces(P) M }t)"

 |"traces(P ;; Q)    = (%M. {u. (EX s. u = rmTick s & s :t traces(P) M ) |
                             (EX s t. u = s ^^^ t & s ^^^ <Tick> :t traces(P) M &
                                      t :t traces(Q) M & noTick s) }t)"
 |"traces(P |. n)    = (%M. traces(P) M .|. n)"
 |"traces($p)        = (%M. M p)"

declare traces.simps [simp del]

(*** for dealing with both !nat and !set ***)

lemma traces_inv_inj[simp]:
   "inj f ==> (EX c. (EX n. c = f n & n : N) & t :t traces (Pf (inv f c)) x)
            = (EX z:N. t :t traces (Pf z) x)"
by (auto)

lemma Rep_int_choice_traces_nat:
  "traces(!nat :N .. Pf) = (%M. {t. t = <> | (EX n:N. t :t traces(Pf n) M) }t)"
apply (simp add: Rep_int_choice_ss_def)
apply (simp add: traces.simps)
done

lemma Rep_int_choice_traces_set:
  "traces(!set :Xs .. Pf) = (%M. {t. t = <> | (EX X:Xs. t :t traces(Pf X) M) }t)"
apply (simp add: Rep_int_choice_ss_def)
apply (simp add: traces.simps)
done

(* contents \<longrightarrow> the_elem *)

lemma Rep_int_choice_traces_com_lm:
   "(EX z. (EX a. z = {a} & a : X) & t :t traces (Pf (the_elem z)) M)
    = (EX a:X. t :t traces (Pf a) M)"
apply (auto)
apply (rule_tac x="{a}" in exI)
apply (auto)
done

lemma Rep_int_choice_traces_com: 
  "traces(! :X .. Pf) = (%M. {t. t = <> | (EX a:X. t :t traces(Pf a) M) }t)"
apply (simp add: Rep_int_choice_com_def)
apply (simp add: Rep_int_choice_traces_set)
apply (simp add: Rep_int_choice_traces_com_lm)
done

lemma Rep_int_choice_traces_f: 
  "inj f ==> traces(!<f> :X .. Pf) = (%M. {t. t = <> | (EX a:X. t :t traces(Pf a) M) }t)"
apply (simp add: Rep_int_choice_f_def)
apply (simp add: Rep_int_choice_traces_com)
done

lemmas Rep_int_choice_traces =
       Rep_int_choice_traces_nat
       Rep_int_choice_traces_set
       Rep_int_choice_traces_com
       Rep_int_choice_traces_f


(*--------------------------------*
 |      Inductive_Ext_choice      |
 *--------------------------------*)

lemma Inductive_external_choice_P_domT: 
    "{t. t = <> | 
         (\<exists> P\<in>set l. t :t traces P M) } : domT"
  apply (simp add: domT_def HC_T1_def)
  apply (simp add: prefix_closed_def)
  apply (rule conjI)
  apply (rule_tac x="<>" in exI, simp)
  
  apply (intro allI impI)
  apply (elim conjE exE)
  apply (elim disjE, simp)
  
  apply (rule disjI2)
  apply (elim bexE)
  apply (rule_tac x="P" in bexI)
  apply (rule memT_prefix_closed)
  by (simp_all)

lemma Inductive_external_choice_i_domT: 
    "{t. t = <> | 
         (\<exists> i\<in>set l. t :t traces (Pf i) M) } : domT"
  apply (simp add: domT_def HC_T1_def)
  apply (simp add: prefix_closed_def)
  apply (rule conjI)
  apply (rule_tac x="<>" in exI, simp)
  
  apply (intro allI impI)
  apply (elim conjE exE)
  apply (elim disjE, simp)
  
  apply (rule disjI2)
  apply (elim bexE)
  apply (rule_tac x="i" in bexI)
  apply (rule memT_prefix_closed)
  by (simp_all)

lemmas Inductive_external_choice_domT =
    Inductive_external_choice_P_domT
    Inductive_external_choice_i_domT

theorem Inductive_ext_choice_traces:
    "traces ([+] l) M = {u. u = <> \<or> (\<exists> P\<in> set l. u :t traces P M)}t"
  apply (induct_tac l)
  apply (simp add: traces.simps)
  apply (simp add: traces.simps S_UnT_T set_CollectT_commute_left)
  by (simp add: CollectT_open_memT Inductive_external_choice_domT)


(*--------------------------------*
 |      Replicated_Ext_choice     |
 *--------------------------------*)

(*theorem Rep_ext_choice_traces:
    "finite X \<Longrightarrow> l = (SOME l. l isListOf X)
     \<Longrightarrow> traces ([+] x:X .. PXf x) M = {u. u = <> \<or> (\<exists> P\<in>(set (map PXf l)). u :t traces P M)}t"
  apply (simp (no_asm) only: Rep_ext_choice_def)
  by (simp only: Inductive_ext_choice_traces)*)

theorem Rep_ext_choice_traces:
    "traces ([+] X .. PXf) M = {u. u = <> \<or> (\<exists> i\<in> set X. u :t traces (PXf i) M)}t"
  apply (simp add: Rep_ext_choice_def)
  by (simp add: Inductive_ext_choice_traces)



(*--------------------------------*
 |       Inductive_interleave     |
 *--------------------------------*)

theorem Inductive_interleave_traces :
    "traces ( ||| l) M = {u. ((l = [] \<and> (u = <> \<or> u = <Tick>))
                           \<or> (l \<noteq> [] \<and> (\<exists>s t. u \<in> s |[{}]|tr t
                                             \<and> s :t traces (hd l) M
                                             \<and> t :t traces ( ||| tl l) M))) }t"
  apply (induct_tac l)
  by (simp_all add: traces.simps nilt_one_CollectT)

(*--------------------------------*
 |         Rep_interleaving       |
 *--------------------------------*)

theorem Rep_interleaving_traces :
    "traces ( ||| X .. PXf) M = {u. ((X = [] \<and> (u = <> \<or> u = <Tick>))
                                  \<or> (X \<noteq> [] \<and> (\<exists>s t. u \<in> s |[{}]|tr t
                                                   \<and> s :t traces (PXf (hd X)) M
                                                   \<and> t :t traces ( ||| map PXf (tl X)) M))) }t"
  apply (simp only: Rep_interleaving_def)
  apply (rule trans, rule Inductive_interleave_traces)
  by (case_tac X, simp_all add: map_tl hd_map)


(*
lemma isListOf_nonEmpty_minus_hd :
    "\<And>X . X \<noteq> {} \<Longrightarrow> x isListOf X \<Longrightarrow> xa isListOf X - {hd x} \<Longrightarrow>
    xa = tl x"
  apply (frule isListOf_distinct)
  apply (frule isListOf_set_eq)
  apply (frule_tac X="X - {hd x}" in isListOf_distinct)
  apply (frule_tac X="X - {hd x}" in isListOf_set_eq)
  apply (elim conjE)
  oops (* xa could be a permutation of x elements *)
*)

lemma Rep_interleaving_traces :
    "traces ( ||| :X .. PXf) M = {u. (X = [] \<and> (u = <> \<or> u = <Tick>))
                                   \<or> (X \<noteq> [] \<and> (\<exists>i\<in> set X . (\<exists>s t. u \<in> s |[{}]|tr t
                                                           \<and> s :t traces (PXf i) M
                                                           \<and> t :t traces ( ||| :(remove1 i X) .. PXf) M))) }t"
  apply (simp add: Rep_interleaving_def)
  apply (rule trans, rule Inductive_interleave_traces)
  apply (induct_tac X, simp_all add: map_tl hd_map)
  apply (rule CollectT_eq)
  oops


lemmas traces_iff = traces.simps Rep_int_choice_traces
                    (*Inductive_ext_choice_traces
                    Rep_ext_choice_traces
                    Inductive_interleave_traces
                    Rep_interleaving_traces*)

(*==================================================================*
                            traces model
 *==================================================================*)

lemma traces_Int_choice_Ext_choice: "traces(P |~| Q) = traces(P [+] Q)"
(* apply (simp add: expand_fun_eq) *)
apply (simp add: fun_eq_iff)
by (simp add: traces_iff)

(*************************************************************
                   set of length of traces+
  lengthset is related to Depth restriction operator (P |. n) 
 *************************************************************)

definition
  lengthset   :: "('p,'a) proc =>  ('p => 'a domT) => nat set"
  where
  lengthset_def:
    "lengthset P == (%M. {n. EX t. t :t traces P M & 
                      (n = lengtht t | n = Suc (lengtht t) & noTick t)})"

(*********************************************************
                     semantics
 *********************************************************)

(*** M-parametarized semantics ***)

definition
  semTf  :: "('p,'a) proc => ('p => 'a domT) => 'a domT" ("[[_]]Tf")
  where  
  semTf_def : "[[P]]Tf == (%M. traces(P) M)"
  
definition  
  semTfun  :: "('p => ('p,'a) proc) =>  ('p => 'a domT) => ('p => 'a domT)" 
                                                         ("[[_]]Tfun")
  where
  semTfun_def : "[[Pf]]Tfun == (%M. %p. [[Pf p]]Tf M)"

(*
notation (xsymbols) semTf   ("\<lbrakk>_\<rbrakk>Tf")
notation (xsymbols) semTfun ("\<lbrakk>_\<rbrakk>Tfun")
*)

(*** relation ***)

lemma semTf_semTfun:
  "(%p. [[Pf p]]Tf M) = [[Pf]]Tfun M"
by (simp add: semTfun_def semTf_def)

lemma traces_semTfun:
  "(%p. traces (Pf p) M) = [[Pf]]Tfun M"
by (simp add: semTfun_def semTf_def)

(*------------------------------------------------------------------*
        M such that [[p]]T M = [[PNfun(p)]]T M
   such M is the fixed point of the function [[PNfun(p)]]Tfun
 *------------------------------------------------------------------*)

definition
  semTfix  :: "('p => ('p,'a) proc) => ('p => 'a domT)"      ("[[_]]Tfix")
  where
  semTfix_def : 
   "[[Pf]]Tfix == (if (FPmode = CMSmode) then (UFP ([[Pf]]Tfun))
                                         else (LFP ([[Pf]]Tfun)))"
(*
notation (xsymbols) semTfix ("\<lbrakk>_\<rbrakk>Tfix")
*)

definition
  MT :: "('p => 'a domT)"
  where
  MT_def : "MT == [[PNfun]]Tfix"

(*** semantics ***)

definition
  semT  :: "('p,'a) proc => 'a domT"      ("[[_]]T")
  where
  semT_def : "[[P]]T == [[P]]Tf MT"

(*
notation (xsymbols) semT ("\<lbrakk>_\<rbrakk>T")
*)

(*********************************************************
              relations over processes
 *********************************************************)

definition
  refT :: "('p,'a) proc => ('p => 'a domT) => 
           ('q => 'a domT) => ('q,'a) proc => bool"
                               ("(0_ /<=T[_,_] /_)" [51,0,0,50] 50)
  where
  refT_def : "P1 <=T[M1,M2] P2 == [[P2]]Tf M2 <= [[P1]]Tf M1"
  
definition  
  eqT :: "('p,'a) proc => ('p => 'a domT) => 
           ('q => 'a domT) => ('q,'a) proc => bool"
                               ("(0_ /=T[_,_] /_)" [51,0,0,50] 50)
  where  
  eqT_def  : "P1  =T[M1,M2] P2 == [[P1]]Tf M1  = [[P2]]Tf M2"

(*------------------------------------*
 |              X-Symbols             |
 *------------------------------------*)
(*
notation (xsymbols) refT ("(0_ /\<sqsubseteq>T[_,_] /_)" [51,0,0,50] 50)
*)
(*********************************************************
        relations over processes (fixed point)
 *********************************************************)

abbreviation
 refTfix :: "('p,'a) proc => ('q,'a) proc => bool" ("(0_ /<=T /_)" [51,50] 50)
 where "P1 <=T P2 == P1 <=T[MT,MT] P2"

abbreviation
 eqTfix :: "('p,'a) proc => ('q,'a) proc => bool"  ("(0_ /=T /_)" [51,50] 50)
 where "P1  =T P2 == P1  =T[MT,MT] P2"

(* =T and <=T *)

lemma refT_semT: "P1 <=T P2 == [[P2]]T <= [[P1]]T"
apply (simp add: refT_def)
apply (simp add: semT_def)
done

lemma eqT_semT: "P1 =T P2 == [[P1]]T = [[P2]]T"
apply (simp add: eqT_def)
apply (simp add: semT_def)
done

(*------------------------------------*
 |              X-Symbols             |
 *------------------------------------*)

(*
notation (xsymbols) refTfix ("(0_ /\<sqsubseteq>T /_)" [51,50] 50)
*)

(*------------------*
 |      csp law     |
 *------------------*)

(*** semantics ***)

lemma cspT_eqT_semantics:
  "(P =T[M1,M2] Q) = (traces P M1 = traces Q M2)"
by (simp add: eqT_def semT_def semTf_def)

lemma cspT_refT_semantics:
  "(P <=T[M1,M2] Q) = (traces Q M2 <= traces P M1)"
by (simp add: refT_def semT_def semTf_def)

lemmas cspT_semantics = cspT_eqT_semantics  cspT_refT_semantics

(*** eq and ref ***)

lemma cspT_eq_ref_iff:
  "(P1 =T[M1,M2] P2) = (P1 <=T[M1,M2] P2 & P2 <=T[M2,M1] P1)"
by (auto simp add: refT_def eqT_def intro:order_antisym)

lemma cspT_eq_ref:
  "P1 =T[M1,M2] P2 ==> P1 <=T[M1,M2] P2"
by (simp add: cspT_eq_ref_iff)

lemma cspT_ref_eq:
  "[| P1 <=T[M1,M2] P2 ; P2 <=T[M2,M1] P1 |] ==> P1 =T[M1,M2] P2"
by (simp add: cspT_eq_ref_iff)

(*** reflexivity ***)

lemma cspT_reflex_eq_P[simp]: "P =T[M,M] P"
by (simp add: eqT_def)

lemma cspT_reflex_eq_STOP[simp]: "STOP =T[M1,M2] STOP"   
apply (simp add: cspT_semantics)
apply (simp add: traces_iff)
done

lemma cspT_reflex_eq_SKIP[simp]: "SKIP =T[M1,M2] SKIP"   
apply (simp add: cspT_semantics)
apply (simp add: traces_iff)
done

lemma cspT_reflex_eq_DIV[simp]: "DIV =T[M1,M2] DIV"   
apply (simp add: cspT_semantics)
apply (simp add: traces_iff)
done

lemmas cspT_reflex_eq = cspT_reflex_eq_P
                        cspT_reflex_eq_STOP
                        cspT_reflex_eq_SKIP
                        cspT_reflex_eq_DIV


lemma cspT_reflex_ref_P[simp]: "P <=T[M,M] P"
by (simp add: refT_def)

lemma cspT_reflex_ref_STOP[simp]: "STOP <=T[M1,M2] STOP"   
apply (simp add: cspT_semantics)
apply (simp add: traces_iff)
done

lemma cspT_reflex_ref_SKIP[simp]: "SKIP <=T[M1,M2] SKIP"   
apply (simp add: cspT_semantics)
apply (simp add: traces_iff)
done

lemma cspT_reflex_ref_DIV[simp]: "DIV <=T[M1,M2] DIV"   
apply (simp add: cspT_semantics)
apply (simp add: traces_iff)
done

lemmas cspT_reflex_ref = cspT_reflex_ref_P
                         cspT_reflex_ref_STOP
                         cspT_reflex_ref_SKIP
                         cspT_reflex_ref_DIV

lemmas cspT_reflex = cspT_reflex_eq cspT_reflex_ref

(*** symmetry ***)

lemma cspT_sym: "P1 =T[M1,M2] P2 ==> P2 =T[M2,M1] P1"
by (simp add: eqT_def)

lemma cspT_symE:
  "[| P1 =T[M1,M2] P2 ; P2 =T[M2,M1] P1 ==> Z |] ==> Z"
by (simp add: eqT_def)

(*** transitivity ***)

lemma cspT_trans_left_eq: 
  "[| P1 =T[M1,M2] P2 ; P2 =T[M2,M3] P3 |] ==> P1 =T[M1,M3] P3"
by (simp add: eqT_def)

lemma cspT_trans_left_ref: 
  "[| P1 <=T[M1,M2] P2 ; P2 <=T[M2,M3] P3 |] ==> P1 <=T[M1,M3] P3"
by (simp add: refT_def)

lemmas cspT_trans_left = cspT_trans_left_eq cspT_trans_left_ref
lemmas cspT_trans = cspT_trans_left

lemma cspT_trans_right_eq: 
  "[| P2 =T[M2,M3] P3 ; P1 =T[M1,M2] P2 |] ==> P1 =T[M1,M3] P3"
by (simp add: eqT_def)

lemma cspT_trans_right_ref: 
  "[| P2 <=T[M2,M3] P3 ;  P1 <=T[M1,M2] P2 |] ==> P1 <=T[M1,M3] P3"
by (simp add: refT_def)

lemmas cspT_trans_right = cspT_trans_right_eq cspT_trans_right_ref

(*** rewrite (eq) ***)

lemma cspT_rw_left_eq_MT:
  "[| P1 =T P2 ; P2 =T P3 |] ==> P1 =T P3"
by (simp add: eqT_def)

lemma cspT_rw_left_eq:
  "[| P1 =T[M1,M1] P2 ; P2 =T[M1,M3] P3 |] ==> P1 =T[M1,M3] P3"
by (simp add: eqT_def)

lemma cspT_rw_left_ref_MT:
  "[| P1 =T P2 ; P2 <=T P3 |] ==> P1 <=T P3"
by (simp add: refT_def eqT_def)

lemma cspT_rw_left_ref:
  "[| P1 =T[M1,M1] P2 ; P2 <=T[M1,M3] P3 |] ==> P1 <=T[M1,M3] P3"
by (simp add: refT_def eqT_def)

lemmas cspT_rw_left = 
   cspT_rw_left_eq_MT cspT_rw_left_ref_MT
   cspT_rw_left_eq cspT_rw_left_ref

lemma cspT_rw_right_eq:
  "[| P3 =T[M3,M3] P2 ; P1 =T[M1,M3] P2 |] ==> P1 =T[M1,M3] P3"
by (simp add: eqT_def)

lemma cspT_rw_right_eq_MT:
  "[| P3 =T P2 ; P1 =T P2 |] ==> P1 =T P3"
by (simp add: eqT_def)

lemma cspT_rw_right_ref:
  "[| P3 =T[M3,M3] P2 ; P1 <=T[M1,M3] P2 |] ==> P1 <=T[M1,M3] P3"
by (simp add: refT_def eqT_def)

lemma cspT_rw_right_ref_MT:
  "[| P3 =T P2 ; P1 <=T P2 |] ==> P1 <=T P3"
by (simp add: refT_def eqT_def)

lemmas cspT_rw_right =
   cspT_rw_right_eq_MT cspT_rw_right_ref_MT
   cspT_rw_right_eq cspT_rw_right_ref

(*** rewrite (ref) ***)

lemma cspT_tr_left_eq:
   "[| P1 =T[M1,M1] P2 ; P2 =T[M1,M3] P3 |] ==> P1 =T[M1,M3] P3"
by (simp add: eqT_def)

lemma cspT_tr_left_ref:
   "[| P1 <=T[M1,M1] P2 ; P2 <=T[M1,M3] P3 |] ==> P1 <=T[M1,M3] P3"
by (simp add: refT_def eqT_def)

lemmas cspT_tr_left = cspT_tr_left_eq cspT_tr_left_ref

lemma cspT_tr_right_eq:
   "[| P2 =T[M3,M3] P3 ; P1 =T[M1,M3] P2 |] ==> P1 =T[M1,M3] P3"
by (simp add: eqT_def)

lemma cspT_tr_right_ref:
  "[| P2 <=T[M3,M3] P3 ; P1 <=T[M1,M3] P2 |] ==> P1 <=T[M1,M3] P3"
by (simp add: refT_def eqT_def)

lemmas cspT_tr_right = cspT_tr_right_eq cspT_tr_right_ref



(*----------------------------------------*
 |   rewriting processes in assumptions   |
 *----------------------------------------*)

(*** rewrite (eq) ***)

lemma cspT_rw_left_eqE_MF:
  "[| P1 =T P3 ; P1 =T P2 ; [| P2 =T P3 |] ==> R |] ==> R"
apply (subgoal_tac "P2 =T P3")
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_sym)
apply (simp)
apply (simp)
done

lemma cspT_rw_left_eqE:
  "[| P1 =T[M1,M3] P3 ; P1 =T[M1,M1] P2 ; 
      [| P2 =T[M1,M3] P3 |] ==> R |] ==> R"
apply (subgoal_tac "P2 =T[M1,M3] P3")
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_sym)
apply (simp)
apply (simp)
done

lemma cspT_rw_left_refE_MF:
  "[| P1 <=T P3 ; P1 =T P2 ; [| P2 <=T P3 |] ==> R |] ==> R"
apply (subgoal_tac "P2 <=T P3")
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_sym)
apply (simp)
apply (simp)
done

lemma cspT_rw_left_refE:
  "[| P1 <=T[M1,M3] P3 ; P1 =T[M1,M1] P2 ; 
      [| P2 <=T[M1,M3] P3 |] ==> R |] ==> R"
apply (subgoal_tac "P2 <=T[M1,M3] P3")
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_sym)
apply (simp)
apply (simp)
done

lemmas cspT_rw_leftE = 
   cspT_rw_left_eqE_MF cspT_rw_left_refE_MF
   cspT_rw_left_eqE    cspT_rw_left_refE


(* right *)

lemma cspT_rw_right_eqE_MF:
  "[| P1 =T P3 ; P3 =T P2 ; [| P1 =T P2 |] ==> R |] ==> R"
apply (subgoal_tac "P1 =T P2")
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_sym)
apply (simp)
apply (simp)
done

lemma cspT_rw_right_eqE:
  "[| P1 =T[M1,M3] P3 ; P3 =T[M3,M3] P2 ;
      [| P1 =T[M1,M3] P2 |] ==> R |] ==> R"
apply (subgoal_tac "P1 =T[M1,M3] P2")
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_sym)
apply (simp)
apply (simp)
done

lemma cspT_rw_right_refE_MF:
  "[| P1 <=T P3 ; P3 =T P2 ; [| P1 <=T P2 |] ==> R |] ==> R"
apply (subgoal_tac "P1 <=T P2")
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_sym)
apply (simp)
apply (simp)
done

lemma cspT_rw_right_refE:
  "[| P1 <=T[M1,M3] P3 ; P3 =T[M3,M3] P2 ;
      [| P1 <=T[M1,M3] P2 |] ==> R |] ==> R"
apply (subgoal_tac "P1 <=T[M1,M3] P2")
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_sym)
apply (simp)
apply (simp)
done

lemmas cspT_rw_rightE = 
   cspT_rw_right_eqE_MF cspT_rw_right_refE_MF
   cspT_rw_right_eqE    cspT_rw_right_refE



(*-----------------------------------------*
 |                   noPN                  |
 *-----------------------------------------*)

 (* lemma "\<lbrakk> ? :s -> f = P \<rbrakk> \<Longrightarrow> range f = UNIV" *) 

lemma traces_noPN_Constant_lm_EC: 
  "[| ALL P:range Pf. (EX T. traces P = (%M. T)) |]
       ==> (EX T2. traces (? :X -> Pf) = (%M. T2))"
apply (auto simp add: traces_iff)
apply (simp add: choice_ALL_EX)
apply (erule exE)
apply (auto)
done

lemma traces_noPN_Constant_lm_RIC: 
  "[| ALL P:range Pf. (EX T. traces P = (%M. T)) |]
   ==> (EX T2. traces (!! :X .. Pf) = (%M. T2))"
apply (auto simp add: traces_iff)
apply (simp add: choice_ALL_EX)
apply (erule exE)
apply (auto)
done

lemma traces_noPN_Constant_lm:
  "noPN P --> (EX T. traces P = (%M. T))"

apply (induct_tac P)
apply (simp add: traces_iff, force)
apply (simp add: traces_iff, force)
apply (simp add: traces_iff, force)
apply (simp add: traces_iff, force)

(* Ext_pre_choice *)
apply (simp add: traces_noPN_Constant_lm_EC)

(* Isabelle 2013   
(* apply (subgoal_tac "ALL x. EX T. traces (fun2 x) = (%M. T)") isabelle 2011 *)
 apply (subgoal_tac "ALL x. EX T. traces (fun x) = (%M. T)")
 apply (simp add: choice_ALL_EX)
 apply (erule exE)
 apply (simp add: traces_iff)
 apply (force) 
 apply (simp)

*)
apply (simp add: traces_iff, force)
apply (simp add: traces_iff, force)

(* Rep_int_choice *)
apply (simp add: traces_noPN_Constant_lm_RIC)

(* Isabelle 2013
apply (intro impI)
 apply (simp)
 apply (subgoal_tac "ALL x. EX T. traces (fun x) = (%M. T)")
  apply (simp add: choice_ALL_EX)
 apply (erule exE)
apply (simp add: traces_iff)
apply (force)
apply (simp)
*)

(* IF *)
 apply (simp add: traces_iff)
 apply (case_tac "x1")
 apply (simp)
 apply (simp)

apply (simp add: traces_iff, force)
apply (simp add: traces_iff, force)
apply (simp add: traces_iff, force)
apply (simp add: traces_iff, force)
apply (simp add: traces_iff, force)
apply (simp add: traces_iff)
done

lemma traces_noPN_Constant:
  "noPN P ==> (EX T. traces P = (%M. T))"
apply (simp add: traces_noPN_Constant_lm)
done

(*-----------------------------------------*
 |              substitution               |
 *-----------------------------------------*)

lemma semT_subst:
  "[[P<<f]]T = [[P]]Tf (%q. [[f q]]T)"
apply (induct_tac P)
apply (simp_all add: semT_def semTf_def traces_iff)
done

lemma semT_subst_semTfun:
  "(%q. [[ (Pf q)<<f ]]T) = ([[Pf]]Tfun (%q. [[f q]]T))"
apply (simp add: semTfun_def)
apply (simp add: fun_eq_iff)
apply (rule allI)
apply (simp add: semT_subst)
done

lemma traces_subst:
  "traces(P<<f) M = traces P (%q. traces(f q) M)"
apply (induct_tac P)
apply (simp_all add: semT_def traces_iff)
done

end
