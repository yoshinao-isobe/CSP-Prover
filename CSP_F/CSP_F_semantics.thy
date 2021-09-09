           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                 August 2005  (modified)   |
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
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_semantics
imports CSP_T.CSP_T_semantics Domain_F_cms
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
  failures :: "('p,'a) proc =>  ('p => 'a domF) => 'a setF"
where
  "failures(STOP)    = (%M. {f. EX X. f = (<>, X) }f)"

 |"failures(SKIP)    = (%M. {f. (EX X. f = (<>, X) & X <= Evset) |
                                (EX X. f = (<Tick>, X)) }f)"
 |"failures(DIV)     = (%M. {}f)"

 |"failures(a -> P)  = (%M. {f. (EX X.   f = (<>,X) & Ev a ~: X) |
                         (EX s X. f = (<Ev a> ^^^ s, X) & (s,X) :f failures(P) M ) }f)"

 |"failures(? :X -> Pf) = (%M. {f. (EX Y.     f = (<>,Y) & Ev`X Int Y = {}) |
                         (EX a s Y. f = (<Ev a> ^^^ s, Y) & 
                                   (s,Y) :f failures(Pf a) M & a : X) }f)"

 |"failures(P [+] Q) = (%M. {f. 
       (EX   X. f = (<>,X) & f :f failures(P) M IntF failures(Q) M) |
       (EX s X. f = (s,X)  & f :f failures(P) M UnF  failures(Q) M & s ~= <>) |
       (EX   X. f = (<>,X) & <Tick> :t traces(P) (fstF o M) UnT 
                                       traces(Q) (fstF o M) & X <= Evset) }f)"

 |"failures(P |~| Q) = (%M. failures(P) M UnF failures(Q) M)"

 |"failures(!! :C .. Pf) = (%M. {f. EX c: sumset C. f :f failures(Pf c) M}f)"

 |"failures(IF b THEN P ELSE Q) = (%M. if b then failures(P) M else failures(Q) M)"

 |"failures(P |[X]| Q)  = (%M. {f. 
      EX u Y Z. f = (u, Y Un Z) & Y-((Ev`X) Un {Tick})= Z-((Ev`X) Un {Tick}) &
     (EX s t. u : s |[X]|tr t & (s,Y) :f failures(P) M & (t,Z) :f failures(Q) M) }f)"

 |"failures(P -- X)  = (%M. {f. 
      EX s Y. f = (s --tr X, Y) & (s,(Ev`X) Un Y) :f failures(P) M}f)"

 |"failures(P [[r]]) = (%M. {f. 
      EX s t X. f = (t,X) & s [[r]]* t & (s, [[r]]inv X) :f failures(P) M }f)" 

 |"failures(P ;; Q) = (%M. {f. 
     (EX t X. f = (t,X) & (t, X Un {Tick}) :f failures(P) M & noTick t) |
     (EX s t X. f = (s ^^^ t,X) & s ^^^ <Tick> :t traces(P) (fstF o M) & 
                                    (t, X) :f failures(Q) M & noTick s) }f)"

 |"failures(P |. n) = (%M. failures(P) M .|. n)"

 |"failures($p)     = (%M. sndF (M p))"

declare failures.simps [simp del]

(*** for dealing with both !nat and !set ***)

lemma failures_inv_inj[simp]:
   "inj g ==> (EX c. (EX n. c = g n & n : N) & f :f failures (Pf (inv g c)) x)
            = (EX z:N. f :f failures (Pf z) x)"
by (auto)

lemma Rep_int_choice_failures_nat:
  "failures(!nat :N .. Pf) = (%M. {f. EX n:N. f :f failures(Pf n) M}f)"
apply (simp add: Rep_int_choice_ss_def)
apply (simp add: failures.simps)
done

lemma Rep_int_choice_failures_set:
  "failures(!set :Xs .. Pf) = (%M. {f. EX X:Xs. f :f failures(Pf X) M}f)"
apply (simp add: Rep_int_choice_ss_def)
apply (simp add: failures.simps)
done

lemma Rep_int_choice_failures_com_lm:
   "(EX z. (EX a. z = {a} & a : X) & f :f failures (Pf (the_elem z)) M)
  = (EX a:X. f :f failures (Pf a) M)"
apply (auto)
apply (rule_tac x="{a}" in exI)
apply (auto)
done

lemma Rep_int_choice_failures_com: 
  "failures(! :X .. Pf) = (%M. {f. EX a:X. f :f failures(Pf a) M}f)"
apply (simp add: Rep_int_choice_com_def)
apply (simp add: Rep_int_choice_failures_set)
apply (simp add: Rep_int_choice_failures_com_lm)
done

lemma Rep_int_choice_failures_f: 
  "inj g ==> failures(!<g> :X .. Pf) = 
             (%M. {f. EX a:X. f :f failures(Pf a) M}f)"
apply (simp add: Rep_int_choice_f_def)
apply (simp add: Rep_int_choice_failures_com)
done

lemmas Rep_int_choice_failures =
       Rep_int_choice_failures_nat
       Rep_int_choice_failures_set
       Rep_int_choice_failures_com
       Rep_int_choice_failures_f


(*--------------------------------*
 |      Inductive_Ext_choice      |
 *--------------------------------*)

abbreviation in_f_Inductive_ext_choice ::
    "(('p,'a) proc) list \<Rightarrow> ('p \<Rightarrow> 'a domF) \<Rightarrow> 'a failure \<Rightarrow> bool"
where "in_f_Inductive_ext_choice l Mf f ==
        ((l = [] \<and> (\<exists> X. f = (<>,X)))
        \<or>(l \<noteq> []
         \<and> ((\<exists>X. f = (<>,X) \<and> f :f failures(hd l) Mf
                                    IntF failures([+] tl l) Mf)
            \<or> (\<exists>s X. f = (s,X)
                \<and> f :f failures(hd l) Mf
                        UnF failures([+] tl l) Mf
                \<and> s ~= <>)
            \<or> (\<exists>X. f = (<>,X)
                \<and> <Tick> :t traces(hd l) (fstF \<circ> Mf)
                            UnT traces([+] tl l) (fstF \<circ> Mf)
                \<and> X <= Evset))))"


theorem Inductive_ext_choice_failures :
    "failures ([+] PXs) Mf = { f. in_f_Inductive_ext_choice PXs Mf f }f"
  apply (induct PXs, simp add: failures.simps)
  by (simp add: failures.simps traces_iff comp_def)


(*--------------------------------*
 |      Replicated_Ext_choice     |
 *--------------------------------*)

theorem Rep_ext_choice_failures :
    "finite X \<Longrightarrow> l = map PXf (SOME l. l isListOf X)
     \<Longrightarrow> failures ([+] X .. PXf) Mf = {f. in_f_Inductive_ext_choice l Mf f }f"
  apply (simp (no_asm) only: Rep_ext_choice_def)
  by (simp only: Inductive_ext_choice_failures[THEN sym])


(*--------------------------------*
 |        Induct_interleave       |
 *--------------------------------*)

abbreviation in_f_Induct_interleave ::
    "(('p,'a) proc) list \<Rightarrow> ('p \<Rightarrow> 'a domF) \<Rightarrow> 'a failure \<Rightarrow> bool"
where "in_f_Induct_interleave l Mf f ==
    ((l = [] \<and> ((EX X. f = (<>, X) & X <= Evset) \<or> (EX X. f = (<Tick>, X))))
    \<or> (l \<noteq> [] \<and> (EX u Y Z. f = (u, Y Un Z) \<and> Y-{Tick}= Z-{Tick}
               \<and> (EX s t. u : s |[{}]|tr t
                        \<and> (s,Y) :f failures(hd l) Mf
                        \<and> (t,Z) :f failures( ||| tl l) Mf))))"

theorem Inductive_interleave_failures :
    "failures ( ||| l) Mf = {f. in_f_Induct_interleave l Mf f }f"
  apply (induction l)
  apply (simp add: failures.simps)
  by (simp add: failures.simps traces_iff)


(*--------------------------------*
 |         Rep_interleaving       |
 *--------------------------------*)

theorem Rep_interleaving_failures :
    "finite X \<Longrightarrow> l = map PXf (SOME l. l isListOf X)
     \<Longrightarrow> failures ( ||| X .. PXf) Mf = {f. in_f_Induct_interleave l Mf f }f"
  by (simp (no_asm) only: Rep_interleaving_def Inductive_interleave_failures[THEN sym], simp)


(*
lemmas failures_def = failures.simps Rep_int_choice_failures
*)
lemmas failures_iff = failures.simps
                      Rep_int_choice_failures
                      (*Inductive_ext_choice_failures
                      Rep_ext_choice_failures*)

(*********************************************************
                     semantics
 *********************************************************)

definition
  semFf   :: "('p,'a) proc => ('p => 'a domF) => 'a domF" ("[[_]]Ff")
  where
  semFf_def  : "[[P]]Ff == (%M. (traces(P) (fstF o M) ,, failures(P) M))"
  
definition  
  semFfun :: "('p => ('p,'a) proc) => ('p => 'a domF) => ('p => 'a domF)" 
                                                         ("[[_]]Ffun")
  where                                                         
  semFfun_def: "[[Pf]]Ffun == (%M. %p. [[Pf p]]Ff M)"

(*
notation (xsymbols) semFf   ("\<lbrakk>_\<rbrakk>Ff")
notation (xsymbols) semFfun ("\<lbrakk>_\<rbrakk>Ffun")
*)

(*** relation ***)

lemma semFf_semFfun:
  "(%p. [[Pf p]]Ff M) = [[Pf]]Ffun M"
by (simp add: semFfun_def semFf_def)

(*------------------------------------------------------------------*
        M such that [[p]]Ff M = [[PNfun(p)]]Ff M
   such M is the fixed point of the function [[PNfun(p)]]Ffun
 *------------------------------------------------------------------*)

definition
  semFfix  :: "('p => ('p,'a) proc) => ('p => 'a domF)"      ("[[_]]Ffix")
  where
  semFfix_def : 
   "[[Pf]]Ffix == (if (FPmode = CMSmode) then (UFP ([[Pf]]Ffun))
                                         else (LFP ([[Pf]]Ffun)))"

(*
notation (xsymbols) semFfix ("\<lbrakk>_\<rbrakk>Ffix")
*)

definition
 MF :: "('p => 'a domF)"
 where
 MF_def : "MF == [[PNfun]]Ffix"

(*** semantics ***)

definition
  semF  :: "('p,'a) proc => 'a domF"      ("[[_]]F")
  where
  semF_def : "[[P]]F == [[P]]Ff MF"
(*
notation (xsymbols) semF ("\<lbrakk>_\<rbrakk>F")
*)

(*********************************************************
              relations over processes
 *********************************************************)

definition
  refF :: "('p,'a) proc => ('p => 'a domF) => 
           ('q => 'a domF) => ('q,'a) proc => bool"
                               ("(0_ /<=F[_,_] /_)" [51,0,0,50] 50)
  where
  refF_def : "P1 <=F[M1,M2] P2 == [[P2]]Ff M2 <= [[P1]]Ff M1"
  
definition  
  eqF :: "('p,'a) proc => ('p => 'a domF) => 
           ('q => 'a domF) => ('q,'a) proc => bool"
                               ("(0_ /=F[_,_] /_)"[51,0,0,50] 50)
  where
  eqF_def  : "P1  =F[M1,M2] P2 == [[P1]]Ff M1  = [[P2]]Ff M2"

(*------------------------------------*
 |              X-Symbols             |
 *------------------------------------*)

(*
notation (xsymbols) refF ("(0_ /\<sqsubseteq>F[_,_] /_)" [51,100,100,50] 50)
*)

(*********************************************************
        relations over processes (fixed point)
 *********************************************************)

abbreviation
 refFfix :: "('p,'a) proc => ('q,'a) proc => bool" ("(0_ /<=F /_)" [51,50] 50)
 where "P1 <=F P2 == P1 <=F[MF,MF] P2"

abbreviation
 eqFfix :: "('p,'a) proc => ('q,'a) proc => bool"  ("(0_ /=F /_)" [51,50] 50)
 where "P1  =F P2 == P1  =F[MF,MF] P2"

(* =F and <=F *)

lemma refF_semF: "(P1 <=F P2) = ([[P2]]F <= [[P1]]F)"
apply (simp add: refF_def)
apply (simp add: semF_def)
done

lemma eqF_semF: "(P1 =F P2) = ([[P1]]F = [[P2]]F)"
apply (simp add: eqF_def)
apply (simp add: semF_def)
done

(*------------------------------------*
 |              X-Symbols             |
 *------------------------------------*)
(*
notation (xsymbols) refFfix ("(0_ /\<sqsubseteq>F /_)" [51,50] 50)
*)

(*------------------*
 |      csp law     |
 *------------------*)

(*** eq and ref ***)

lemma cspF_eq_ref_iff:
 "(P1 =F[M1,M2] P2) = (P1 <=F[M1,M2] P2 & P2 <=F[M2,M1] P1)"
by (auto simp add: refF_def eqF_def)

lemma cspF_eq_ref:
  "P1 =F[M1,M2] P2 ==> P1 <=F[M1,M2] P2"
by (simp add: cspF_eq_ref_iff)

lemma cspF_ref_eq:
  "[| P1 <=F[M1,M2] P2 ; P2 <=F[M2,M1] P1 |] ==> P1 =F[M1,M2] P2"
by (simp add: cspF_eq_ref_iff)

(*** reflexivity ***)

lemma cspF_reflex_eq_P[simp]: "P =F[M,M] P"
by (simp add: eqF_def)

lemma cspF_reflex_eq_STOP[simp]: "STOP =F[M1,M2] STOP"   
by (simp add: eqF_def semFf_def traces_iff failures_iff)

lemma cspF_reflex_eq_SKIP[simp]: "SKIP =F[M1,M2] SKIP"   
by (simp add: eqF_def semFf_def traces_iff failures_iff)

lemma cspF_reflex_eq_DIV[simp]: "DIV =F[M1,M2] DIV"   
by (simp add: eqF_def semFf_def traces_iff failures_iff)

lemmas cspF_reflex_eq = cspF_reflex_eq_P
                        cspF_reflex_eq_STOP
                        cspF_reflex_eq_SKIP
                        cspF_reflex_eq_DIV

lemma cspF_reflex_ref_P[simp]: "P <=F[M,M] P"
by (simp add: refF_def)

lemma cspF_reflex_ref_STOP[simp]: "STOP <=F[M1,M2] STOP"   
by (simp add: refF_def semFf_def traces_iff failures_iff)

lemma cspF_reflex_ref_SKIP[simp]: "SKIP <=F[M1,M2] SKIP"   
by (simp add: refF_def semFf_def traces_iff failures_iff)

lemma cspF_reflex_ref_DIV[simp]: "DIV <=F[M1,M2] DIV"   
by (simp add: refF_def semFf_def traces_iff failures_iff)

lemmas cspF_reflex_ref = cspF_reflex_ref_P
                         cspF_reflex_ref_STOP
                         cspF_reflex_ref_SKIP
                         cspF_reflex_ref_DIV

lemmas cspF_reflex = cspF_reflex_eq cspF_reflex_ref

(*** symmetry ***)

lemma cspF_sym: "P1 =F[M1,M2] P2 ==> P2 =F[M2,M1] P1"
by (simp add: eqF_def)

lemma cspF_symE:
  "[| P1 =F[M1,M2] P2 ; P2 =F[M2,M1] P1 ==> Z |] ==> Z"
by (simp add: eqF_def)

(*** transitivity ***)

lemma cspF_trans_left_eq: 
  "[| P1 =F[M1,M2] P2 ; P2 =F[M2,M3] P3 |] ==> P1 =F[M1,M3] P3"
by (simp add: eqF_def)

lemma cspF_trans_left_ref: 
  "[| P1 <=F[M1,M2] P2 ; P2 <=F[M2,M3] P3 |] ==> P1 <=F[M1,M3] P3"
by (simp add: refF_def)

lemmas cspF_trans_left = cspF_trans_left_eq cspF_trans_left_ref
lemmas cspF_trans = cspF_trans_left

lemma cspF_trans_right_eq: 
  "[| P2 =F[M2,M3] P3 ; P1 =F[M1,M2] P2 |] ==> P1 =F[M1,M3] P3"
by (simp add: eqF_def)

lemma cspF_trans_right_ref: 
  "[| P2 <=F[M2,M3] P3 ;  P1 <=F[M1,M2] P2 |] ==> P1 <=F[M1,M3] P3"
by (simp add: refF_def)

lemmas cspF_trans_rught = cspF_trans_right_eq cspF_trans_right_ref

(*** rewrite (eq) ***)

lemma cspF_rw_left_eq_MF:
  "[| P1 =F P2 ; P2 =F P3 |] ==> P1 =F P3"
by (simp add: eqF_def)

lemma cspF_rw_left_eq:
  "[| P1 =F[M1,M1] P2 ; P2 =F[M1,M3] P3 |] ==> P1 =F[M1,M3] P3"
by (simp add: eqF_def)

lemma cspF_rw_left_ref_MF:
  "[| P1 =F P2 ; P2 <=F P3 |] ==> P1 <=F P3"
by (simp add: refF_def eqF_def)

lemma cspF_rw_left_ref:
  "[| P1 =F[M1,M1] P2 ; P2 <=F[M1,M3] P3 |] ==> P1 <=F[M1,M3] P3"
by (simp add: refF_def eqF_def)

lemmas cspF_rw_left = 
   cspF_rw_left_eq_MF cspF_rw_left_ref_MF
   cspF_rw_left_eq cspF_rw_left_ref

lemma cspF_rw_right_eq:
  "[| P3 =F[M3,M3] P2 ; P1 =F[M1,M3] P2 |] ==> P1 =F[M1,M3] P3"
by (simp add: eqF_def)

lemma cspF_rw_right_eq_MF:
  "[| P3 =F P2 ; P1 =F P2 |] ==> P1 =F P3"
by (simp add: eqF_def)

lemma cspF_rw_right_ref:
  "[| P3 =F[M3,M3] P2 ; P1 <=F[M1,M3] P2 |] ==> P1 <=F[M1,M3] P3"
by (simp add: refF_def eqF_def)

lemma cspF_rw_right_ref_MF:
  "[| P3 =F P2 ; P1 <=F P2 |] ==> P1 <=F P3"
by (simp add: refF_def eqF_def)

lemmas cspF_rw_right =
   cspF_rw_right_eq_MF cspF_rw_right_ref_MF
   cspF_rw_right_eq cspF_rw_right_ref

(*** rewrite (ref) ***)

lemma cspF_tr_left_eq:
   "[| P1 =F[M1,M1] P2 ; P2 =F[M1,M3] P3 |] ==> P1 =F[M1,M3] P3"
by (simp add: eqF_def)

lemma cspF_tr_left_ref:
   "[| P1 <=F[M1,M1] P2 ; P2 <=F[M1,M3] P3 |] ==> P1 <=F[M1,M3] P3"
by (simp add: refF_def eqF_def)

lemmas cspF_tr_left = cspF_tr_left_eq cspF_tr_left_ref

lemma cspF_tr_right_eq:
   "[| P2 =F[M3,M3] P3 ; P1 =F[M1,M3] P2 |] ==> P1 =F[M1,M3] P3"
by (simp add: eqF_def)

lemma cspF_tr_right_ref:
  "[| P2 <=F[M3,M3] P3 ; P1 <=F[M1,M3] P2 |] ==> P1 <=F[M1,M3] P3"
by (simp add: refF_def eqF_def)

lemmas cspF_tr_right = cspF_tr_right_eq cspF_tr_right_ref


(*----------------------------------------*
 |   rewriting processes in assumptions   |
 *----------------------------------------*)

(*** rewrite (eq) ***)

lemma cspF_rw_left_eqE_MF:
  "[| P1 =F P3 ; P1 =F P2 ; [| P2 =F P3 |] ==> R |] ==> R"
apply (subgoal_tac "P2 =F P3")
apply (simp)
apply (rule cspF_rw_left)
apply (rule cspF_sym)
apply (simp)
apply (simp)
done

lemma cspF_rw_left_eqE:
  "[| P1 =F[M1,M3] P3 ; P1 =F[M1,M1] P2 ; 
      [| P2 =F[M1,M3] P3 |] ==> R |] ==> R"
apply (subgoal_tac "P2 =F[M1,M3] P3")
apply (simp)
apply (rule cspF_rw_left)
apply (rule cspF_sym)
apply (simp)
apply (simp)
done

lemma cspF_rw_left_refE_MF:
  "[| P1 <=F P3 ; P1 =F P2 ; [| P2 <=F P3 |] ==> R |] ==> R"
apply (subgoal_tac "P2 <=F P3")
apply (simp)
apply (rule cspF_rw_left)
apply (rule cspF_sym)
apply (simp)
apply (simp)
done

lemma cspF_rw_left_refE:
  "[| P1 <=F[M1,M3] P3 ; P1 =F[M1,M1] P2 ; 
      [| P2 <=F[M1,M3] P3 |] ==> R |] ==> R"
apply (subgoal_tac "P2 <=F[M1,M3] P3")
apply (simp)
apply (rule cspF_rw_left)
apply (rule cspF_sym)
apply (simp)
apply (simp)
done

lemmas cspF_rw_leftE = 
   cspF_rw_left_eqE_MF cspF_rw_left_refE_MF
   cspF_rw_left_eqE    cspF_rw_left_refE

(* right *)

lemma cspF_rw_right_eqE_MF:
  "[| P1 =F P3 ; P3 =F P2 ; [| P1 =F P2 |] ==> R |] ==> R"
apply (subgoal_tac "P1 =F P2")
apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_sym)
apply (simp)
apply (simp)
done

lemma cspF_rw_right_eqE:
  "[| P1 =F[M1,M3] P3 ; P3 =F[M3,M3] P2 ;
      [| P1 =F[M1,M3] P2 |] ==> R |] ==> R"
apply (subgoal_tac "P1 =F[M1,M3] P2")
apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_sym)
apply (simp)
apply (simp)
done

lemma cspF_rw_right_refE_MF:
  "[| P1 <=F P3 ; P3 =F P2 ; [| P1 <=F P2 |] ==> R |] ==> R"
apply (subgoal_tac "P1 <=F P2")
apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_sym)
apply (simp)
apply (simp)
done

lemma cspF_rw_right_refE:
  "[| P1 <=F[M1,M3] P3 ; P3 =F[M3,M3] P2 ;
      [| P1 <=F[M1,M3] P2 |] ==> R |] ==> R"
apply (subgoal_tac "P1 <=F[M1,M3] P2")
apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_sym)
apply (simp)
apply (simp)
done

lemmas cspF_rw_rightE = 
   cspF_rw_right_eqE_MF cspF_rw_right_refE_MF
   cspF_rw_right_eqE    cspF_rw_right_refE


(*-----------------------------------------*
 |                   noPN                  |
 *-----------------------------------------*)

lemma failures_noPN_Constant_lm_EC: 
  "[| ALL P:range Pf. (EX F. failures P = (%M. F)) |]
       ==> (EX F2. failures (? :X -> Pf) = (%M. F2))"
apply (auto simp add: failures_iff)
apply (simp add: choice_ALL_EX)
apply (erule exE)
apply (auto)
done

lemma failures_noPN_Constant_lm_RIC: 
  "[| ALL P:range Pf. (EX F. failures P = (%M. F)) |]
       ==> (EX F2. failures (!! :X .. Pf) = (%M. F2))"
apply (auto simp add: failures_iff)
apply (simp add: choice_ALL_EX)
apply (erule exE)
apply (auto)
done

lemma failures_noPN_Constant_lm:
  "noPN P --> (EX F. failures P = (%M. F))"
apply (induct_tac P)
apply (simp add: failures_iff, force)
apply (simp add: failures_iff, force)
apply (simp add: failures_iff, force)
apply (simp add: failures_iff, force)

(* Ext_pre_choice *)
 apply (intro impI)
 apply (simp add: failures_noPN_Constant_lm_EC)

(* Ext_choice *)
 apply (intro impI)
 apply (simp add: failures_iff)
 apply (elim exE)
 apply (simp add: failures_iff)
 apply (subgoal_tac "ALL P. noPN P --> (EX T. traces P = (%M. T))")
 apply (frule_tac x="x1" in spec)
 apply (drule_tac x="x2" in spec)
 apply (simp)
 apply (elim exE)
 apply (simp)
 apply (force)
 apply (simp add: traces_noPN_Constant)

apply (simp add: failures_iff, force)

(* Rep_int_choice_nat *)
 apply (intro impI)
 apply (simp add: failures_noPN_Constant_lm_RIC)

(* IF *)
 apply (simp add: failures_iff)
 apply (case_tac "x1")
 apply (simp)
 apply (simp)

apply (simp add: failures_iff, force)
apply (simp add: failures_iff, force)
apply (simp add: failures_iff, force)

(* Seq_comp *)
 apply (intro impI)
 apply (simp)
 apply (elim exE)
 apply (simp add: failures_iff)
 apply (subgoal_tac "ALL P. noPN P --> (EX T. traces P = (%M. T))")
 apply (drule_tac x="x1" in spec)
 apply (simp)
 apply (elim exE)
 apply (simp)
 apply (force)
 apply (simp add: traces_noPN_Constant)

apply (simp add: failures_iff, force)
apply (simp add: failures_iff)
done

lemma failures_noPN_Constant:
  "noPN P ==> (EX F. failures P = (%M. F))"
apply (simp add: failures_noPN_Constant_lm)
done

end
