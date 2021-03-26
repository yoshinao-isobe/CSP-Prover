           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2020         |
            |                  March 2021  (modified)   |
            |                                           |
            |        Joabe Jesus (eComp POLI UPE)       |
            |        Joabe Jesus (CIn UFPE)             |
            *-------------------------------------------*)

theory CSP_T_law_rep_interleaving
imports CSP_T_law_decompo CSP_T_law_basic
begin

subsection \<open> Inductive interleave \<close>

(*
lemma cspT_Interleave_Act_prefix_Alpha_Par :
    "a \<noteq> b \<Longrightarrow>
     (a -> SKIP ||| b -> SKIP)
     =T [||] [ (a -> SKIP, {a}), (b -> SKIP, {b}) ]"
  apply (cspT_auto)
  apply (rule cspT_rw_right, simp add: Alpha_parallel_def)

  apply (cspT_auto)
  apply (rule cspT_rw_right)
    apply (rule cspT_decompo, simp)
    apply (rule cspT_decompo, simp)
    apply (rule cspT_Parallel_term)
    apply (rule cspT_decompo, simp)
    apply (rule cspT_decompo, simp)
    apply (rule cspT_Parallel_term)
    apply (rule cspT_reflex)
  apply (rule cspT_rw_right)
    apply (rule cspT_decompo, simp)
    apply (rule cspT_reflex)
    apply (rule cspT_decompo, simp)
    apply (rule cspT_reflex)
    apply (rule cspT_reflex)
    apply (cspT_auto)
    apply (cspT_auto)
done
*)

(*
lemma cspT_Inductive_interleave_map_cong2 :
    "\<forall>a. PXf a = PXg a \<Longrightarrow> ( ||| map PXf x) =T ( ||| map PXg x)"
  apply (induct x)
  apply (simp add: Inductive_interleave_def)
  apply (simp (no_asm) add: map_unwind)
  apply (rule cspT_decompo, simp, clarsimp)
  apply (force)
done
*)

lemma cspT_Inductive_interleave_cong :
    "x = y \<Longrightarrow> ||| x =T ||| y"
by (simp)


lemma cspT_Inductive_interleaving_Cons_cong :
    "\<lbrakk> P =T Q; ||| Ps =T ||| Qs \<rbrakk> \<Longrightarrow> ||| (P#Ps) =T ||| (Q#Qs)"
by (simp, rule cspT_decompo, simp)

lemma cspT_Inductive_interleave_map_cong :
    "\<forall>a \<in> set x. PXf a =T PXg a \<Longrightarrow> ( ||| map PXf x) =T ( ||| map PXg x)"
  apply (induct x, simp_all)
by (rule cspT_decompo, simp_all)+

lemma cspT_Inductive_interleave_map_to_List :
    "map PXf x = l \<Longrightarrow> ( ||| map PXf x) =T ( ||| l)"
by (simp)

lemma cspT_Inductive_interleave_map_to_List_Cons :
    "l \<noteq> [] \<Longrightarrow> ||| map PXf l =T ||| ( (PXf (hd l)) # map PXf (tl l) )"
  apply (rule cspT_Inductive_interleave_map_to_List)

by (induct l, simp, simp add: map_def)


lemma cspT_Subst_procfun_Inductive_interleave_map :
   "\<forall> i \<in> set l. (PXf i) << Pf =T PXf i
    \<Longrightarrow> ( ||| map PXf l) << Pf =T ( ||| map PXf l)"
  apply (induct l, simp_all)
by (rule cspT_decompo, simp_all)+


subsection \<open> Replicated interleaving \<close>

lemma cspT_Rep_interleaving_to_Inductive_interleave :
    "finite X \<Longrightarrow> l = (SOME y. y isListOf X)
     \<Longrightarrow> ||| x:X .. PXf x =T[M,M] ||| (map PXf l)"
by (simp add: Rep_interleaving_def)


lemma cspT_Rep_interleaving_cong :
    "X = Y \<Longrightarrow> ||| x:X .. PfX =T ||| y:Y .. PfX"
by (simp)

lemma cspT_Rep_interleaving_pair_cong :
    "X = Y \<Longrightarrow> ||| (a,b):X .. PfX =T ||| (c,d):Y .. PfX"
by (simp)



(*
TODO

lemma Rep_interleaving2Alpha_parallel :
    "\<lbrakk> finite X; \<exists> i . i : X; Y = X-{i}; alphabet(Pf i) \<inter> alphabet( |||Y .. Pf ) = {} \<rbrakk> \<Longrightarrow>
     |||X .. Pf =T (Pf i |[- X]| SKIP) |[{}]| ( |||Y .. Pf |[- Y]| SKIP)"
  apply (case_tac "X={}")
  apply (simp)
  
  apply (rule cspT_rw_left)
  apply (simp add: Rep_interleaving_def)
  apply (rule cspT_InductPar_map_unwind)
  apply (rule someI2_ex)
  apply (rule isListOf_EX, simp)
  apply (rule isListOf_nonemptyset, simp, simp)
  apply (cspT_auto)
  
  apply (rule cspT_rw_right)
  apply (rule cspT_decompo, simp)
  apply (rule cspT_SKIP_DIV)
apply (simp add: Rep_interleaving_def)
apply (cspT_auto)
*)




(*
   Inductive_parallel : "[||] (PX # PXs) = (fst PX) |[snd PX, Union (snd ` set PXs)]| ([||] PXs)"
   
   Alpha_parallel_def : "P |[X,Y]| Q  == (P |[- X]| SKIP) |[X Int Y]| (Q |[- Y]| SKIP)"
   
   "traces(P |[X]| Q) = (%M. {u. EX s t. u : s |[X]|tr t
                                       & s :t traces(P) M
                                       & t :t traces(Q) M }t)"
                                  
   par_tr_def : "s |[X]|tr t == {u. (u, s, t) : parx X}"
   
   parx_nil_nil:   "(<>, <>, <>) : parx X" |
   parx_Tick_Tick: "(<Tick>, <Tick>, <Tick>) : parx X" |
   parx_Ev_nil:    "[| (u,  s, <>) : parx X ; a ~: X |] ==> (<Ev a> ^^^ u, <Ev a> ^^^ s, <>) : parx X" |
   parx_nil_Ev:    "[| (u, <>,  t) : parx X ; a ~: X |] ==> (<Ev a> ^^^ u, <>, <Ev a> ^^^ t) : parx X" |
   parx_Ev_sync:   "[| (u,  s,  t) : parx X ;  a : X |] ==> (<Ev a> ^^^ u, <Ev a> ^^^ s, <Ev a> ^^^ t) : parx X" |
   parx_Ev_left:   "[| (u,  s,  t) : parx X ; a ~: X |] ==> (<Ev a> ^^^ u, <Ev a> ^^^ s, t) : parx X" |
   parx_Ev_right:  "[| (u,  s,  t) : parx X ; a ~: X |] ==> (<Ev a> ^^^ u, s, <Ev a> ^^^ t) : parx X"
 *)


(*
(let x = (SOME x . x : X); X2 = X-{x} in (PXf x) ||| ( |||X2 .. PXf ) )

lemma Rep_interleaving_unwind :
    "\<lbrakk> finite X; \<exists> i . i : X; X2 = X-{i}; alphabet(Pf i) \<inter> alphabet( |||X2 .. Pf ) = {} \<rbrakk> \<Longrightarrow>
     |||X .. Pf =T (Pf i) ||| ( |||X2 .. Pf )"
  apply (case_tac "X={}")
  apply (cspT_auto)
  apply (rule cspT_rw_left)
  apply (simp add: Rep_interleaving_def)
  apply (rule cspT_InductPar_map_unwind)
  apply (rule someI2_ex, rule isListOf_EX, simp)
  apply (rule isListOf_nonemptyset, simp, simp)
*)

end