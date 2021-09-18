           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021               |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_law_DFkev
imports DFP_DFkev DFP_law_DFnonTick
begin



lemma cspF_DFkev_0_i_eqF_DIV : "$DFkev 0 i =F DIV"
  by (cspF_auto)

lemma cspF_DFkev_k_0_eqF_DIV : "$DFkev k 0 =F DIV"
  by (cspF_auto, induct k, simp_all)

lemma cspF_DFkev_k_less_i_eqF_DIV : "i > k \<Longrightarrow> $DFkev k i =F DIV"
  apply (cspF_auto, induct k, simp)
  by (induct i, simp_all)

lemma cspF_DFkev_k_i_unwind : "k \<ge> i \<Longrightarrow> i > 1 \<Longrightarrow> $DFkev k i =F ! x -> $DFkev k (i-1)"
  apply (cspF_auto_left, induct k)
   apply (simp)
   apply (case_tac i)
   by (simp_all)

lemma cspF_DFkev_k_1_restarts : "k > 0 \<Longrightarrow> $DFkev k (Suc 0) =F ! x -> $DFkev k k"
  by (cspF_auto_left, induct k, simp_all)

lemmas cspF_DFkev_DIV = cspF_DFkev_0_i_eqF_DIV
                        cspF_DFkev_k_0_eqF_DIV
                        cspF_DFkev_k_less_i_eqF_DIV

lemmas cspF_DFkev_unwind = cspF_DFkev_k_1_restarts
                           cspF_DFkev_k_i_unwind
                           cspF_DFkev_DIV
                           
lemma DFkev_0_0_unwind : "$DFkev 0 0 =F DIV"
  by (rule cspF_DFkev_unwind)

lemma DFkev_1_1_unwind : "$DFkev (Suc 0) (Suc 0) =F ! x -> $DFkev (Suc 0) (Suc 0)"
  by (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)

lemma DFkev_2_2_unwind : "$DFkev 2 2 =F ! x -> ! x -> $DFkev 2 2"
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  by (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)

lemma DFkev_3_3_unwind : "$DFkev 3 3 =F ! x -> ! x -> ! x -> $DFkev 3 3"
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  by (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)

lemma DFkev_4_4_unwind : "$DFkev 4 4 =F ! x -> ! x -> ! x -> ! x -> $DFkev 4 4"
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  by (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)

lemma DFkev_5_5_unwind : "$DFkev 5 5 =F ! x -> ! x -> ! x -> ! x -> ! x -> $DFkev 5 5"
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  by (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)







(* TEST... *)
lemma test_DFkev_5_5_eqF_DFkev_4_4 : "$DFkev 5 5 =F $DFkev 4 4"
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all) (* 4 restarts *)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all) (* 5 restarts *)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all) (* 4 restarts *)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all) (* 5 restarts *)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all) (* 4 restarts *)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all) (* 5 restarts *)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all) (* 4 restarts *)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (rule cspF_rw_left, rule cspF_DFkev_unwind, simp_all) (* 5 restarts *)
  apply (rule cspF_rw_right, rule cspF_DFkev_unwind, simp_all) (* 4 restarts *)
  apply (cspF_step, rule cspF_decompo, simp)+

  (* SORRY - THIS IS ONLY A TEST! *)
  oops

end