theory tockCSP_Proof_Rule1
imports tockCSP_FD
begin


subsection \<open> tockCSP to untimed CSP \<close>


text \<open> "Setting D equal to \<Sigma> - {tock} would correspond to all normal events being
       arbitrarily delayable by the environment – the conventional CSP view
       of communication." (Roscoe, pag.393) \<close>
(*  P =F ((? x:X \<rightarrow> Pfx)::('e ChaosName,'e::tockCSP) proc) \<Longrightarrow>
    {tock} \<subseteq> X \<Longrightarrow>*)


(*lemma cspF_Parallel_Chaos_absorb :
    "P |[X]| $Chaos X =F P |~| STOP"
  apply (cspF_auto, simp add: guardedfun_def, rule cspF_reflex)
    apply (cspF_auto_left)+
    apply (case_tac "X = {}")
      apply (simp, cspF_simp)
      apply (cspF_auto)
defer
      apply (cspF_simp)
      apply (cspF_auto)
*)

declare [[show_consts]]
lemma Rule_untimed_CSP_Roscoe :
    "FPmode \<noteq> CPOmode \<Longrightarrow> tock \<notin> X \<Longrightarrow> X \<noteq> {} \<Longrightarrow>
    P =F ? x:X \<rightarrow> Pfx x \<Longrightarrow>
    \<forall>x\<in>X. $TOCKSTick <=F ((Pfx x -- (UNIV - {tock}))::('e ChaosName,'e::tockCSP) proc) \<Longrightarrow>
    $TOCKSTick <=F (P |[ UNIV - {tock} ]| (($(Chaos (UNIV - {tock})))::('e ChaosName,'e::tockCSP) proc)) -- (UNIV - {tock})"
(*
  apply (case_tac "X = {}")

  (* X = {} . Thus, P = STOP *)
  apply (cspF_auto_right)+
  apply (simp add: guardedfun_def)
  apply (rule cspF_reflex)
  apply (rule cspF_reflex)
  apply (cspF_auto_right)+

  apply (rule cspF_Int_choice_right)
defer
  apply (rule cspF_DIV_top)
defer
*)

  (* X \<noteq> {} *)
  apply (rule Rule_check_timestops_Roscoe_TOCKSTick, simp_all)

  apply (simp only: Compl_eq_Diff_UNIV[THEN sym])

  apply (cspF_unwind_left, simp add: guardedfun_def)
  apply (cspF_step_left)
  apply (cspF_dist_left)

  apply (rule cspF_rw_left, rule cspF_Int_choice_to_Rep)

  apply (rule cspF_ref_eq)

  apply (rule cspF_Rep_int_choice_left)
  apply (rule_tac x=1 in exI, simp)
  apply (cspF_simp_left)
  apply (cspF_step_left)
  apply (cspF_step_left)
defer
  apply (rule cspF_Rep_int_choice_right, simp, elim disjE)
  apply (simp)
  apply (cspF_simp_right)
  apply (cspF_auto_right)
  apply (cspF_auto_right)
  apply (rule cspF_Rep_int_choice_right, simp)
defer
  apply (cspF_simp_right)
  apply (cspF_auto_right)
  apply (cspF_auto_right)

  oops




lemma Rule_Roscoe_untimed_CSP_pag393 :
    "{tock} \<subseteq> X \<Longrightarrow>
    D = UNIV - {tock} \<Longrightarrow>
    $TOCKS <=F (P |[ D ]| CHAOS D) -- (UNIV - {tock})"
  apply (simp add: CHAOS_def)
  oops











(*
fun TOCKS_to_well_timedness
where
    "TOCKS_to_well_timedness P D (TOCKS) = (P |[ D ]| $(Chaos D)) -- (UNIV - {tock})"


PROVED IN tockCSP.thy with additional assumptions

lemma cspF_Rule_delayed_Roscoe_pag393 :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    $TOCKS <=F (P |[ D ]| $(Chaos D)) -- (UNIV - {tock})"

  apply (rule cspF_fp_induct_ref_left[of _ "TOCKS_to_well_timedness P D"])
  apply (simp_all)
  apply (simp)
  apply (case_tac p, simp)

  apply (simp only: Compl_eq_Diff_UNIV[THEN sym])
  apply (rule cspF_rw_right, rule cspF_decompo, simp)
    apply (rule cspF_decompo, simp)
    apply (rule cspF_reflex)
    apply (rule cspF_unwind, simp)
    apply (simp add: guardedfun_def)
    apply (simp (no_asm_simp))

  apply (cspF_step_right)
  apply (cspF_dist_right)+
  apply (rule cspF_Int_choice_right)
  apply (case_tac "D={}")
  apply (simp)
    apply (cspF_simp)
    apply (cspF_auto)
defer
    apply (cspF_simp)
    apply (cspF_auto)+
    apply (rule cspF_Rep_int_choice_right)
*)


(* not infinitely many events between two tock events
   From Roscoe TPC page 392 *)
lemma Rule_notInfiniteBetweenTock_Roscoe :
    "isDivergenceFree (P -- (UNIV - {tock}))"
  oops (* needs failures-divergences FD model to check divergece free*)


(* From Roscoe TPC page 393 *)
lemma Rule_well_timedness_Roscoe :
    "refFDfix ($TOCKS) ((P |[ D ]| $(Chaos D)) -- (UNIV - {tock}))"
  oops (* needs failures-divergences FD model to check divergece free*)


end