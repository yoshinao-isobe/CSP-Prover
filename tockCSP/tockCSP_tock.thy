theory tockCSP_tock
imports tockCSP_Infra
begin





subsection \<open> tockCSP = tock Event class \<close>

class tockCSP =
  fixes tock :: "'a"

  assumes nonempty_Nontock [simp]: "- { tock } \<noteq> {}"
begin

abbreviation Nontock :: "'a set"
where "Nontock == - { tock }"


subsubsection \<open> tockCSP lemmas \<close>

lemma in_Nontock_iff :
    "x \<in> Nontock \<longleftrightarrow> x \<noteq> tock"
  by (simp)


lemma tockCSP_UNIV [simp]:
    "insert tock Nontock = UNIV"
  by (auto simp add: in_Nontock_iff)


lemma ex_neq_tock : "\<exists>x. x \<noteq> tock"
  apply (simp only: in_Nontock_iff[THEN sym])
  apply (simp only: ex_in_conv)
  by (simp)


lemma not_UNIV_subset_tock [simp]:
    "\<not> UNIV \<subseteq> {tock}"
  apply (auto simp add: subset_eq)
  by (rule ex_neq_tock)




subsection \<open> Tock == "Ev tock", NonTockEv and NonTickTockEv \<close>

abbreviation Tock :: "'a event"
where
  "Tock == Ev tock"

abbreviation NonTickTockEv :: "'a event set"
where
  "NonTickTockEv == Ev ` Nontock"

abbreviation NonTockEv :: "'a event set"
where
  "NonTockEv == insert Tick NonTickTockEv"


abbreviation tocks_rel ("_ =tocks'(_')" [85,85] 84)
where
    "t =tocks(s) == (s --tr Nontock = t)"


abbreviation tocks_nonrel ("_ \<noteq>tocks'(_')" [85,85] 84)
where
    "t \<noteq>tocks(s) == (s --tr Nontock ~= t)"


abbreviation nontocks_rel ("_ =nontocks'(_')" [85,85] 84)
where
    "t =nontocks(s) == (s --tr {tock} = t)"


abbreviation nontocks_nonrel ("_ \<noteq>nontocks'(_')" [85,85] 84)
where
    "t \<noteq>nontocks(s) == (s --tr {tock} ~= t)"



subsubsection \<open> Tock lemmas \<close>

lemma Tock_in_Evset [simp]:
    "Tock \<in> Evset"
  by (simp add: Evset_def image_def)


lemma insert_Tock_Evset [simp]:
    "insert Tock Evset = Evset"
  by (auto)

lemma insert_Tock_EvsetTick [simp]:
    "insert Tock EvsetTick = EvsetTick"
  by (auto)


lemma insert_Tick_Tock :
    "insert Tick (insert Tock Y) = Y \<union> {Tick,Tock}"
  by (auto)

lemma noTick_if_sett_Tock :
    "sett s \<subseteq> {Tock} \<Longrightarrow> noTick s"
  by (auto simp add: noTick_def)



lemma sett_subset_TickTock_if:
    "(u = <> | u = <Tick> | (\<exists> a s. u = <Ev a> ^^^ s & sett (<Ev a> ^^^ s) \<subseteq> {Tick, Tock})) ==>
    (sett u <= {Tick,Tock})"
  by (auto)

lemma sett_subset_TickTock_only_if:
    "(sett u <= {Tick,Tock}) --> (u = <> | u = <Tick> | (\<exists> a s. u = <Ev a> ^^^ s & sett (<Ev a> ^^^ s) \<subseteq> {Tick, Tock}))"
  apply (induct_tac u rule: induct_trace)
  by (simp_all)

lemma sett_subset_TickTock:
    "(sett u <= {Tick,Tock}) = (u = <> | u = <Tick> | (\<exists> a s. u = <Ev a> ^^^ s & sett (<Ev a> ^^^ s) \<subseteq> {Tick, Tock}))"
  apply (rule iffI)
  apply (simp only: sett_subset_TickTock_only_if)
  apply (simp only: sett_subset_TickTock_if)
  done



subsubsection \<open> NonTickTockEv lemmas \<close>

lemma in_NonTickTockEv_iff [simp]: "x \<in> NonTickTockEv \<longleftrightarrow> x \<noteq> Tick \<and> x \<noteq> Tock"
  apply (simp add: image_def)
  by (case_tac x, simp_all)


lemma NonTickTockEv_simp :
    "NonTickTockEv = Evset - {Tock}"
  by (auto simp add: Evset_def)


lemma NonTickTockEv_neq_Evset [simp]:
    "NonTickTockEv \<noteq> Evset"
  by (auto simp add: Evset_def image_def)


lemma Tick_notin_NonTickTockEv [simp]:
    "Tick \<notin> NonTickTockEv"
  by (rule Tick_notin_Ev_image)


lemma Tock_notin_NonTickTockEv [simp]:
    "Tock \<notin> NonTickTockEv"
  by (simp add: image_def)



lemma Tock_notin_if_subset_NonTickTockEv :
    "X \<subseteq> NonTickTockEv \<Longrightarrow> Tock \<notin> X"
  by (auto simp add: subset_eq)


lemma NonTickTockEv_Un_eq_Evset_Un_if :
    "Tock \<in> X \<Longrightarrow> NonTickTockEv \<union> X = Evset \<union> X"
  by (auto simp add: Evset_def)


lemma NonTickTockEv_Un_Evset_absorb [simp]:
    "NonTickTockEv \<union> Evset = Evset"
  by (rule Un_Evset)


lemma NonTickTockEv_Tick_Tock :
    "NonTickTockEv \<union> {Tick, Tock} = EvsetTick"
  by (auto)


lemma NonTickTockEv_subset_Evset [simp]:
    "NonTickTockEv \<subseteq> Evset"
  by (auto simp add: Evset_def)


lemma NonTickTockEv_subset_EvsetTick [simp]:
    "NonTickTockEv \<subseteq> EvsetTick"
  by (auto simp add: EvsetTick_def)


lemma insert_Tock_NonTickTockEv [simp]:
    "insert Tock NonTickTockEv = Evset"
  by (auto simp add: NonTickTockEv_simp)

lemma insert_Tock_NonTickTockEv_Un [simp]:
    "insert Tock (NonTickTockEv \<union> X) = Evset \<union> X"
  by (auto simp add: NonTickTockEv_simp)



lemma Compl_NonTickTockEv [simp]:
    "- NonTickTockEv = {Tick,Tock}"
  by (auto)




subsubsection \<open> NonTockEv lemmas \<close>


lemma in_NonTockEv_iff [simp]: "x \<in> NonTockEv \<longleftrightarrow> x \<noteq> Tock"
  apply (simp add: image_def)
  by (case_tac x, simp_all)


lemma NonTockEv_simp :
    "NonTockEv = EvsetTick - {Tock}"
  apply (simp only: EvsetTick_def Compl_eq_Diff_UNIV)
  apply (auto simp add: image_def)
  by (case_tac x, auto)


lemma NonTockEv_neq_Evset [simp]:
    "NonTockEv \<noteq> Evset"
  by (auto simp add: Evset_def image_def)



lemma Tick_in_NonTockEv [simp]:
    "Tick \<in> NonTockEv"
  by (rule insertI1)


lemma Tock_notin_NonTockEv [simp]:
    "Tock \<notin> NonTockEv"
  by (simp add: image_def)



lemma Tock_notin_if_subset_NonTockEv :
    "X \<subseteq> NonTockEv \<Longrightarrow> Tock \<notin> X"
  by (auto simp add: subset_eq)



lemma NonTickTockEv_Un_eq_NonTockEv_Un_if :
    "Tick \<in> X \<Longrightarrow> NonTickTockEv \<union> X = NonTockEv \<union> X"
  by (auto simp add: Evset_def)

lemma insert_Tick_NonTickTockEv_Un :
    "insert Tick (NonTickTockEv \<union> X) = NonTockEv \<union> X"
  by (auto simp add: NonTickTockEv_simp)



lemma NonTockEv_Un_eq_EvsetTick_if :
    "Tock \<in> X \<Longrightarrow> NonTockEv \<union> X = EvsetTick"
  by (auto simp only: NonTockEv_simp EvsetTick_def)

lemma NonTockEv_Un_Evset_eq_EvsetTick [simp]:
    "NonTockEv \<union> Evset = EvsetTick"
  by (rule NonTockEv_Un_eq_EvsetTick_if, simp)

lemma insert_Tock_NonTockEv [simp]:
    "insert Tock NonTockEv = EvsetTick"
  apply (simp only: NonTockEv_simp EvsetTick_def)
  by (simp add: insert_UNIV)

lemma insert_Tick_NonTockEv_absorb [simp]:
    "insert Tick NonTockEv = NonTockEv"
  by (simp add: insert_absorb)





lemma cases_NonTickTockEv_Un_X :
    "NonTickTockEv \<union> X = Y \<longrightarrow> Y = NonTickTockEv \<or> Y = NonTockEv \<or> Y = Evset \<or> Y = EvsetTick"
  apply (rule)
  apply (drule sym, simp)
  apply (case_tac "X \<subseteq> NonTickTockEv")
  apply (simp)
  apply (simp add: Un_absorb2)
  apply (simp add: subset_eq)
  apply (case_tac "Tick : X")
  apply (simp only: NonTickTockEv_Un_eq_NonTockEv_Un_if)
  apply (case_tac "Tock : X")
  apply (simp only: NonTockEv_Un_eq_EvsetTick_if, clarify)
  apply (simp add: NonTickTockEv_simp Evset_def, force)
  apply (case_tac "Tock : X")
  apply (simp only: NonTickTockEv_Un_eq_Evset_Un_if, clarify)
  apply (simp add: NonTickTockEv_simp Evset_def, force)
  apply (simp add: NonTickTockEv_simp Evset_def, force)
  done


end





end
