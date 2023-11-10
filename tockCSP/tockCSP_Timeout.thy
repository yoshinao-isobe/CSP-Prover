           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 2022 / 2023               |
            |                                           |
            |          Lemmas and Theorems from         |
            |    Jesus and Sampaio's SBMF 2022 paper    |
            |                     and                   |
            |    Jesus and Sampaio's SCP 2023 paper     |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory tockCSP_Timeout
imports tockCSP_tock
begin


subsection \<open> Timeout from Roscoe's book The Theory and Practice of Concurrency \<close>


class timeoutCSP = tockCSP +
  fixes setuptoc :: "nat \<Rightarrow> 'a"
    and resettoc :: "'a"
    and timesout :: "'a"

  assumes setuptoc_cong : "setuptoc t = setuptoc t2 \<longleftrightarrow> (t = t2)"
      and setup_neq_reset : "\<forall>t. setuptoc t \<noteq> resettoc"
      and setup_neq_timesout : "\<forall>t. setuptoc t \<noteq> timesout"
      and reset_neq_timesout : "timesout \<noteq> resettoc"

      and setup_neq_tock : "\<forall>t. setuptoc t \<noteq> tock"
      and reset_neq_tock : "resettoc \<noteq> tock"
      and timesout_neq_tock : "timesout \<noteq> tock"
begin

declare setup_neq_reset [simp add]
declare setup_neq_timesout [simp add]
declare reset_neq_timesout [simp add]
declare setup_neq_tock [simp add]
declare reset_neq_tock [simp add]
declare timesout_neq_tock [simp add]

lemma setup_neq_reset_sym [simp]: "\<forall>t. resettoc \<noteq> setuptoc t"
  by (simp add: not_sym)

lemma setup_neq_timesout_sym [simp]: "\<forall>t. timesout \<noteq> setuptoc t"
  by (simp add: not_sym)

lemma inj_setuptoc [simp]: "inj setuptoc"
  by (simp add: inj_def setuptoc_cong)

end




datatype TimeoutPN = TOC
                   | Armed nat

fun TimeoutPNfun
where
  "TimeoutPNfun(TOC) = setuptoc ? n \<rightarrow> $(Armed n)
                       [+] tock \<rightarrow> $TOC
                       [+] resettoc \<rightarrow> $TOC"
 | "TimeoutPNfun(Armed n) = (IF (n = 0) THEN (timesout \<rightarrow> $TOC)
                                        ELSE (tock \<rightarrow> $(Armed (n - 1))))
                            [+] resettoc \<rightarrow> $TOC"


end