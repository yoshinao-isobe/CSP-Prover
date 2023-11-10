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

theory TSF_TimeStop
imports TSF_Infra
begin


subsection \<open> TimeStopFree \<close>

definition
  TimeStopFree :: "'e event set => ('p,'e::tockCSP) proc => bool"
                  ("(0[_]-TimeStopFree _)" [0,55] 55)
  where
  TimeStopFree_def :
    "[X]-TimeStopFree P == [X Un {Tock}]-DeadlockFree (P -- Nontock)"
(* P -- Nontock   means the PROCESS controlling TIME PASSING
                  OBS: TIME PASSING produces Tock events AND allows Tick *)

(*** Timing-only time-stop-free (allows termination) ***)

abbreviation
  isTimeStopFree  :: "('p,'e::tockCSP) proc => bool" 
                         ("_ isTimeStopFree" [1000] 1000)
where
  "P isTimeStopFree == [{Tick}]-TimeStopFree (P)" 
                 (* == [{Tick} Un {Tock}]-DeadlockFree (P -- Nontock) *)

(* Tick is necessary to specify that the initial execution trace (nilt <>)
        can refuse Tock but can not refuse both Tock and Tick. This is important
        to prove SKIP isTimeStopFree. *)




subsection \<open> NonTickTimeStopFree \<close>

(*** General alphabet time-stop-free (non-terminating) ***)

definition NonTickTimeStopFree :: "'e event set => ('p,'e::tockCSP) proc => bool" 
           ("(0[_]-NonTickTimeStopFree _)" [0,55] 55)
where
  "[X]-NonTickTimeStopFree P == [X Un {Tick,Tock}]-NonTickDeadlockFree (P -- Nontock)"


(*** Timing-only time-stop-free (non-terminating) ***)

abbreviation "isNonTickTimeStopFree"  :: "('p,'e::tockCSP) proc => bool" 
       ("_ isNonTickTimeStopFree" [1000] 1000)
where
    "P isNonTickTimeStopFree == [{}]-NonTickTimeStopFree P"

end