theory TSF_TimeStop
imports TSF_Infra
begin


subsection \<open> TimeStopFree \<close>

definition
  TimeStopFree :: "'e event set => ('p,'e::tockCSP) proc => bool"
                  ("(0[_]-TimeStopFree _)" [0,55] 55)
  where
  TimeStopFree_def :
    "[X]-TimeStopFree P == [X \<union> {Tick,Tock}]-DeadlockFree (P -- Nontock)"
(*
    P -- Nontock   means the PROCESS controlling TIME PASSING
                   OBS: TIME PASSING produces Tock events AND allows Tick
*)


abbreviation
  isTimeStopFree  :: "('p,'e::tockCSP) proc => bool" 
                         ("_ isTimeStopFree" [1000] 1000)
where
  "P isTimeStopFree == [EvsetTick]-TimeStopFree (P)"

(*
    EvsetTick      means all events (including Tock and Tick) are REFUSED
*)
lemmas isTimeStopFree_def = TimeStopFree_def
                            insert_EvsetTick


end