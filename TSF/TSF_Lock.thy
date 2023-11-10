theory TSF_Lock
imports TSF_law
begin


subsection \<open> LockFree \<close>

definition
  LockFree :: "'e event set => ('p,'e::tockCSP) proc => bool"
                  ("(0[_]-LockFree _)" [0,55] 55)
  where
  LockFree_def :
    "[X]-LockFree P ==
        [X]-TimeStopFree P & [X - {Tock}]-DeadlockFree (P -- {tock})"
(*
    P -- {tock}   means the untimed PROCESS
*)


abbreviation
  isLockFree  :: "('p,'e::tockCSP) proc => bool" 
                         ("_ isLockFree" [1000] 1000)
where
  "P isLockFree == [EvsetTick]-LockFree P"
(*
    EvsetTick      means all events (including Tock and Tick) are REFUSED
*)

lemmas isLockFree_def = LockFree_def
                        insert_EvsetTick





end