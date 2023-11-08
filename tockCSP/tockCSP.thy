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

theory tockCSP
imports tockCSP_TOCKS
        tockCSP_RUNT
begin



(* TODO: definition of tockCSP specific syntax (@see tick-tock-CSP) *)

(* https://github.com/robo-star/tick-tock-CSP/ *)


(*

 P ;; Q \<leadsto> P ;; Q
 P \ X \<leadsto> P \ X
 P [ f ] \<leadsto> P [[ f ]]

 STOP \<leadsto> STOP\<^sub>T = TOCKS = RUN({tock})
 STOP\<^sub>U \<leadsto> STOP
 Wait n \<leadsto> Wait n
 Timed event prefix \<leadsto> e -t\<rightarrow> P
 P |~| Q \<leadsto> P |~t| Q
 P [+] Q \<leadsto> P [t] Q
 P /> Q \<leadsto> P /t> Q (* Time-synchronising timeout  *)
 P />d Q \<leadsto> P /t>d Q (* Strict timed timeout *)
 P [| A |] Q \<leadsto> P |[ A @t ]| Q

*)


end