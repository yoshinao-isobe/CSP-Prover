           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                 August 2004               |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009-2       |
            |                October 2010  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CPO_set
imports CPO_prod
begin

(*****************************************************************

         1. Bool is CPO  for (Isabelle 2011)
         2. Sets are CPO.
         3. 
         4. 

 *****************************************************************)

(********************************************************** 
              def: bot in bool
 **********************************************************)


declare le_bool_def [simp del] (* for Isabelle 2011 *)

(*
instance bool :: bot0
apply (intro_classes)
done
*)

instantiation "set" :: (type) bot0
begin

definition
  set_Bot_def : "Bot == {}"
  instance ..
end



(*
for Isabelle 2011

instantiation bool :: bot0
begin

definition
  bool_Bot_def : "Bot == False"
  instance ..
end
*)

(* isabelle 2009-1
defs (overloaded)
  bool_Bot_def : "Bot == False"
*)

(*
     For Isabelle 2007

instance "set" :: (type) bot0
apply (intro_classes)
done

defs (overloaded)
  set_Bot_def : "Bot == {}"
*)

(************************************************************
                   Bool bot ==> bot  (Isabelle 2011)
 ************************************************************)

(*
for Isabelle 2011

lemma bool_Bot:
  "ALL (X::(bool)). Bot <= X"
apply (simp add: bool_Bot_def)
apply (simp add: le_bool_def)
done
*)

(*
lemma set_Bot:
  "ALL (X::('a set)). Bot <= X"
apply (simp add: set_Bot_def)
done
*)

(*****************************
       bool bot => bot
 *****************************)

(*
Isabelle 2011

instance bool :: bot
apply (intro_classes)
apply (simp only: bool_Bot)
done

*)

(************************************************************
                   Set bot ==> bot

                    Isabelle 2011
 ************************************************************)

(*** set Bot ***)
(*
lemma set_Bot:
  "ALL (X::('a set)). Bot <= X"
apply (simp add: set_Bot_def)
(* apply (simp add: prod_Bot)   Isabelle 2011 *)
done
*)

(************************************************************
                      Bool : CPO  Isabelle 2011
 ************************************************************)

(*
(* modified when Isabelle 2011 => Isabelle 2012 *)

(*** bool directed decompo ***)

lemma bool_cpo_lm:
  "directed (Bs::(bool) set) ==> Bs hasLUB"
apply (simp add: hasLUB_def)
apply (rule_tac x="(EX b:Bs. b)" in exI)
apply (simp add: isLUB_def isUB_def)
apply (simp add: le_bool_def)
by (auto)


(*****************************
          Bool : CPO
 *****************************)

instance bool :: cpo
apply (intro_classes)
by (simp add: bool_cpo_lm)
*)

(************************************************************
                      Bool : CPO_BOT
 ************************************************************)

(*
Isabelle 2011

instance bool :: cpo_bot
by (intro_classes)
*)

(************************************************************
                      Set : CPO
 ************************************************************)


lemma set_cpo_lm:
  "directed (Xs::('a set) set) ==> Xs hasLUB"
apply (simp add: hasLUB_def)
apply (rule_tac x="Union Xs" in exI)
apply (simp add: isLUB_def isUB_def)
by (auto)

(*****************************
          Set : CPO
 *****************************)

instance set :: (type) cpo
apply (intro_classes)
by (simp add: set_cpo_lm)

(************************************************************
                      Set : CPO_BOT
 ************************************************************)

instance set :: (type) cpo_bot
apply (intro_classes)
apply (simp add: set_Bot_def)
done

(* ============================================================== *) 
(* for isabelle 2011

lemma set_cpo:
  "directed (Xs::('a set) set) ==> Xs hasLUB"
by (simp add: complete_cpo)

(* because (bool::cpo) and ("fun" :: (type,cpo) cpo) *)

(************************************************************
                      Set : CPO_bot
 ************************************************************)

lemma set_bot:
  "Bot <= (x::'a set)"

by (simp add: bottom_bot)

(* because (bool::bot) and ("fun" :: (type,bot) bot) *)

(* -------------------------------------------------------- *)
*)

declare le_bool_def [simp] (* for Isabelle 2011 *)

end

