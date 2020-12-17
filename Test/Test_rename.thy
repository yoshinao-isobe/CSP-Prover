           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2009-1       |
            |              January 2010                 |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Test_rename
imports CSP_F
begin

datatype Event = a1 | a2 | a3 | aa

definition
  RenList :: " (Event * Event) set list"
  where
  RenList_def :
  "RenList == [a1 <-- aa, a2 <-- aa, a3 <-- aa]"

(* automatic proof *)

(* note: [[ ]]* is used } *)

lemma "(a1 -> a2 -> a3 -> STOP)[[RenList]]* =F
       (aa -> aa -> aa-> STOP)"
apply (simp add: RenList_def)
apply (cspF_auto | auto)+
done

(* step by step proof *)

lemma "(a1 -> a2 -> a3 -> STOP)[[RenList]]* =F 
       (aa -> aa -> aa-> STOP)"
apply (simp add: RenList_def)

(* a1 *)

apply (cspF_auto)+
apply (auto)

(* a2 *)

apply (cspF_auto)+
apply (auto)

(* a3 *)

apply (cspF_auto)+
apply (auto)

(* STOP *)

apply (cspF_auto)+
done


(* the other renaming technique *)

definition
  Ren :: " (Event * Event) set"
  where
  Ren_def :
  "Ren == ({a1,a2,a3} <<- aa)"

(* automatic proof *)

(* note: [[ ]] is used } *)

lemma "(a1 -> a2 -> a3 -> STOP)[[Ren]] =F 
       (aa -> aa -> aa-> STOP)"
apply (simp add: Ren_def)
apply (cspF_auto | auto)+
done

end
