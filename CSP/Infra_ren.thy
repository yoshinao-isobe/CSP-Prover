           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                October 2009  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                  April 2011  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                  April 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory Infra_ren
imports Infra_HOL
        Infra_fun
begin

(* -------------------------- *
      renaming (Intra_ren)
 * -------------------------- *)

(*
consts
  fun_to_rel :: "('a => 'a) => ('a * 'a) set"  ("<rel>")

defs
  fun_to_rel_def : "<rel> f == {(x, f x)|x. True}"
*)
  
definition
  fun_to_rel :: "('a => 'a) => ('a * 'a) set"  ("<rel>")
  where
  "<rel> f == {(x, f x)|x. True}"

(*consts
  diff_fun :: "('x => 'a) set => bool"*)

(*
consts
  Renaming1_event_fun   :: "'a => 'a => ('a => 'a)"
  Renaming1_channel_fun :: "('x => 'a) => ('x => 'a) => ('a => 'a)"

  Renaming1_event   :: "'a => 'a => ('a * 'a) set"   ("_<-->_" [100,100] 100)
                                        
  Renaming1_channel :: "('x => 'a) => ('x => 'a) => ('a * 'a) set"
                                                    ("_<==>_" [100,100] 100)

  Renaming2_event_fun   :: "'a set => 'a => ('a => 'a)"
  Renaming2_channel_fun :: "('x => 'a) => ('x => 'a) => ('a => 'a)"

  Renaming2_event   :: "'a set => 'a => ('a * 'a) set"   ("_<<-_" [100,100] 100)
                                        
  Renaming2_channel :: "('x => 'a) => ('x => 'a) => ('a * 'a) set"
                                                    ("_<==_" [100,100] 100)

defs
  Renaming1_event_fun_def : "Renaming1_event_fun a b == 
              (%c. if (c=a) then b else if (c=b) then a else c)"

  Renaming1_channel_fun_def : "Renaming1_channel_fun f g == 
              (%c. if (disjoint_range f g)
                   then      if (EX x. f x = c) then g(inv f c) 
                        else if (EX x. g x = c) then f(inv g c)
                        else c
                   else c)"

  Renaming1_event_def   : "a<-->b == <rel> (Renaming1_event_fun a b)"

  Renaming1_channel_def : "f<==>g == <rel> (Renaming1_channel_fun f g)"

defs
  Renaming2_event_fun_def : "Renaming2_event_fun A b == 
              (%c. if (c:A) then b else c)"

  Renaming2_channel_fun_def : "Renaming2_channel_fun f g == 
              (%c. if (disjoint_range f g)
                   then      if (EX x. f x = c) then g(inv f c) 
                        else c
                   else c)"
  Renaming2_event_def   : "A<<-b == <rel> (Renaming2_event_fun A b)"
  Renaming2_channel_def : "f<==g == <rel> (Renaming2_channel_fun f g)"
*)

definition
  Renaming1_event_fun   :: "'a => 'a => ('a => 'a)"
  where
    "Renaming1_event_fun a b == 
              (%c. if (c=a) then b else if (c=b) then a else c)"
  
definition              
  Renaming1_channel_fun :: "('x => 'a) => ('x => 'a) => ('a => 'a)"
  where
  "Renaming1_channel_fun f g == 
              (%c. if (disjoint_range f g)
                   then      if (EX x. f x = c) then g(inv f c) 
                        else if (EX x. g x = c) then f(inv g c)
                        else c
                   else c)"

definition
  Renaming1_event   :: "'a => 'a => ('a * 'a) set"   ("_<-->_" [100,100] 100)
  where
  "a<-->b == <rel> (Renaming1_event_fun a b)"
  
definition  
  Renaming1_channel :: "('x => 'a) => ('x => 'a) => ('a * 'a) set"
                                                    ("_<==>_" [100,100] 100)
  where "f<==>g == <rel> (Renaming1_channel_fun f g)"

definition  
  Renaming2_event_fun   :: "'a set => 'a => ('a => 'a)"
  where
  "Renaming2_event_fun A b == 
              (%c. if (c:A) then b else c)"

definition              
  Renaming2_channel_fun :: "('x => 'a) => ('x => 'a) => ('a => 'a)"
  where
  "Renaming2_channel_fun f g == 
              (%c. if (disjoint_range f g)
                   then      if (EX x. f x = c) then g(inv f c) 
                        else c
                   else c)"

definition
  Renaming2_event   :: "'a set => 'a => ('a * 'a) set"   ("_<<-_" [100,100] 100)
  where
  "A<<-b == <rel> (Renaming2_event_fun A b)"

definition  
  Renaming2_channel :: "('x => 'a) => ('x => 'a) => ('a * 'a) set"
                                                    ("_<==_" [100,100] 100)
  where "f<==g == <rel> (Renaming2_channel_fun f g)"

abbreviation
  Renaming2_signle_event :: "'a => 'a => ('a * 'a) set"  ("_<--_" [100,100] 100)
where "a<--b == {a}<<-b"

lemmas Renaming_event_fun_def =
       Renaming1_event_fun_def
       Renaming2_event_fun_def

lemmas Renaming_channel_fun_def =
       Renaming1_channel_fun_def
       Renaming2_channel_fun_def

lemmas Renaming_event_def =
       Renaming1_event_def
       Renaming2_event_def

lemmas Renaming_channel_def =
       Renaming1_channel_def
       Renaming2_channel_def


lemma Renaming_event_fun_commut:
  "Renaming1_event_fun a b = Renaming1_event_fun b a"
apply (simp add: Renaming_event_fun_def)
(* apply (simp add: expand_fun_eq) for Isabelle 2009 *)
apply (simp add: fun_eq_iff)
done

lemma Renaming_event_commut: "(a<-->b) = (b<-->a)"
apply (simp add: Renaming_event_def)
apply (simp add: Renaming_event_fun_commut)
done

lemma Renaming_channel_fun_commut:
  "Renaming1_channel_fun f g = Renaming1_channel_fun g f"
(* apply (simp add: expand_fun_eq) for Isabelle 2009 *)
apply (simp add: fun_eq_iff)
apply (simp add: Renaming_channel_fun_def)
apply (case_tac "(disjoint_range f g) & (disjoint_range g f)")
apply (force)

apply (subgoal_tac "~(disjoint_range f g) & ~(disjoint_range g f)")
apply (simp (no_asm_simp))
apply (auto)
apply (rule_tac x="y" in exI)
apply (rule_tac x="x" in exI)
apply (simp)
apply (rule_tac x="y" in exI)
apply (rule_tac x="x" in exI)
apply (simp)
done

lemma Renaming_channel_commut: "(f<==>g) = (g<==>f)"
apply (simp add: Renaming_channel_def)
apply (simp add: Renaming_channel_fun_commut)
done

lemmas Renaming_commut = Renaming_event_commut Renaming_channel_commut

lemma Renaming_channel_fun_f:
   "[| inj f ; disjoint_range f g |] ==> Renaming1_channel_fun f g (f x) = g x"
   "[| inj f ; disjoint_range f g |] ==> Renaming2_channel_fun f g (f x) = g x"
by (auto simp add: Renaming_channel_fun_def)

lemma Renaming_channel_fun_g:
   "[| inj g ; disjoint_range f g |] ==> Renaming1_channel_fun f g (g x) = f x"
   "[| inj g ; disjoint_range f g |] ==> Renaming2_channel_fun f g (g x) = g x"
by (auto simp add: Renaming_channel_fun_def)

lemma Renaming_channel_fun_h:
   "[| disjoint_range f g ; disjoint_range f h ; disjoint_range g h |]
    ==> Renaming1_channel_fun f g (h x) = h x"
   "[| disjoint_range f g ; disjoint_range f h |]
    ==> Renaming2_channel_fun f g (h x) = h x"
by (auto simp add: Renaming_channel_fun_def)

lemma Renaming_channel_fun_map_f:
  "[| inj f; disjoint_range f g |] ==> Renaming1_channel_fun f g ` f ` X = g ` X"
  "[| inj f; disjoint_range f g |] ==> Renaming2_channel_fun f g ` f ` X = g ` X"
  apply (simp add: image_def, auto simp add: Renaming_channel_fun_f)+
done

lemma Renaming_channel_fun_map_g:
  "[| inj g; disjoint_range f g |] ==> Renaming1_channel_fun f g ` g ` X = f ` X"
apply (simp add: image_def, auto simp add: Renaming_channel_fun_g)
done

lemma Renaming_channel_fun_map_h:
   "[| (disjoint_range f h) ;
       (disjoint_range g h) ;
       disjoint_range f g |]
    ==> Renaming1_channel_fun f g ` h ` X = h ` X"
   "[| (disjoint_range f h) ;
       disjoint_range f g |]
    ==> Renaming2_channel_fun f g ` h ` X = h ` X"
apply (simp add: image_def, auto simp add: Renaming_channel_fun_h)
apply (simp add: image_def, auto simp add: Renaming_channel_fun_h)
done

lemmas Renaming_channel_fun_simp 
     = Renaming_channel_fun_map_f
       Renaming_channel_fun_map_g
       Renaming_channel_fun_map_h
       Renaming_channel_fun_f
       Renaming_channel_fun_g
       Renaming_channel_fun_h


(* --- range (chanset) --- *)

lemma Renaming_Image_singleton_notin_f :
    "e \<notin> (range f) \<Longrightarrow> (f<==g `` {e}) = {e}"
  apply (simp add: Image_def Renaming_channel_def fun_to_rel_def)
  by (simp add: Renaming2_channel_fun_def image_def, force)

lemma Renaming_range_f :
   "inj f \<Longrightarrow> disjoint_range f g \<Longrightarrow> (f <== g `` (range f)) = (range g)"
  apply (simp add: Image_def Renaming_channel_def fun_to_rel_def)
  by (simp add: Renaming_channel_fun_f image_def)

lemma Renaming_range_g :
    "inj g \<Longrightarrow> disjoint_range f g \<Longrightarrow> (f <== g `` (range g)) = (range g)"
  apply (simp add: Image_def Renaming_channel_def fun_to_rel_def)
  by (simp add: Renaming_channel_fun_g image_def)

lemma Renaming_range_h :
    "disjoint_range f h \<Longrightarrow> disjoint_range f g \<Longrightarrow> f <== g `` (range h) = (range h)"
  apply (simp add: Image_def Renaming_channel_def fun_to_rel_def)
  by (simp add: Renaming_channel_fun_h image_def)

lemma Renaming_Image_singleton_f :
    "inj f \<Longrightarrow> disjoint_range f g \<Longrightarrow> (f<==g `` {f a}) = {g a}"
  apply (simp add: Image_def Renaming_channel_def fun_to_rel_def)
  by (simp add: Renaming_channel_fun_f image_def)

(* --- Ren --- *)

lemma pair_in_Renaming1_channel_1:
   "[| inj f; inj g; disjoint_range f g |]  ==> (a, g x) : f<==>g = (a = f x)"
apply (simp add: Renaming_channel_def)
apply (simp add: Renaming_channel_fun_def)
apply (simp add: fun_to_rel_def)
apply (auto)
apply (rotate_tac -1)
apply (drule sym)
apply (simp)
apply (simp add: inj_on_def)
apply (fast)
done

lemma pair_in_Renaming1_channel_2:
   "[| inj f; inj g; disjoint_range f g |] ==> (a, g x) : g<==>f = (a = f x)"
apply (simp add: Renaming_commut)
apply (simp add: pair_in_Renaming1_channel_1)
done

lemma pair_in_Renaming1_channel_3:
   "[| inj f; inj g; disjoint_range f g |] ==> (f x, a) : f<==>g = (a = g x)"
apply (simp add: Renaming_channel_def)
apply (simp add: Renaming_channel_fun_def)
apply (simp add: fun_to_rel_def)
apply (auto)
done

lemma pair_in_Renaming2_channel_3:
   "[| inj f; inj g; disjoint_range f g |] ==> (f x, a) : f<==g = (a = g x)"
apply (simp add: Renaming_channel_def)
apply (simp add: Renaming_channel_fun_def)
apply (simp add: fun_to_rel_def)
apply (auto)
done

lemmas pair_in_Renaming_channel_3 =
       pair_in_Renaming1_channel_3
       pair_in_Renaming2_channel_3

lemma pair_in_Renaming1_channel_4:
   "[| inj f; inj g; disjoint_range f g |] ==> (f x, a) : g<==>f = (a = g x)"
apply (simp add: Renaming_commut)
apply (simp add: pair_in_Renaming_channel_3)
done

lemma pair_in_Renaming1_channel_5:
   "[| inj f; inj g; disjoint_range f g ;
       ALL x. b ~= f x ;
       ALL x. b ~= g x |] ==> (a, b) : f<==>g = (a = b)"
apply (simp add: Renaming_channel_def)
apply (simp add: Renaming_channel_fun_def)
apply (simp add: fun_to_rel_def)
apply (auto)
done

lemma pair_in_Renaming1_channel_6:
   "[| inj f; inj g; 
       disjoint_range f g ;
       ALL x. a ~= f x ;
       ALL x. a ~= g x |] ==> (a, b) : f<==>g = (a = b)"
apply (simp add: Renaming_channel_def)
apply (simp add: Renaming_channel_fun_def)
apply (simp add: fun_to_rel_def)
apply (auto)
done

lemma pair_in_Renaming2_channel_6:
   "[| inj f; inj g; 
       disjoint_range f g ;
       ALL x. a ~= f x |] ==> (a, b) : f<==g = (a = b)"
apply (simp add: Renaming_channel_def)
apply (simp add: Renaming_channel_fun_def)
apply (simp add: fun_to_rel_def)
apply (auto)
done

lemmas pair_in_Renaming_channel_6 =
       pair_in_Renaming1_channel_6
       pair_in_Renaming2_channel_6

lemmas pair_in_Renaming_channel =
       pair_in_Renaming1_channel_1
       pair_in_Renaming1_channel_2
       pair_in_Renaming_channel_3
       pair_in_Renaming1_channel_4
       pair_in_Renaming1_channel_5
       pair_in_Renaming_channel_6

(* --- sym --- *)

lemma Renaming_channel_sym_rule:
  "[| inj f ; inj g ; ((b, a) : f<==>g) |] ==> ((a, b) : f<==>g)"
apply (case_tac "~ (disjoint_range f g)")
 apply (subgoal_tac "(f<==>g) = <rel> (%c. c)")
 apply (simp add: fun_to_rel_def)
 apply (simp (no_asm_simp) add: Renaming_channel_def Renaming_channel_fun_def)

 apply (simp add: Renaming_channel_def Renaming_channel_fun_def)
 apply (simp add: fun_to_rel_def)
 apply (auto)
done

lemma Renaming_channel_sym:
  "[| inj f ; inj g |] ==> ((b, a) : f<==>g) = ((a, b) : f<==>g)"
apply (rule iffI)
apply (rule Renaming_channel_sym_rule, simp_all)
apply (rule Renaming_channel_sym_rule, simp_all)
done

(* --- inj --- *)

lemma inj_Renaming_channel_fun:
  "[| inj f; inj g |] ==> inj (Renaming1_channel_fun f g)"
apply (case_tac "~ (disjoint_range f g)")
 apply (subgoal_tac "Renaming1_channel_fun f g = (%c. c)")
 apply (simp)
   apply (simp (no_asm_simp) add: Renaming_channel_def Renaming_channel_fun_def)
apply (simp add: Renaming_channel_fun_def)
apply (simp (no_asm_simp) add: inj_on_def)
apply (elim add_not_eq_symE)
apply (intro conjI allI impI)
apply (auto)
apply (simp_all add: inj_on_def)
apply (blast)
apply (blast)
done

lemma Renaming_channel_unique:
  "ALL a b c. ((a, b) : f<==>g & (a, c) : f<==>g) --> b=c"
  "ALL a b c. ((a, b) : f<==g & (a, c) : f<==g) --> b=c"
apply (simp add: fun_to_rel_def Renaming_channel_def)
apply (simp add: fun_to_rel_def Renaming_channel_def)
done

lemma Renaming_channel_independ:
   "ALL f1 f2 g1 g2 a b c d d'.
   (inj f1 & inj f2 & inj g1 & inj g2 & 
   (disjoint_range f1 f2) &
   (disjoint_range f1 g1) &
   (disjoint_range f1 g2) &
   (disjoint_range f2 g1) &
   (disjoint_range f2 g2) &
   (disjoint_range g1 g2) &
    (a,b) : f1<==>f2 &
    (b,d) : g1<==>g2 &
    (a,c) : g1<==>g2 &
   (c,d') : f1<==>f2)
   --> d = d'"
apply (intro allI impI)
apply (elim conjE exE)
apply (elim add_not_eq_symE)

apply (case_tac "(ALL x. a ~= f1 x) & (ALL x. a ~= f2 x)")
 apply (case_tac "(ALL x. a ~= g1 x) & (ALL x. a ~= g2 x)")
  apply (simp add: pair_in_Renaming_channel)

  apply (elim disjE conjE exE)
  apply (simp add: pair_in_Renaming_channel)
  apply (elim disjE conjE exE)
  apply (simp add: pair_in_Renaming_channel)
  apply (simp add: pair_in_Renaming_channel)
  apply (simp add: pair_in_Renaming_channel)

 apply (case_tac "(ALL x. a ~= g1 x) & (ALL x. a ~= g2 x)")
  apply (simp add: pair_in_Renaming_channel)

  apply (elim disjE conjE exE)
  apply (simp add: pair_in_Renaming_channel)
  apply (simp add: pair_in_Renaming_channel)
  apply (simp add: pair_in_Renaming_channel)

apply (auto)
done

end
