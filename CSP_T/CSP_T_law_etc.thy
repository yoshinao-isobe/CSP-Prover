           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                  April 2006               |
            |                  March 2007  (modified)   |
            |                October 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_law_etc
imports CSP_T_law_aux
begin

(*------------------------*
         |~| --> !!
 *------------------------*)

lemma cspT_Int_choice_to_Rep:
  "(P |~| Q) =T[M,M] (!nat n:{0, (Suc 0)} .. (IF (n = 0) THEN P ELSE Q))"
apply (rule cspT_rw_right)
apply (subgoal_tac 
 "(!nat n:{0, (Suc 0)} .. IF (n = 0) THEN P ELSE Q) =T[M,M]
  (!nat n:({0} Un {(Suc 0)}) .. IF (n = 0) THEN P ELSE Q)")
apply (assumption)
apply (rule cspT_decompo)
apply (fast)
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_Rep_int_choice_union_Int)
apply (rule cspT_decompo)

apply (rule cspT_rw_right)
apply (rule cspT_Rep_int_choice_singleton)
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (simp)

apply (rule cspT_rw_right)
apply (rule cspT_Rep_int_choice_singleton)
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF)
apply (simp)
done

(*** cspT_Rep_int_choice_set_input ***)

lemma cspT_Rep_int_choice_sum_set_input:
  "!! c:C .. (!set X:(Xsf c) .. (? :X -> (Pff c)))
   =T[M,M] !set X:(Union {(Xsf c) |c. c : sumset C}) .. 
          (? a:X -> (!! c:{c:C. EX X. X:(Xsf c) & a:X}s .. (Pff c a)))"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE bexE disjE)
 apply (simp_all)
  apply (force)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE bexE disjE)
 apply (simp_all)
  apply (rule_tac x="c" in bexI)
  apply (force)
  apply (simp)

  apply (simp)
  apply (rule_tac x="ca" in bexI)
  apply (simp)
  apply (simp)
  apply (fast)
  apply (simp)
done

(*** cspT_Rep_int_choice_set_input ***)

lemma cspT_Rep_int_choice_set_input:
  "!nat n:N .. (!set X:(Xsf n) .. (? :X -> (Pff n)))
   =T[M,M] !set X:(Union {(Xsf n) |n. n : N}) .. 
          (? a:X -> (!nat n:{n:N. EX X. X:(Xsf n) & a:X} .. (Pff n a)))"
apply (simp add: Rep_int_choice_nat_def)
apply (rule cspT_rw_left)
apply (rule cspT_Rep_int_choice_sum_set_input)
apply (rule cspT_decompo)
apply (force)
apply (simp)
done

(*** cspT_Rep_int_choice_set_set_DIV ***)

lemma cspT_Rep_int_choice_set_set_DIV:
  "[| Xs ~= {} ; Ys ~= {} |] ==> 
   !set X:Xs .. (!set Y:Ys .. (? a:(X Un Y) -> DIV))
   =T[M,M] !set Z:{X Un Y |X Y. X:Xs & Y:Ys} .. (? a:Z -> DIV)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE bexE disjE)
 apply (simp_all)
  apply (rule_tac x="X Un Xa" in exI)
  apply (simp)
  apply (rule_tac x="X" in exI)
  apply (rule_tac x="Xa" in exI)
  apply (simp)
  apply (rule_tac x="X Un Xa" in exI)
  apply (simp)
  apply (rule_tac x="X" in exI)
  apply (rule_tac x="Xa" in exI)
  apply (simp)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE bexE disjE)
 apply (simp_all)
 apply (force)
done

(*********************************************************
               (P [+] SKIP) |~| (Q [+] SKIP)
 *********************************************************)

(* p.289 *)

lemma cspT_Int_choice_Ext_choice_SKIP:
  "(P [+] SKIP) |~| (Q [+] SKIP) =T[M,M] (P [+] Q [+] SKIP)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces)
 apply (force)

(* <= *)
 apply (rule, simp add: in_traces)
 apply (force)
done

(*********************************************************
               (P [+] DIV) |~| (Q [+] DIV)
 *********************************************************)

lemma cspT_Int_choice_Ext_choice_DIV:
  "(P [+] DIV) |~| (Q [+] DIV) =T[M,M] (P [+] Q [+] DIV)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces)
 apply (force)

(* <= *)
 apply (rule, simp add: in_traces)
 apply (force)
done

(*********************************************************
             (P [+] SKIP) |~| (Q [+] DIV)
 *********************************************************)

lemma cspT_Int_choice_Ext_choice_SKIP_DIV: 
  "(P [+] SKIP) |~| (Q [+] DIV) =T[M,M] (P [+] Q [+] SKIP)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces, force)+
done

(*********************************************************
             (P [+] DIV) |~| (Q [+] SKIP)
 *********************************************************)

lemma cspT_Int_choice_Ext_choice_DIV_SKIP: 
  "(P [+] DIV) |~| (Q [+] SKIP) =T[M,M] (P [+] Q [+] SKIP)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces, force)+
done

(*********************************************************
         (P [+] SKIP or DIV) |~| (Q [+] DIV or SKIP)
 *********************************************************)

lemma cspT_Int_choice_Ext_choice_SKIP_or_DIV:
  "[| P2 = SKIP | P2 = DIV ; Q2 = SKIP | Q2 = DIV |] ==>
   (P1 [+] P2) |~| (Q1 [+] Q2) =T[M,M] (P1 [+] Q1 [+] (P2 |~| Q2))"
apply (elim disjE)
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_decompo)
apply (rule cspT_reflex)
apply (rule cspT_idem)
apply (simp add: cspT_Int_choice_Ext_choice_SKIP)

apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_decompo)
apply (rule cspT_reflex)
apply (rule cspT_unit)
apply (simp add: cspT_Int_choice_Ext_choice_SKIP_DIV)

apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_decompo)
apply (rule cspT_reflex)
apply (rule cspT_unit)
apply (simp add: cspT_Int_choice_Ext_choice_DIV_SKIP)

apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_decompo)
apply (rule cspT_reflex)
apply (rule cspT_unit)
apply (simp add: cspT_Int_choice_Ext_choice_DIV)
done

(*********************************************************
                    (P [+] DIV) |~| P
 *********************************************************)

lemma cspT_Ext_choice_DIV_Int_choice_Id:
  "(P [+] DIV) |~| P =T[M,M] P"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
 apply (rule, simp add: in_traces)
 apply (force)
 apply (rule, simp add: in_traces)
done


(* =================================================== *
 |             addition for CSP-Prover 5               |
 |                    (renaming)                       |
 * =================================================== *)

lemma cspT_Ext_pre_choice_Renaming_fun_step:
  "(? x:X -> Pf x)[[<rel> f]] =T[M,M] 
   (? y:(f ` X) -> (! x:{x:X. y = f x} .. (Pf x[[<rel> f]])))"
apply (rule cspT_rw_left)
apply (rule cspT_step)

apply (rule cspT_decompo)
apply (simp add: fun_to_rel_def)
apply (force)

apply (rule cspT_decompo)
apply (simp add: fun_to_rel_def)
apply (force)
done

(* Act prefix event *)

lemma cspT_Act_prefix_Renaming_fun_step:
  "(a -> P)[[<rel> f]] =T[M,M] f(a) -> P[[<rel> f]]"
apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_step)

apply (rule cspT_rw_left)
apply (rule cspT_Ext_pre_choice_Renaming_fun_step)

apply (rule cspT_rw_right)
apply (rule cspT_step)

apply (rule cspT_decompo)
apply (simp)

apply (simp)
apply (subgoal_tac 
  "{x. x = a & f a = f x}={a}")
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_Rep_int_choice_const_com_rule)
apply (auto)
apply (rule cspT_rw_left)
apply (rule cspT_IF_split)
apply (auto)
done

lemmas cspT_Renaming_fun_step
     = cspT_Ext_pre_choice_Renaming_fun_step
       cspT_Act_prefix_Renaming_fun_step

(* -------- event -------- *)

lemma cspT_Act_prefix_Renaming1_event1_step_in:
  "(a -> P)[[a<-->b]] =T[M,M] b -> P[[a<-->b]]"
apply (simp add: Renaming_event_def Renaming_event_fun_def)
by (rule cspT_rw_left, rule cspT_Act_prefix_Renaming_fun_step, auto)

lemma cspT_Act_prefix_Renaming1_event2_step_in:
  "(a -> P)[[b<-->a]] =T[M,M] b -> P[[b<-->a]]"
by (simp add: cspT_Act_prefix_Renaming1_event1_step_in Renaming_commut)

lemma cspT_Act_prefix_Renaming1_event_step_notin:
  "[| a ~= c ; b ~= c |] ==> (c -> P)[[a<-->b]] =T[M,M] c -> P[[a<-->b]]"
apply (simp add: Renaming_event_def Renaming_event_fun_def)
by (rule cspT_rw_left, rule cspT_Act_prefix_Renaming_fun_step, auto)

lemmas cspT_Act_prefix_Renaming1_event_step =
       cspT_Act_prefix_Renaming1_event1_step_in
       cspT_Act_prefix_Renaming1_event2_step_in
       cspT_Act_prefix_Renaming1_event_step_notin


lemma cspT_Act_prefix_Renaming2_set_event_step_in:
  "a:A ==> (a -> P)[[A<<-b]] =T[M,M] b -> P[[A<<-b]]"
apply (simp add: Renaming_event_def Renaming_event_fun_def)
by (rule cspT_rw_left, rule cspT_Act_prefix_Renaming_fun_step, auto)

lemma cspT_Act_prefix_Renaming2_set_event_step_notin:
  "c~:A ==> (c -> P)[[A<<-b]] =T[M,M] c -> P[[A<<-b]]"
apply (simp add: Renaming_event_def Renaming_event_fun_def)
by (rule cspT_rw_left, rule cspT_Act_prefix_Renaming_fun_step, auto)

lemma cspT_Act_prefix_Renaming2_set_event_step:
  "(a -> P)[[A<<-b]] =T[M,M]
   IF (a:A) THEN (b -> P[[A<<-b]])
            ELSE (a -> P[[A<<-b]])"
apply (case_tac "a:A")
apply (rule cspT_rw_left)
apply (rule cspT_Act_prefix_Renaming2_set_event_step_in)
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_Act_prefix_Renaming2_set_event_step_notin)
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (simp)
done

lemmas cspT_Act_prefix_Renaming2_set_event_steps =
       cspT_Act_prefix_Renaming2_set_event_step_in
       cspT_Act_prefix_Renaming2_set_event_step_notin

(* sinlge *)

lemma cspT_Act_prefix_Renaming2_event_step_in:
  "(a -> P)[[a<--b]] =T[M,M] b -> P[[a<--b]]"
by (simp add: cspT_Act_prefix_Renaming2_set_event_step_in)

lemma cspT_Act_prefix_Renaming2_event_step_notin:
  "c~=a ==> (c -> P)[[a<--b]] =T[M,M] c -> P[[a<--b]]"
by (simp add: cspT_Act_prefix_Renaming2_set_event_step_notin)

lemmas cspT_Act_prefix_Renaming2_event_step =
       cspT_Act_prefix_Renaming2_event_step_in
       cspT_Act_prefix_Renaming2_event_step_notin


lemmas cspT_Act_prefix_Renaming_event_step =
       cspT_Act_prefix_Renaming1_event_step
       cspT_Act_prefix_Renaming2_event_step

(* -------- channel -------- *)

(* Act prefix channel *)

lemma cspT_Act_prefix_Renaming1_channel1_step_in:
  "[| inj f ; disjoint_range f g |]
   ==> (f v -> P)[[f<==>g]] =T[M,M] g v -> P[[f<==>g]]"
apply (simp add: Renaming_channel_fun_def Renaming_channel_def)
by (rule cspT_rw_left, rule cspT_Act_prefix_Renaming_fun_step, auto)

lemma cspT_Act_prefix_Renaming1_channel2_step_in:
  "[| inj f ; disjoint_range f g |]
   ==> (f v -> P)[[g<==>f]] =T[M,M] g v -> P[[g<==>f]]"
by (simp add: Renaming_commut cspT_Act_prefix_Renaming1_channel1_step_in)

lemma cspT_Act_prefix_Renaming1_channel_step_notin:
  "[| (ALL x. a ~= f x) | a ~: range f ;
      (ALL x. a ~= g x) | a ~: range g |]
   ==> (a -> P)[[f<==>g]] =T[M,M] a -> P[[f<==>g]]"
apply (simp add: Renaming_channel_fun_def Renaming_channel_def)
by (rule cspT_rw_left, rule cspT_Act_prefix_Renaming_fun_step, auto)

lemmas cspT_Act_prefix_Renaming1_channel_step =
       cspT_Act_prefix_Renaming1_channel1_step_in
       cspT_Act_prefix_Renaming1_channel2_step_in
       cspT_Act_prefix_Renaming1_channel_step_notin


lemma cspT_Act_prefix_Renaming2_channel_step_in:
  "[| inj f ; disjoint_range f g |]
   ==> (f v -> P)[[f<==g]] =T[M,M] g v -> P[[f<==g]]"
apply (simp add: Renaming_channel_fun_def Renaming_channel_def)
by (rule cspT_rw_left, rule cspT_Act_prefix_Renaming_fun_step, auto)

lemma cspT_Act_prefix_Renaming2_channel_step_notin:
  "[| (ALL x. a ~= f x) | a ~: range f |]
   ==> (a -> P)[[f<==g]] =T[M,M] a -> P[[f<==g]]"
apply (simp add: Renaming_channel_fun_def Renaming_channel_def)
by (rule cspT_rw_left, rule cspT_Act_prefix_Renaming_fun_step, auto)

lemmas cspT_Act_prefix_Renaming2_channel_step =
       cspT_Act_prefix_Renaming2_channel_step_in
       cspT_Act_prefix_Renaming2_channel_step_notin

lemmas cspT_Act_prefix_Renaming_channel_step =
       cspT_Act_prefix_Renaming1_channel_step 
       cspT_Act_prefix_Renaming2_channel_step 

(* -------*)

lemmas cspT_Act_prefix_Renaming_step = 
       cspT_Act_prefix_Renaming_fun_step
       cspT_Act_prefix_Renaming_event_step
       cspT_Act_prefix_Renaming_channel_step

(* --- Ext_pre_choice_Renaming_even --- *)

(* <--> *)

lemma cspT_Ext_pre_choice_Renaming1_event1_step:
  "a ~= b ==> 
     (? x:X -> Pf x)[[a<-->b]] =T[M,M] 
     (IF (a:X) THEN (b -> (Pf a)[[a<-->b]]) ELSE STOP) [+] 
     (IF (b:X) THEN (a -> (Pf b)[[a<-->b]]) ELSE STOP) [+] 
      (? x:(X - {a,b}) -> (Pf x)[[a<-->b]])"
apply (rule cspT_rw_left)
apply (simp add: Renaming_event_def)
apply (rule cspT_Renaming_fun_step)
apply (fold Renaming_event_def)

apply (case_tac "a:X")
 apply (case_tac "b:X")
  apply (simp)
  apply (rule cspT_rw_right)
  apply (rule cspT_decompo)
  apply (rule cspT_decompo)
  apply (rule cspT_IF_split)
  apply (rule cspT_IF_split)
  apply (rule cspT_reflex)
  apply (simp)

  apply (rule cspT_rw_right)
  apply (rule cspT_decompo)
  apply (rule cspT_decompo)
  apply (rule cspT_step)
  apply (rule cspT_step)
  apply (rule cspT_reflex)

  apply (rule cspT_rw_right)
  apply (rule cspT_decompo)
  apply (rule cspT_step)
  apply (rule cspT_reflex)

  apply (rule cspT_rw_right)
  apply (rule cspT_step)
  apply (simp)

  apply (rule cspT_decompo)
  apply (simp add: image_def Renaming_event_fun_def)
  apply (force)

  apply (simp)

   apply (case_tac "aa = a")
   apply (simp)
   apply ((rule cspT_rw_right, rule cspT_IF_split | rule cspT_decompo)| simp)+
   apply (simp add: image_def Renaming_event_fun_def)
   apply (rule cspT_rw_left)
   apply (rule cspT_Rep_int_choice_singleton)
   apply (simp)

   apply (case_tac "aa = b")
   apply (simp)
   apply ((rule cspT_rw_right, rule cspT_IF_split | rule cspT_decompo)| simp)+
   apply (simp add: image_def Renaming_event_fun_def)
   apply (subgoal_tac "{x. x ~= b & (x ~= b --> x = a)}={a}")
   apply (simp)
   apply (rule cspT_Rep_int_choice_singleton)
   apply (force)

   (* etc *)
   apply (simp)
   apply ((rule cspT_rw_right, rule cspT_IF_split | rule cspT_decompo)| simp)+
   apply (simp add: image_def Renaming_event_fun_def)
   apply (subgoal_tac 
     "{x. x ~= b & (x ~= b --> x ~= a & (x ~= a --> x : X & aa = x))}={aa}")
   apply (simp)
   apply (rule cspT_Rep_int_choice_singleton)
   apply (force)

 (* b~:X *)
  apply (simp)
  apply (rule cspT_rw_right)
  apply (rule cspT_decompo)
  apply (rule cspT_decompo)
  apply (rule cspT_IF_split)
  apply (rule cspT_IF_split)
  apply (rule cspT_reflex)
  apply (simp)

  apply (rule cspT_rw_right)
  apply (rule cspT_decompo)
  apply (rule cspT_decompo)
  apply (rule cspT_step)
  apply (rule cspT_step)
  apply (rule cspT_reflex)

  apply (rule cspT_rw_right)
  apply (rule cspT_decompo)
  apply (rule cspT_step)
  apply (rule cspT_reflex)
  apply (simp)

  apply (rule cspT_rw_right)
  apply (rule cspT_step)
  apply (simp)


  apply (rule cspT_decompo)
  apply (simp add: image_def Renaming_event_fun_def)
  apply (force)

  apply (simp)

   apply (case_tac "aa = b")
   apply (simp)
   apply ((rule cspT_rw_right, rule cspT_IF_split | rule cspT_decompo)| simp)+
   apply (simp add: image_def Renaming_event_fun_def)
   apply (subgoal_tac "{x. x ~= b & (x ~= b --> x = a)}={a}")
   apply (simp)
   apply (rule cspT_Rep_int_choice_singleton)
   apply (force)

   apply (simp)
   apply ((rule cspT_rw_right, rule cspT_IF_split | rule cspT_decompo)| simp)+
   apply (simp add: image_def Renaming_event_fun_def)
   apply (subgoal_tac
   "{x. x ~= b & (x ~= b --> x ~= a & (x ~= a --> x : X & aa = x))} = {aa}")
   apply (simp)
   apply (rule cspT_Rep_int_choice_singleton)
   apply (force)


(* a~:X *)
 apply (case_tac "b:X")

  apply (simp)
  apply (rule cspT_rw_right)
  apply (rule cspT_decompo)
  apply (rule cspT_decompo)
  apply (rule cspT_IF_split)
  apply (rule cspT_IF_split)
  apply (rule cspT_reflex)
  apply (simp)

  apply (rule cspT_rw_right)
  apply (rule cspT_decompo)
  apply (rule cspT_decompo)
  apply (rule cspT_step)
  apply (rule cspT_step)
  apply (rule cspT_reflex)

  apply (rule cspT_rw_right)
  apply (rule cspT_decompo)
  apply (rule cspT_step)
  apply (rule cspT_reflex)
  apply (simp)

  apply (rule cspT_rw_right)
  apply (rule cspT_step)
  apply (simp)

  apply (rule cspT_decompo)
  apply (simp add: image_def Renaming_event_fun_def)
  apply (force)

  apply (simp)

   apply (case_tac "aa = a")
   apply (simp)
   apply ((rule cspT_rw_right, rule cspT_IF_split | rule cspT_decompo)| simp)+
   apply (simp add: image_def Renaming_event_fun_def)
   apply (rule cspT_Rep_int_choice_singleton)

   apply (simp)
   apply ((rule cspT_rw_right, rule cspT_IF_split | rule cspT_decompo)| simp)+
   apply (simp add: image_def Renaming_event_fun_def)
   apply (subgoal_tac
   "{x. x ~= b & (x ~= b --> x ~= a & (x ~= a --> x : X & aa = x))} = {aa}")
   apply (simp)
   apply (rule cspT_Rep_int_choice_singleton)
   apply (force)


 (* b~:X *)
  apply (simp)
  apply (rule cspT_rw_right)
  apply (rule cspT_decompo)
  apply (rule cspT_decompo)
  apply (rule cspT_IF_split)
  apply (rule cspT_IF_split)
  apply (rule cspT_reflex)
  apply (simp)

  apply (rule cspT_rw_right)
  apply (rule cspT_decompo)
  apply (rule cspT_decompo)
  apply (rule cspT_step)
  apply (rule cspT_step)
  apply (rule cspT_reflex)

  apply (rule cspT_rw_right)
  apply (rule cspT_decompo)
  apply (rule cspT_step)
  apply (rule cspT_reflex)
  apply (simp)

  apply (rule cspT_rw_right)
  apply (rule cspT_step)
  apply (simp)

  apply (rule cspT_decompo)
  apply (simp add: image_def Renaming_event_fun_def)
  apply (force)

   apply ((rule cspT_rw_right, rule cspT_IF_split | rule cspT_decompo)| simp)+
   apply (simp add: image_def Renaming_event_fun_def)
   apply (subgoal_tac
   "{x. x ~= b & (x ~= b --> x ~= a & (x ~= a --> x : X & aa = x))} = {aa}")
   apply (simp)
   apply (rule cspT_Rep_int_choice_singleton)
   apply (force)
done

lemma cspT_Ext_pre_choice_Renaming1_event2_step:
  "a = b ==> 
     (? x:X -> Pf x)[[a<-->b]] =T[M,M] 
     (IF (a:X) THEN (b -> (Pf a)[[a<-->b]]) ELSE STOP) [+] 
     (IF (b:X) THEN (a -> (Pf b)[[a<-->b]]) ELSE STOP) [+] 
      (? x:(X - {a,b}) -> (Pf x)[[a<-->b]])"
apply (simp)
apply (rule cspT_rw_left)
apply (simp add: Renaming_event_def)
apply (rule cspT_Renaming_fun_step)
apply (fold Renaming_event_def)

apply (rule cspT_rw_right)
apply (rule cspT_decompo)
apply (rule cspT_idem)
apply (rule cspT_reflex)

 apply (case_tac "b:X")
  apply (simp)
  apply (rule cspT_rw_right)
  apply (rule cspT_decompo)
  apply (rule cspT_IF_split)
  apply (rule cspT_reflex)
  apply (simp)

  apply (rule cspT_rw_right)
  apply (rule cspT_decompo)
  apply (rule cspT_step)
  apply (rule cspT_reflex)

  apply (rule cspT_rw_right)
  apply (rule cspT_step)
  apply (simp)

  apply (rule cspT_decompo)
  apply (simp add: image_def Renaming_event_fun_def)
  apply (force)

  apply (simp)

   apply (case_tac "aa = b")
   apply (simp)
   apply ((rule cspT_rw_right, rule cspT_IF_split | rule cspT_decompo)| simp)+
   apply (simp add: image_def Renaming_event_fun_def)
   apply (rule cspT_Rep_int_choice_singleton)

   apply (simp)
   apply ((rule cspT_rw_right, rule cspT_IF_split | rule cspT_decompo)| simp)+
   apply (simp add: image_def Renaming_event_fun_def)
   apply (subgoal_tac 
     "{x. x ~= b & (x ~= b --> x ~= a & (x ~= a --> x : X & aa = x))}={aa}")
   apply (simp)
   apply (rule cspT_Rep_int_choice_singleton)
   apply (force)

 (* b~:X *)
  apply (simp)
  apply (rule cspT_rw_right)
  apply (rule cspT_decompo)
  apply (rule cspT_IF_split)
  apply (rule cspT_reflex)
  apply (simp)

  apply (rule cspT_rw_right)
  apply (rule cspT_decompo)
  apply (rule cspT_step)
  apply (rule cspT_reflex)

  apply (rule cspT_rw_right)
  apply (rule cspT_step)
  apply (simp)

  apply (rule cspT_decompo)
  apply (simp add: image_def Renaming_event_fun_def)
  apply (force)

   apply ((rule cspT_rw_right, rule cspT_IF_split | rule cspT_decompo)| simp)+
   apply (simp add: image_def Renaming_event_fun_def)
   apply (subgoal_tac
   "{x. x ~= b & (x ~= b --> x ~= a & (x ~= a --> x : X & aa = x))} = {aa}")
   apply (simp)
   apply (rule cspT_Rep_int_choice_singleton)
   apply (force)
done

lemma cspT_Ext_pre_choice_Renaming1_event_step:
  "(? x:X -> Pf x)[[a<-->b]] =T[M,M] 
     (IF (a:X) THEN (b -> (Pf a)[[a<-->b]]) ELSE STOP) [+] 
     (IF (b:X) THEN (a -> (Pf b)[[a<-->b]]) ELSE STOP) [+] 
      (? x:(X - {a,b}) -> (Pf x)[[a<-->b]])"
apply (case_tac "a=b")
apply (rule cspT_Ext_pre_choice_Renaming1_event2_step)
apply (simp_all)
apply (rule cspT_Ext_pre_choice_Renaming1_event1_step)
apply (simp_all)
done

(* <<- *)

lemma cspT_Ext_pre_choice_Renaming2_set_event_step_in:
  "X Int A ~= {} ==> 
     (? x:X -> Pf x)[[A<<-a]] =T[M,M] 
      a -> (! x:(X Int A) .. (Pf x)[[A<<-a]]) 
     [+] ? x:(X-A) -> (Pf x)[[A<<-a]]"
apply (rule cspT_rw_left)
apply (simp add: Renaming_event_def)
apply (rule cspT_Renaming_fun_step)
apply (fold Renaming_event_def)
apply (simp add: image_def)

apply (rule cspT_rw_right)
apply (rule cspT_decompo)
apply (rule cspT_step)
apply (rule cspT_reflex)
apply (rule cspT_rw_right)
apply (rule cspT_step)

apply (rule cspT_decompo)
apply (simp add: Renaming_event_fun_def)
apply (blast)

apply (simp)

apply (case_tac "aa = a")
 apply (simp)
 apply (case_tac "a : X & a ~: A")
  apply (simp)
  apply (rule cspT_rw_right)
  apply (rule cspT_IF_split)
  apply (simp)
  apply (rule cspT_ref_eq)

  (* <= *)
  apply (rule cspT_Int_choice_right)
   apply (rule cspT_Rep_int_choice_right)
   apply (simp)
   apply (rule cspT_Rep_int_choice_left)
   apply (rule_tac x="aaa" in exI)
   apply (simp)
   apply (simp add: Renaming_event_fun_def)

   apply (rule cspT_Rep_int_choice_left)
   apply (rule_tac x="a" in exI)
   apply (simp)
   apply (simp add: Renaming_event_fun_def)

  (* => *)
   apply (rule cspT_Rep_int_choice_right)
   apply (simp)
   apply (elim conjE bexE)
   apply (simp add: Renaming_event_fun_def)
   apply (case_tac "aaa : A")

    apply (simp)
    apply (rule cspT_Int_choice_left1)
    apply (rule cspT_Rep_int_choice_left)
    apply (simp)
    apply (rule_tac x="aaa" in exI)
    apply (simp)

    apply (simp)
    apply (rule cspT_Int_choice_left2)
    apply (simp)

 (* ~(a : X & a ~: A) *)
  apply (simp (no_asm_simp))
  apply (rule cspT_rw_right)
  apply (rule cspT_IF_split)
  apply (simp)
  apply (rule cspT_rw_right)
  apply (rule cspT_IF_split)
  apply (simp)

  apply (rule cspT_decompo)
  apply (simp add: Renaming_event_fun_def)
  apply (fast)
  apply (simp)

(* aa ~= a *)
 apply (simp)
 apply (rule cspT_rw_right)
 apply (rule cspT_IF_split)
 apply (simp)
 apply (rule cspT_rw_right)
 apply (rule cspT_IF_split)
 apply (simp)
 apply (simp add: Renaming_event_fun_def)
 apply (subgoal_tac "{x. x ~: A & (x ~: A --> x : X & aa = x)}={aa}")
 apply (simp)
 apply (rule cspT_Rep_int_choice_singleton)
 apply (force)
done


lemma cspT_Ext_pre_choice_Renaming2_set_event_step_notin:
  "[| X Int A = {} |] ==> 
     (? x:X -> Pf x)[[A<<-b]] =T[M,M] ? x:X -> (Pf x)[[A<<-b]]"
apply (simp add: Renaming_event_def)
apply (rule cspT_rw_left)
apply (rule cspT_Renaming_fun_step)
apply (fold Renaming_event_def)

apply (rule cspT_decompo)
apply (simp add: Image_def image_def)
apply (simp add: Renaming_event_fun_def)
apply (force)
apply (simp add: Renaming_event_fun_def)
apply (subgoal_tac 
  "{x. (x : A --> x : X & a = b) & (x ~: A --> x : X & a = x)} = {a}")
apply (simp)
apply (rule cspT_Rep_int_choice_singleton)
apply (force)
done

lemma cspT_Ext_pre_choice_Renaming2_set_event_step:
  "(? x:X -> Pf x)[[A<<-a]] =T[M,M] 
  IF (X Int A ~= {})
  THEN (a -> (! x:(X Int A) .. (Pf x)[[A<<-a]])
        [+] ? x:(X-A) -> (Pf x)[[A<<-a]])
  ELSE (? x:X -> (Pf x)[[A<<-a]])"
apply (case_tac "X Int A ~= {}")
apply (rule cspT_rw_left)
apply (rule cspT_Ext_pre_choice_Renaming2_set_event_step_in)
apply (simp)
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_Ext_pre_choice_Renaming2_set_event_step_notin)
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (simp)
done

(* <-- *)

lemma cspT_Ext_pre_choice_Renaming2_event_step:
  "(? x:X -> Pf x)[[a<--b]] =T[M,M] 
  IF (a : X)
  THEN (b -> (Pf a)[[a<--b]]
        [+] ? x:(X-{a}) -> (Pf x)[[a<--b]])
  ELSE (? x:X -> (Pf x)[[a<--b]])"
apply (rule cspT_rw_left)
apply (rule cspT_Ext_pre_choice_Renaming2_set_event_step)
apply (case_tac "a:X")

 apply (rule cspT_decompo)
 apply (simp)
 apply (rule cspT_decompo)
 apply (rule cspT_decompo)
 apply (simp)
 apply (subgoal_tac "X Int {a} = {a}")
 apply (simp)
 apply (rule cspT_Rep_int_choice_singleton)
 apply (force)
 apply (simp)
 apply (simp)

 apply (simp)
 apply (rule cspT_rw_right)
 apply (rule cspT_IF_split)
 apply (simp)
 apply (rule cspT_rw_left)
 apply (rule cspT_IF_split)
 apply (simp)
done

lemmas cspT_Ext_pre_choice_Renaming_event_step =
       cspT_Ext_pre_choice_Renaming1_event_step
       cspT_Ext_pre_choice_Renaming2_set_event_step
       cspT_Ext_pre_choice_Renaming2_event_step

(* sending -- event -- *)

lemma cspT_Send_prefix_Renaming1_event1_step_in:
  "inj f ==> (f!v -> P)[[a<-->f v]] =T[M,M] a -> P[[a<-->f v]]"
apply (simp add: csp_prefix_ss_def)
apply (simp add: cspT_Act_prefix_Renaming_step)
done

lemma cspT_Send_prefix_Renaming1_event2_step_in:
  "inj f ==> (f!v -> P)[[f v<-->a]] =T[M,M] a -> P[[f v<-->a]]"
by (simp add: Renaming_commut cspT_Send_prefix_Renaming1_event1_step_in)

lemma cspT_Send_prefix_Renaming1_event_step_notin:
  "[| a ~= f v | f v ~= a ; b ~= f v | f v ~= b |]
   ==> (f!v -> P)[[a<-->b]] =T[M,M] f!v -> P[[a<-->b]]" 
apply (simp add: csp_prefix_ss_def)
apply (simp add: cspT_Act_prefix_Renaming_step)
done

lemmas cspT_Send_prefix_Renaming1_event_step =
       cspT_Send_prefix_Renaming1_event1_step_in
       cspT_Send_prefix_Renaming1_event2_step_in
       cspT_Send_prefix_Renaming1_event_step_notin

(* <<- *)

lemma cspT_Send_prefix_Renaming2_set_event_step_in:
  "f v : A ==> (f!v -> P)[[A<<-a]] =T[M,M] a -> P[[A<<-a]]"
apply (simp add: csp_prefix_ss_def)
apply (simp add: cspT_Act_prefix_Renaming2_set_event_step_in)
done

lemma cspT_Send_prefix_Renaming2_set_event_step_notin:
  "f v ~: A
   ==> (f!v -> P)[[A<<-b]] =T[M,M] f!v -> P[[A<<-b]]" 
apply (simp add: csp_prefix_ss_def)
apply (simp add: cspT_Act_prefix_Renaming2_set_event_step_notin)
done

lemma cspT_Send_prefix_Renaming2_set_event_step:
  "(f!v -> P)[[A<<-a]] =T[M,M] 
   IF (f v : A) THEN (a -> P[[A<<-a]]) ELSE (f!v -> P[[A<<-a]])"
apply (case_tac "f v : A")
apply (rule cspT_rw_left)
apply (rule cspT_Send_prefix_Renaming2_set_event_step_in)
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_Send_prefix_Renaming2_set_event_step_notin)
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (simp)
done

(* <-- *)

lemma cspT_Send_prefix_Renaming2_event_step_in:
  "(f!v -> P)[[f v<--a]] =T[M,M] a -> P[[f v<--a]]"
by (simp add: cspT_Send_prefix_Renaming2_set_event_step_in)

lemma cspT_Send_prefix_Renaming2_event_step_notin:
  "[| a ~= f v | f v ~= a |]
   ==> (f!v -> P)[[a<--b]] =T[M,M] f!v -> P[[a<--b]]" 
by (simp add: cspT_Send_prefix_Renaming2_set_event_step_notin)

lemmas cspT_Send_prefix_Renaming2_event_step =
       cspT_Send_prefix_Renaming2_event_step_in
       cspT_Send_prefix_Renaming2_event_step_notin

lemmas cspT_Send_prefix_Renaming_event_step =
       cspT_Send_prefix_Renaming1_event_step
       cspT_Send_prefix_Renaming2_event_step

(* sending -- channel -- *)

lemma cspT_Send_prefix_Renaming1_channel1_step_in:
  "[| inj f ; disjoint_range f g |]
   ==> (f!v -> P)[[f<==>g]] =T[M,M] g!v -> P[[f<==>g]]"
apply (simp add: csp_prefix_ss_def)
apply (simp add: cspT_Act_prefix_Renaming_step)
done

lemma cspT_Send_prefix_Renaming1_channel2_step_in:
  "[| inj f ; disjoint_range f g |]
   ==> (f!v -> P)[[g<==>f]] =T[M,M] g!v -> P[[g<==>f]]"
by (simp add: Renaming_commut cspT_Send_prefix_Renaming1_channel1_step_in)

lemma cspT_Send_prefix_Renaming1_channel_step_notin:
  "[| (ALL x. h v ~= f x) | h v ~: range f ;
      (ALL x. h v ~= g x) | h v ~: range g |]
    ==> (h!v -> P)[[f<==>g]] =T[M,M] h!v -> P[[f<==>g]]"
apply (simp add: csp_prefix_ss_def)
apply (simp add: cspT_Act_prefix_Renaming_step)
done

lemmas cspT_Send_prefix_Renaming1_channel_step =
       cspT_Send_prefix_Renaming1_channel1_step_in
       cspT_Send_prefix_Renaming1_channel2_step_in
       cspT_Send_prefix_Renaming1_channel_step_notin

lemma cspT_Send_prefix_Renaming2_channel_step_in:
  "[| inj f ; disjoint_range f g |]
   ==> (f!v -> P)[[f<==g]] =T[M,M] g!v -> P[[f<==g]]"
apply (simp add: csp_prefix_ss_def)
apply (simp add: cspT_Act_prefix_Renaming_step)
done

lemma cspT_Send_prefix_Renaming2_channel_step_notin:
  "[| (ALL x. h v ~= f x) | h v ~: range f |]
    ==> (h!v -> P)[[f<==g]] =T[M,M] h!v -> P[[f<==g]]"
apply (simp add: csp_prefix_ss_def)
apply (simp add: cspT_Act_prefix_Renaming_step)
done

lemmas cspT_Send_prefix_Renaming2_channel_step =
       cspT_Send_prefix_Renaming2_channel_step_in
       cspT_Send_prefix_Renaming2_channel_step_notin

lemmas cspT_Send_prefix_Renaming_channel_step =
       cspT_Send_prefix_Renaming1_channel_step
       cspT_Send_prefix_Renaming2_channel_step

lemmas cspT_Send_prefix_Renaming_step =
       cspT_Send_prefix_Renaming_event_step
       cspT_Send_prefix_Renaming_channel_step

(* --- Rec_prefix_Renaming_even --- *)

(* <--> *)

lemma cspT_Rec_prefix_Renaming1_event1_step_in:
  "[| inj f ; v:X ; ALL x:X. a ~= f x |] ==> 
     (f ? x:X -> Pf x)[[a<-->f v]] =T[M,M] 
     (a -> (Pf v)[[a<-->f v]]) [+] f ? x:(X-{v}) -> (Pf x)[[a<-->f v]]"
apply (simp add: csp_prefix_ss_def)
apply (rule cspT_rw_left)
apply (simp add: Renaming_event_def)
apply (rule cspT_Renaming_fun_step)
apply (fold Renaming_event_def)

apply (rule cspT_rw_right)
apply (rule cspT_decompo)
apply (rule cspT_step)
apply (rule cspT_reflex)
apply (rule cspT_rw_right)
apply (rule cspT_step)

apply (rule cspT_decompo)
apply (simp add: inj_on_def)
apply (simp add: Image_def image_def)
apply (simp add: Renaming_event_fun_def)
apply (blast)

apply (simp)
apply (rule cspT_ref_eq)

(* <= *)
apply (case_tac "aa = a")

 (* aa = a *)
 apply (simp)
 apply (case_tac "a : f ` (X - {v})")
  apply (simp add: image_iff)

  (* a ~: f ` (X - {v})" *)
  apply (simp)
  apply (rule cspT_rw_right)
  apply (rule cspT_IF_split)
  apply (simp)
  apply (rule cspT_rw_right)
  apply (rule cspT_IF_split)
  apply (simp)
  apply (rule cspT_Rep_int_choice_left)
  apply (rule_tac x="f v" in exI)
  apply (simp add: Renaming_event_fun_def)

 (* aa ~= a *)
 apply (simp)

 apply (rule cspT_rw_right)
 apply (rule cspT_IF_split)
 apply (simp)
 apply (rule cspT_rw_right)
 apply (rule cspT_IF_split)
 apply (simp)

 apply (rule cspT_Rep_int_choice_left)
 apply (rule_tac x="aa" in exI)
 apply (simp)

 apply (simp add: image_iff)
 apply (erule bexE)
 apply (simp add: inj_on_def)
 apply (simp add: Renaming_event_fun_def)
 apply (force)

(* => *)
apply (simp add: Renaming_event_fun_def)
apply (case_tac "aa = a")

 (* aa = a *)
 apply (simp)
 apply (case_tac "a : f ` (X - {v})")

  apply (simp add: image_iff)

  (* a ~: f ` (X - {v})" *)
  apply (simp)
  apply (rule cspT_rw_left)
  apply (rule cspT_IF_split)
  apply (simp)
  apply (rule cspT_rw_left)
  apply (rule cspT_IF_split)
  apply (simp)
  apply (rule cspT_Rep_int_choice_right)
  apply (force)

 (* aa ~= a *)
 apply (simp)

 apply (rule cspT_rw_left)
 apply (rule cspT_IF_split)
 apply (simp)
 apply (rule cspT_rw_left)
 apply (rule cspT_IF_split)
 apply (simp)

 apply (rule cspT_Rep_int_choice_right)
 apply (auto)
done

lemma cspT_Rec_prefix_Renaming1_event2_step_in:
  "[| inj f ; v:X ; ALL x:X. a ~= f x |] ==> 
     (f ? x:X -> Pf x)[[f v<-->a]] =T[M,M] 
     (a -> (Pf v)[[f v<-->a]]) [+] f ? x:(X-{v}) -> (Pf x)[[f v<-->a]]"
apply (simp add: Renaming_commut)
apply (simp add: cspT_Rec_prefix_Renaming1_event1_step_in)
done

lemma cspT_Rec_prefix_Renaming1_event_step_notin:
  "[| (ALL x:X. a ~= f x) | a ~: f ` X ;
      (ALL x:X. b ~= f x) | b ~: f ` X |] ==> 
     (f ? x:X -> Pf x)[[a<-->b]] =T[M,M] f ? x:X -> (Pf x)[[a<-->b]]"
apply (simp add: csp_prefix_ss_def)
apply (simp add: Renaming_event_def)
apply (rule cspT_rw_left)
apply (rule cspT_Renaming_fun_step)
apply (fold Renaming_event_def)

apply (rule cspT_decompo)
apply (simp add: Image_def image_def)
apply (simp add: Renaming_event_fun_def)
apply (force)
apply (subgoal_tac 
  "{x : f ` X. aa = Renaming1_event_fun a b x} = {aa}")
apply (simp)
apply (rule cspT_Rep_int_choice_singleton)

apply (simp add: Renaming_event_fun_def)
apply (force)
done

lemmas cspT_Rec_prefix_Renaming1_event_step =
       cspT_Rec_prefix_Renaming1_event1_step_in
       cspT_Rec_prefix_Renaming1_event2_step_in
       cspT_Rec_prefix_Renaming1_event_step_notin

(* <<- *)

lemma cspT_Rec_prefix_Renaming2_set_event_step_in:
  "[| inj f ; EX x:X. f x : A |] ==> 
     (f ? x:X -> Pf x)[[A<<-a]] =T[M,M] 
      a -> (!<f> x:{x:X. f x : A} .. (Pf x)[[A<<-a]]) 
     [+] f ? x:(X-{x. f x : A}) -> (Pf x)[[A<<-a]]"
apply (simp add: csp_prefix_ss_def)
apply (rule cspT_rw_left)
apply (simp add: Renaming_event_def)
apply (rule cspT_Renaming_fun_step)
apply (fold Renaming_event_def)
apply (simp add: image_def)

apply (rule cspT_rw_right)
apply (rule cspT_decompo)
apply (rule cspT_step)
apply (rule cspT_reflex)
apply (rule cspT_rw_right)
apply (rule cspT_step)

apply (rule cspT_decompo)
apply (simp add: Renaming_event_fun_def)
apply (blast)

apply (simp)

apply (case_tac "aa = a")
 apply (simp)
 apply (case_tac "EX x:X - {x. f x : A}. a = f x")
  apply (simp add: image_iff)
  apply (rule cspT_rw_right)
  apply (rule cspT_IF_split)
  apply (elim conjE bexE)
  apply (simp)

  apply (rule cspT_ref_eq)

  (* <= *)
  apply (rule cspT_Int_choice_right)
   apply (rule cspT_Rep_int_choice_right)
   apply (simp)
   apply (simp)
   apply (rule cspT_Rep_int_choice_left)
   apply (rule_tac x="f aaa" in exI)
   apply (simp)
   apply (simp add: Renaming_event_fun_def)
   apply (fast)

   apply (rule cspT_Rep_int_choice_left)
   apply (rule_tac x="a" in exI)
   apply (simp)
   apply (rule conjI)
    apply (blast)
   apply (simp add: Renaming_event_fun_def)

  (* => *)
   apply (rule cspT_Rep_int_choice_right)
   apply (simp)
   apply (elim conjE bexE)
   apply (simp add: Renaming_event_fun_def)
   apply (case_tac "f xb : A")

    apply (simp)
    apply (rule cspT_Int_choice_left1)
    apply (rule cspT_Rep_int_choice_left)
    apply (simp)
    apply (rule_tac x="xb" in exI)
    apply (simp)

    apply (simp)
    apply (rule cspT_Int_choice_left2)
    apply (simp add: inj_on_def)
    apply (force)

 (* ~(EX x:X - {x. f x : A}. a = f x) *)
  apply (simp)
  apply (rule cspT_rw_right)
  apply (rule cspT_IF_split)
  apply (simp)
  apply (rule cspT_rw_right)
  apply (rule cspT_IF_split)
  apply (simp)

  apply (rule cspT_ref_eq)

  (* <= *)
   apply (rule cspT_Rep_int_choice_right)
   apply (simp)
   apply (simp)
   apply (rule cspT_Rep_int_choice_left)
   apply (rule_tac x="f aaa" in exI)
   apply (simp)
   apply (simp add: Renaming_event_fun_def)
   apply (fast)

  (* => *)
   apply (rule cspT_Rep_int_choice_right)
   apply (simp)
   apply (rule cspT_Rep_int_choice_left)
   apply (simp)
   apply (elim conjE bexE)
   apply (simp add: Renaming_event_fun_def)
   apply (case_tac "f xa : A")

    apply (simp)
    apply (rule_tac x="xa" in exI)
    apply (simp)
    apply (simp)

 (* aa ~= a *)
 apply (simp)

 apply (rule cspT_rw_right)
 apply (rule cspT_IF_split)
 apply (simp)
 apply (rule cspT_rw_right)
 apply (rule cspT_IF_split)
 apply (simp)
 apply (rule cspT_ref_eq)

  (* => *)
  apply (rule cspT_Rep_int_choice_left)
  apply (rule_tac x="aa" in exI)
  apply (simp)
  apply (erule bexE)
  apply (simp add: inj_on_def)
  apply (simp add: Renaming_event_fun_def)
  apply (force)

 (* <= *)
  apply (rule cspT_Rep_int_choice_right)
  apply (simp)
  apply (elim conjE bexE)
  apply (simp add: Renaming_event_fun_def)
   apply (case_tac "f xb : A")
   apply (simp)
   apply (simp add: inj_on_def)
   apply (force)
done


lemma cspT_Rec_prefix_Renaming2_set_event_step_notin:
  "[| (ALL x:X. f x ~: A) | A Int f ` X = {} |] ==> 
     (f ? x:X -> Pf x)[[A<<-b]] =T[M,M] f ? x:X -> (Pf x)[[A<<-b]]"
apply (simp add: csp_prefix_ss_def)
apply (simp add: Renaming_event_def)
apply (rule cspT_rw_left)
apply (rule cspT_Renaming_fun_step)
apply (fold Renaming_event_def)

apply (rule cspT_decompo)
apply (simp add: Image_def image_def)
apply (simp add: Renaming_event_fun_def)
apply (force)
apply (subgoal_tac 
  "{x : f ` X. a = Renaming2_event_fun A b x} = {a}")
apply (simp)
apply (rule cspT_Rep_int_choice_singleton)

apply (simp add: Renaming_event_fun_def)
apply (force)
done

lemma cspT_Rec_prefix_Renaming2_set_event_step:
  "inj f ==> 
  (f ? x:X -> Pf x)[[A<<-a]] =T[M,M] 
  IF (EX x:X. f x : A) 
  THEN (a -> (!<f> x:{x:X. f x : A} .. (Pf x)[[A<<-a]]) 
       [+] f ? x:(X-{x. f x : A}) -> (Pf x)[[A<<-a]])
  ELSE (f ? x:X -> (Pf x)[[A<<-a]])"
apply (case_tac "EX x:X. f x : A")
apply (rule cspT_rw_left)
apply (rule cspT_Rec_prefix_Renaming2_set_event_step_in)
apply (simp)
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_Rec_prefix_Renaming2_set_event_step_notin)
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (simp)
done

(* <-- *)

lemma cspT_Rec_prefix_Renaming2_event_step_in:
  "[| inj f ; v:X |] ==>
     (f ? x:X -> Pf x)[[f v<--a]] =T[M,M] 
     (a -> (Pf v)[[f v<--a]]) [+] f ? x:(X-{v}) -> (Pf x)[[f v<--a]]"
apply (rule cspT_rw_left)
apply (rule cspT_Rec_prefix_Renaming2_set_event_step_in)
apply (simp)
apply (simp)
apply (force)
apply (simp)

apply (rule cspT_decompo)
 apply (rule cspT_decompo)
 apply (simp)
 apply (subgoal_tac "{x : X. f x = f v}={v}")
 apply (simp)
 apply (rule cspT_rw_left)
 apply (rule cspT_Rep_int_choice_singleton)
 apply (simp)
 apply (simp)
 apply (simp add: inj_on_def)
 apply (force)

 apply (subgoal_tac "{x. f x = f v}={v}")
 apply (simp)
 apply (simp add: inj_on_def)
 apply (force)
done

lemma cspT_Rec_prefix_Renaming2_event_step_notin:
  "[| (ALL x:X. a ~= f x) | a ~: f ` X |] ==> 
     (f ? x:X -> Pf x)[[a<--b]] =T[M,M] f ? x:X -> (Pf x)[[a<--b]]"
apply (rule cspT_rw_left)
apply (rule cspT_Rec_prefix_Renaming2_set_event_step_notin)
apply (simp)
apply (force)
apply (simp)
done

lemmas cspT_Rec_prefix_Renaming2_event_step =
       cspT_Rec_prefix_Renaming2_event_step_in
       cspT_Rec_prefix_Renaming2_event_step_notin

lemmas cspT_Rec_prefix_Renaming_event_step =
       cspT_Rec_prefix_Renaming1_event_step 
       cspT_Rec_prefix_Renaming2_event_step 

(* ------ *)

(* <==> *)

lemma cspT_Rec_prefix_Renaming1_channel1_step_in:
  "[| inj f ; inj g ; disjoint_range f g |] ==>
     (f ? x:X -> Pf x)[[f<==>g]] =T[M,M] g ? x:X -> (Pf x)[[f<==>g]]"
apply (simp add: Renaming_channel_def)
apply (simp add: csp_prefix_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Renaming_fun_step)
apply (rule cspT_decompo)
apply (simp add: Renaming_channel_fun_simp)
apply (simp add: image_iff)
apply (erule bexE)
apply (simp)
apply (subgoal_tac 
  "{xa. (EX x:X. xa = f x) & g x = Renaming1_channel_fun f g xa} = {f x}")
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_Rep_int_choice_singleton)
apply (simp)

apply (auto)
apply (simp add: Renaming_channel_fun_simp)
apply (simp add: inj_on_def)
apply (force)
apply (simp add: Renaming_channel_fun_simp)
done

lemma cspT_Rec_prefix_Renaming1_channel2_step_in:
  "[| inj f ; inj g ; disjoint_range f g |] ==>
     (f ? x:X -> Pf x)[[g<==>f]] =T[M,M] g ? x:X -> (Pf x)[[g<==>f]]"
apply (simp add: Renaming_commut)
apply (simp add: cspT_Rec_prefix_Renaming1_channel1_step_in)
done

(*
lemma Renaming_channel_fun_h:
   "[| disjoint_range f g ; disjoint_range f h ; disjoint_range g h |]
    ==> Renaming_channel_fun f g (h x) = h x"
by (auto simp add: Renaming_channel_fun_def)

lemma Renaming_channel_fun_map_h:
   "[| (disjoint_range f h) ;
       (disjoint_range g h) ;
       disjoint_range f g |]
    ==> Renaming_channel_fun f g ` h ` X = h ` X"
apply (simp add: image_def)
apply (auto simp add: Renaming_channel_fun_h)
done
*)

lemma cspT_Rec_prefix_Renaming1_channel_step_notin:
  "[| inj h;
      (disjoint_range f h) | range f Int range h = {} ;
      (disjoint_range g h) | range g Int range h = {} ;
       disjoint_range f g |] ==>
    (h ? x:X -> Pf x)[[f<==>g]] =T[M,M] h ? x:X -> (Pf x)[[f<==>g]]"
apply (subgoal_tac "(disjoint_range f h) & (disjoint_range g h)")
apply (simp add: Renaming_channel_def)
apply (simp add: csp_prefix_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Renaming_fun_step)
apply (rule cspT_decompo)
apply (simp add: Renaming_channel_fun_simp)

apply (simp add: image_iff)
apply (erule bexE)
apply (simp)
apply (subgoal_tac 
  "{xa. (EX x:X. xa = h x) & h x = Renaming1_channel_fun f g xa} = {h x}")
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_Rep_int_choice_singleton)
apply (simp)

apply (auto)
apply (simp add: Renaming_channel_fun_simp)
apply (simp add: Renaming_channel_fun_simp)
apply (blast)+
done

lemmas cspT_Rec_prefix_Renaming1_channel_step =
       cspT_Rec_prefix_Renaming1_channel1_step_in
       cspT_Rec_prefix_Renaming1_channel2_step_in
       cspT_Rec_prefix_Renaming1_channel_step_notin

(* <== *)

lemma cspT_Rec_prefix_Renaming2_channel_step_in:
  "[| inj f ; inj g ; disjoint_range f g |] ==>
     (f ? x:X -> Pf x)[[f<==g]] =T[M,M] g ? x:X -> (Pf x)[[f<==g]]"
apply (simp add: Renaming_channel_def)
apply (simp add: csp_prefix_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Renaming_fun_step)
apply (rule cspT_decompo)
apply (simp add: Renaming_channel_fun_simp)
apply (simp add: image_iff)
apply (erule bexE)
apply (simp)
apply (subgoal_tac 
  "{xa. (EX x:X. xa = f x) & g x = Renaming2_channel_fun f g xa} = {f x}")
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_Rep_int_choice_singleton)
apply (simp)

apply (auto)
apply (simp add: Renaming_channel_fun_simp)
apply (simp add: inj_on_def)
apply (force)
apply (simp add: Renaming_channel_fun_simp)
done


lemma cspT_Rec_prefix_Renaming2_channel_step_notin:
  "[| inj h;
      (disjoint_range f h) | range f Int range h = {} ;
       disjoint_range f g |] ==>
    (h ? x:X -> Pf x)[[f<==g]] =T[M,M] h ? x:X -> (Pf x)[[f<==g]]"
apply (subgoal_tac "(disjoint_range f h)")
apply (simp add: Renaming_channel_def)
apply (simp add: csp_prefix_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Renaming_fun_step)
apply (rule cspT_decompo)
apply (simp add: Renaming_channel_fun_simp)

apply (simp add: image_iff)
apply (erule bexE)
apply (simp)
apply (subgoal_tac 
  "{xa. (EX x:X. xa = h x) & h x = Renaming2_channel_fun f g xa} = {h x}")
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_Rep_int_choice_singleton)
apply (simp)

apply (auto)
apply (simp add: Renaming_channel_fun_simp)
apply (simp add: Renaming_channel_fun_simp)
apply (blast)+
done

lemmas cspT_Rec_prefix_Renaming2_channel_step =
       cspT_Rec_prefix_Renaming2_channel_step_in
       cspT_Rec_prefix_Renaming2_channel_step_notin

lemmas cspT_Rec_prefix_Renaming_channel_step =
       cspT_Rec_prefix_Renaming1_channel_step 
       cspT_Rec_prefix_Renaming2_channel_step 

lemmas cspT_Rec_prefix_Renaming_step =
       cspT_Rec_prefix_Renaming_event_step
       cspT_Rec_prefix_Renaming_channel_step

(* Nondet Sending *)

(* <--> *)

lemma cspT_Nondet_send_prefix_Renaming1_event1_step_in:
  "[| inj f ; v:X ; ALL x. a ~= f x |] ==>
     (f !? x:X -> Pf x)[[a<-->f v]] =T[M,M] 
     (a -> (Pf v)[[a<-->f v]]) |~| f !? x:(X-{v}) -> (Pf x)[[a<-->f v]]"
apply (simp add: csp_prefix_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Dist)
apply (subgoal_tac "(f ` X) = {f v} Un (f ` (X - {v}))")
apply (simp del: Un_insert_left)
apply (rule cspT_rw_left)
apply (rule cspT_Rep_int_choice_com_union_Int)
apply (rule cspT_decompo)

 (* 1 *)
 apply (rule cspT_rw_left)
 apply (rule cspT_Rep_int_choice_singleton)
 apply (simp add: cspT_Act_prefix_Renaming_event_step)

 (* 2 *)
 apply (rule cspT_decompo)
 apply (simp)
 apply (rule cspT_rw_left)
 apply (rule cspT_Act_prefix_Renaming_event_step)
 apply (auto)
 apply (simp add: inj_on_def)
done

lemma cspT_Nondet_send_prefix_Renaming1_event2_step_in:
  "[| inj f ; v:X ; ALL x. a ~= f x |] ==>
     (f !? x:X -> Pf x)[[f v<-->a]] =T[M,M] 
     (a -> (Pf v)[[f v<-->a]]) |~| f !? x:(X-{v}) -> (Pf x)[[f v<-->a]]"
apply (simp add: Renaming_commut)
apply (simp add: cspT_Nondet_send_prefix_Renaming1_event1_step_in)
done

lemma cspT_Nondet_send_prefix_Renaming1_event_step_notin:
  "[| (ALL x. a ~= f x) | a ~: range f ;
      (ALL x. b ~= f x) | b ~: range f |] ==> 
   (f !? x:X -> Pf x)[[a<-->b]] =T[M,M] f !? x:X -> (Pf x)[[a<-->b]]"
apply (simp add: csp_prefix_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Dist)
apply (rule cspT_decompo)
apply (simp)
 apply (rule cspT_rw_left)
 apply (rule cspT_Act_prefix_Renaming_event_step)
 apply (auto)
done

lemmas cspT_Nondet_send_prefix_Renaming1_event_step =
       cspT_Nondet_send_prefix_Renaming1_event1_step_in
       cspT_Nondet_send_prefix_Renaming1_event2_step_in
       cspT_Nondet_send_prefix_Renaming1_event_step_notin

(* <<- *)

lemma cspT_Nondet_send_prefix_Renaming2_set_event_step_in:
  "[| inj f ; EX x:X. f x : A |] ==>
     (f !? x:X -> Pf x)[[A<<-a]] =T[M,M] 
      a -> (!<f> x:{x:X. f x : A} .. (Pf x)[[A<<-a]]) 
     |~| f !? x:(X-{x. f x : A}) -> (Pf x)[[A<<-a]]"
apply (simp add: csp_prefix_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Dist)
apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_step)

apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_step)

apply (subgoal_tac "(f ` X) = (f ` {x : X. f x : A}) Un (f ` (X - {x. f x : A}))") (* 1 *)
 apply (simp del: Un_insert_left)
 apply (rule cspT_rw_left)
 apply (rule cspT_Rep_int_choice_com_union_Int)
 apply (rule cspT_decompo)

 (* left *)
 apply (subgoal_tac 
  "a -> (!<f> x:{x : X. f x : A} .. Pf x [[A<<-a]])
   =T[M,M] !<f> x:{x : X. f x : A} .. a -> Pf x [[A<<-a]]")  (* 2 *)

  apply (rule cspT_rw_right)
  apply (assumption)
  apply (simp add: Rep_int_choice_f_def)
  apply (rule cspT_decompo)
  apply (simp)
  apply (simp add: image_iff)
  apply (elim conjE exE bexE)
  apply (simp)

  apply (rule cspT_rw_right)
  apply (rule cspT_step)
  apply (rule cspT_decompo)
  apply (simp add: Renaming_event_def)
  apply (simp add: Renaming_event_fun_def)
  apply (simp add: fun_to_rel_def)
  apply (force)

  apply (rule cspT_ref_eq)

   (* <= *)
   apply (rule cspT_Rep_int_choice_left)
   apply (simp add: Renaming_event_def)
   apply (simp add: Renaming_event_fun_def)
   apply (simp add: fun_to_rel_def)
   (* => *)
   apply (rule cspT_Rep_int_choice_right)
   apply (simp)

 (* 2 *)
  apply (rule cspT_rw_right)
  apply (rule cspT_choice_delay)
  apply (simp)
  apply (subgoal_tac "~(ALL x. x : X --> f x ~: A)")
   apply (simp (no_asm_simp))
   apply (rule cspT_rw_right)
   apply (rule cspT_IF_split)
   apply (simp)
  apply (force)


 (* right *)
 apply (rule cspT_decompo)
 apply (simp)

 apply (rule cspT_rw_right)
 apply (rule cspT_step)
 apply (rule cspT_decompo)
  apply (simp add: Renaming_event_def)
  apply (simp add: Renaming_event_fun_def)
  apply (simp add: fun_to_rel_def)
  apply (force)

 apply (simp)
 apply (rule cspT_ref_eq)

  (* <= *)
  apply (rule cspT_Rep_int_choice_left)
  apply (simp add: Renaming_event_def)
  apply (simp add: Renaming_event_fun_def)
  apply (simp add: fun_to_rel_def)
  apply (force)

  (* => *)
  apply (rule cspT_Rep_int_choice_right)
  apply (simp)

(* 1 *)
apply (auto)
done

lemma cspT_Nondet_send_prefix_Renaming2_set_event_step_notin:
  "[| (ALL x:X. f x ~: A) | A Int f ` X = {} |] ==> 
     (f !? x:X -> Pf x)[[A<<-a]] =T[M,M] 
      f !? x:X -> (Pf x)[[A<<-a]]"
apply (simp add: csp_prefix_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Dist)
apply (rule cspT_decompo)
apply (simp)

apply (rule cspT_rw_left)
apply (rule cspT_decompo)
apply (simp)
apply (rule cspT_step)

apply (rule cspT_rw_left)
apply (rule cspT_step)

apply (rule cspT_rw_right)
apply (rule cspT_step)

apply (rule cspT_decompo)
 apply (simp add: Renaming_event_def)
 apply (simp add: Renaming_event_fun_def)
 apply (simp add: fun_to_rel_def)
 apply (force)

apply (simp)
 apply (rule cspT_ref_eq)

  (* <= *)
  apply (rule cspT_Rep_int_choice_left)
  apply (simp add: Renaming_event_def)
  apply (simp add: Renaming_event_fun_def)
  apply (simp add: fun_to_rel_def)
  apply (force)

  (* => *)
  apply (rule cspT_Rep_int_choice_right)
  apply (simp)
done

lemma cspT_Nondet_send_prefix_Renaming2_set_event_step:
  "inj f ==>
  (f !? x:X -> Pf x)[[A<<-a]] =T[M,M] 
   IF (EX x:X. f x : A) 
   THEN (a -> (!<f> x:{x:X. f x : A} .. (Pf x)[[A<<-a]]) 
         |~| f !? x:(X-{x. f x : A}) -> (Pf x)[[A<<-a]])
   ELSE (f !? x:X -> (Pf x)[[A<<-a]])"
apply (case_tac "EX x:X. f x : A")
apply (rule cspT_rw_left)
apply (rule cspT_Nondet_send_prefix_Renaming2_set_event_step_in)
apply (simp)
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (simp)
apply (rule cspT_rw_left)
apply (rule cspT_Nondet_send_prefix_Renaming2_set_event_step_notin)
apply (simp)
apply (simp)
apply (rule cspT_rw_right)
apply (rule cspT_IF_split)
apply (simp)
done

(* <-- *)

lemma cspT_Nondet_send_prefix_Renaming2_event_step_in:
  "[| inj f ; v:X ; ALL x. a ~= f x |] ==>
     (f !? x:X -> Pf x)[[f v<--a]] =T[M,M] 
     (a -> (Pf v)[[f v<--a]]) |~| f !? x:(X-{v}) -> (Pf x)[[f v<--a]]"
apply (rule cspT_rw_left)
apply (rule cspT_Nondet_send_prefix_Renaming2_set_event_step_in)
apply (simp)
apply (simp)
apply (force)
apply (simp)

apply (rule cspT_decompo)
 apply (rule cspT_decompo)
 apply (simp)
 apply (subgoal_tac "{x : X. f x = f v}={v}")
 apply (simp)
 apply (rule cspT_rw_left)
 apply (rule cspT_Rep_int_choice_singleton)
 apply (simp)
 apply (simp)
 apply (simp add: inj_on_def)
 apply (force)

 apply (subgoal_tac "{x. f x = f v}={v}")
 apply (simp)
 apply (simp add: inj_on_def)
 apply (force)
done

lemma cspT_Nondet_send_prefix_Renaming2_event_step_notin:
  "[| (ALL x. a ~= f x) | a ~: range f |] ==> 
   (f !? x:X -> Pf x)[[a<--b]] =T[M,M] f !? x:X -> (Pf x)[[a<--b]]"
apply (rule cspT_rw_left)
apply (rule cspT_Nondet_send_prefix_Renaming2_set_event_step_notin)
apply (simp)
apply (force)
apply (simp)
done

lemmas cspT_Nondet_send_prefix_Renaming2_event_step =
       cspT_Nondet_send_prefix_Renaming2_event_step_in
       cspT_Nondet_send_prefix_Renaming2_event_step_notin

lemmas cspT_Nondet_send_prefix_Renaming_event_step =
       cspT_Nondet_send_prefix_Renaming1_event_step
       cspT_Nondet_send_prefix_Renaming2_event_step

(* <==> *)

lemma cspT_Nondet_send_prefix_Renaming1_channel1_step_in:
  "[| inj f ; inj g ; disjoint_range f g |] ==> 
   (f !? x:X -> Pf x)[[f<==>g]] =T[M,M] g !? x:X -> (Pf x)[[f<==>g]]"
apply (simp add: csp_prefix_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Dist)
apply (rule cspT_ref_eq)

(* <= *)
 apply (rule cspT_Rep_int_choice_right)
 apply (simp add: image_iff)
 apply (erule bexE)
 apply (simp)

 apply (rule cspT_Rep_int_choice_left)
 apply (rule_tac x="f x" in exI)
 apply (simp)
 apply (rule cspT_rw_left)
 apply (rule cspT_Act_prefix_Renaming_channel_step)
 apply (simp_all)

(* => *)
 apply (rule cspT_Rep_int_choice_right)
 apply (simp add: image_iff)
 apply (erule bexE)
 apply (simp)

 apply (rule cspT_Rep_int_choice_left)
 apply (rule_tac x="g x" in exI)
 apply (simp)
 apply (rule cspT_rw_right)
 apply (rule cspT_Act_prefix_Renaming_channel_step)
 apply (simp_all)
done

lemma cspT_Nondet_send_prefix_Renaming1_channel2_step_in:
  "[| inj f ; inj g ; disjoint_range f g |] ==> 
   (f !? x:X -> Pf x)[[g<==>f]] =T[M,M] g !? x:X -> (Pf x)[[g<==>f]]"
apply (simp add: Renaming_commut)
apply (simp add: cspT_Nondet_send_prefix_Renaming1_channel1_step_in)
done

lemma cspT_Nondet_send_prefix_Renaming1_channel_step_notin:
  "[| (disjoint_range f h) | (range f Int range h = {}) ;
      (disjoint_range g h) | (range g Int range h = {}) |] ==>
   (h !? x:X -> Pf x)[[f<==>g]] =T[M,M] h !? x:X -> (Pf x)[[f<==>g]]"
apply (simp add: csp_prefix_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Dist)
apply (rule cspT_decompo)
apply (simp)

apply (rule cspT_rw_left)
apply (rule cspT_Act_prefix_Renaming_channel_step)
apply (blast)
apply (blast)
apply (simp)
done

lemmas cspT_Nondet_send_prefix_Renaming1_channel_step =
       cspT_Nondet_send_prefix_Renaming1_channel1_step_in
       cspT_Nondet_send_prefix_Renaming1_channel2_step_in
       cspT_Nondet_send_prefix_Renaming1_channel_step_notin

(* <== *)

lemma cspT_Nondet_send_prefix_Renaming2_channel_step_in:
  "[| inj f ; inj g ; disjoint_range f g |] ==> 
   (f !? x:X -> Pf x)[[f<==g]] =T[M,M] g !? x:X -> (Pf x)[[f<==g]]"
apply (simp add: csp_prefix_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Dist)
apply (rule cspT_ref_eq)

(* <= *)
 apply (rule cspT_Rep_int_choice_right)
 apply (simp add: image_iff)
 apply (erule bexE)
 apply (simp)

 apply (rule cspT_Rep_int_choice_left)
 apply (rule_tac x="f x" in exI)
 apply (simp)
 apply (rule cspT_rw_left)
 apply (rule cspT_Act_prefix_Renaming_channel_step)
 apply (simp_all)

(* => *)
 apply (rule cspT_Rep_int_choice_right)
 apply (simp add: image_iff)
 apply (erule bexE)
 apply (simp)

 apply (rule cspT_Rep_int_choice_left)
 apply (rule_tac x="g x" in exI)
 apply (simp)
 apply (rule cspT_rw_right)
 apply (rule cspT_Act_prefix_Renaming_channel_step)
 apply (simp_all)
done

lemma cspT_Nondet_send_prefix_Renaming2_channel_step_notin:
  "[| (disjoint_range f h) | (range f Int range h = {}) |] ==>
   (h !? x:X -> Pf x)[[f<==g]] =T[M,M] h !? x:X -> (Pf x)[[f<==g]]"
apply (simp add: csp_prefix_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_Dist)
apply (rule cspT_decompo)
apply (simp)

apply (rule cspT_rw_left)
apply (rule cspT_Act_prefix_Renaming_channel_step)
apply (blast)
apply (simp)
done

lemmas cspT_Nondet_send_prefix_Renaming2_channel_step =
       cspT_Nondet_send_prefix_Renaming2_channel_step_in
       cspT_Nondet_send_prefix_Renaming2_channel_step_notin

lemmas cspT_Nondet_send_prefix_Renaming_channel_step =
       cspT_Nondet_send_prefix_Renaming1_channel_step
       cspT_Nondet_send_prefix_Renaming2_channel_step

lemmas cspT_Nondet_send_prefix_Renaming_step =
       cspT_Nondet_send_prefix_Renaming_event_step
       cspT_Nondet_send_prefix_Renaming_channel_step



(* ---------------- *
      in or notin
 * ---------------- *)

lemmas cspT_prefix_Renaming_in_step =
       cspT_Act_prefix_Renaming1_event1_step_in
       cspT_Act_prefix_Renaming1_event2_step_in
       cspT_Act_prefix_Renaming1_channel1_step_in
       cspT_Act_prefix_Renaming1_channel2_step_in
       cspT_Send_prefix_Renaming1_event1_step_in
       cspT_Send_prefix_Renaming1_event2_step_in
       cspT_Send_prefix_Renaming1_channel1_step_in
       cspT_Send_prefix_Renaming1_channel2_step_in
       cspT_Rec_prefix_Renaming1_event1_step_in
       cspT_Rec_prefix_Renaming1_event2_step_in
       cspT_Rec_prefix_Renaming1_channel1_step_in
       cspT_Rec_prefix_Renaming1_channel2_step_in
       cspT_Nondet_send_prefix_Renaming1_event1_step_in
       cspT_Nondet_send_prefix_Renaming1_event2_step_in
       cspT_Nondet_send_prefix_Renaming1_channel1_step_in
       cspT_Nondet_send_prefix_Renaming1_channel2_step_in
       cspT_Act_prefix_Renaming2_event_step_in
       cspT_Act_prefix_Renaming2_channel_step_in
       cspT_Send_prefix_Renaming2_event_step_in
       cspT_Send_prefix_Renaming2_channel_step_in
       cspT_Rec_prefix_Renaming2_event_step_in
       cspT_Rec_prefix_Renaming2_channel_step_in
       cspT_Nondet_send_prefix_Renaming2_event_step_in
       cspT_Nondet_send_prefix_Renaming2_channel_step_in

(* notin + <<- + ?X *)

lemmas cspT_prefix_Renaming_notin_step =
       cspT_Act_prefix_Renaming1_event_step_notin
       cspT_Act_prefix_Renaming1_channel_step_notin
       cspT_Send_prefix_Renaming1_event_step_notin
       cspT_Send_prefix_Renaming1_channel_step_notin
       cspT_Rec_prefix_Renaming1_event_step_notin
       cspT_Rec_prefix_Renaming1_channel_step_notin
       cspT_Nondet_send_prefix_Renaming1_event_step_notin
       cspT_Nondet_send_prefix_Renaming1_channel_step_notin
       cspT_Act_prefix_Renaming2_event_step_notin
       cspT_Act_prefix_Renaming2_channel_step_notin
       cspT_Send_prefix_Renaming2_event_step_notin
       cspT_Send_prefix_Renaming2_channel_step_notin
       cspT_Rec_prefix_Renaming2_event_step_notin
       cspT_Rec_prefix_Renaming2_channel_step_notin
       cspT_Nondet_send_prefix_Renaming2_event_step_notin
       cspT_Nondet_send_prefix_Renaming2_channel_step_notin

       cspT_Act_prefix_Renaming2_set_event_step
       cspT_Send_prefix_Renaming2_set_event_step
       cspT_Rec_prefix_Renaming2_set_event_step
       cspT_Nondet_send_prefix_Renaming2_set_event_step

       cspT_Ext_pre_choice_Renaming_event_step

(* ----------------------------------------------------------- *)

end
