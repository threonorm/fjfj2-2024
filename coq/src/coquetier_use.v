(*|
.. coq:: none
|*)
Require Import Lia.
Require Import egg.Loader.
Require Import List.
Import ListNotations.

Theorem cons_app : forall (A : Type) (l : list A) (x : A), cons x l = [x] ++ l.
    eauto.
Qed.
Theorem app_cons : forall (A : Type) (l : list A) (x : A),  [x] ++ l = cons x l.
    eauto.
Qed.
Theorem length_cons : forall (A : Type) (l : list A) (x : A), length (cons x l) = S (length l).
    eauto.
Qed.
Theorem length_nil : forall (A : Type) , length (@nil A) = O.
    eauto.
Qed.
Theorem cons_inj : forall A (x1 x2 : A) (l1 l2 : list A), x1::l1 = x2:: l2 -> x1 = x2 /\ l1 = l2.
    intros; inversion H; eauto.
Qed.
Theorem cons_inj_tl : forall A (x1 x2 : A) (l1 l2 : list A), x1::l1 = x2:: l2 ->  l1 = l2.
    intros; inversion H; eauto.
Qed.
Theorem cons_inj_hd : forall A (x1 x2 : A) (l1 l2 : list A), x1::l1 = x2:: l2 -> x1 = x2.
    intros; inversion H; eauto.
Qed.
Theorem app_inj_tl: forall A (x1 x2 : A) (l1 l2 : list A), l1 ++ [x1] =  l2 ++ [x2] ->  l1 = l2.
    intros.
    pose proof app_inj_tail; eauto.
    specialize (H0) with (1:= H).
    eapply H0.
Qed.
Theorem app_inj_hd: forall A (x1 x2 : A) (l1 l2 : list A), l1 ++ [x1] =  l2 ++ [x2] ->  x1= x2.
    intros.
    pose proof app_inj_tail; eauto.
    specialize (H0) with (1:= H).
    eapply H0.
Qed.
(* 
Ltac egg_repeat := 
  repeat (time "Egg" (egg_simpl_goal 5) ; 
          try reflexivity;
          try lazymatch goal with 
                | [H :?a |- _] => solve [ inversion H ] end). *)

Tactic Notation "egg_repeat" int(k) := 
  repeat (time "Egg" (egg_simpl_goal k) ; 
          try reflexivity;
          try lazymatch goal with 
                | [H :?a |- _] => solve [ inversion H ] end).
Tactic Notation "egg_simpl" int(k) constr(x):= 
(* x needs to be a const, a bit sad *)
  time "Egg Elim" (egg_elim k x).

Tactic Notation "egg_eexists" int(k) := 
  time "Egg Search Evar" (egg_search_evars k).


Ltac egg_repeat4 := 
  repeat (time "Egg" (egg_simpl_goal 4) ; 
          try reflexivity;
          try lazymatch goal with 
                | [H :?a |- _] => solve [ inversion H ] end).
Ltac add_term t :=
    idtac t;
    let tt := type of t in
    match tt with 
    | forall x, ?a => 
        match t with 
        | ?f ?x => add_term f; add_term x
        | ?a => idtac
        end
    | Type => 
        idtac
    | Set => 
        idtac
    | _ => 
        pose proof (eq_refl t) 
    end.

Ltac keepterms t := 
    (* Useful tactic to remember *)
    match t with
| ?a ?b =>
    tryif (assert_fails (has_evar a)) then 
    (tryif (assert_fails (has_evar b)) then add_term (a b)else (add_term ( a); keepterms b))
        else 
    (keepterms a; keepterms b)
| ?a => tryif (assert_fails (has_evar a)) then (add_term ( a)) else idtac
    end.

Require Import Coq.Logic.PropExtensionality.
Ltac propintu := intros; apply propositional_extensionality; intuition idtac.
Lemma and_True_l: forall (P: Prop), (True /\ P) = P. Proof. propintu. Qed.
Lemma and_True_r: forall (P: Prop), (P /\ True) = P. Proof. propintu. Qed.
Lemma reify_fundamental : forall t (x y:t), x = y ->  True = (x = y).  propintu. Qed. 
Ltac add_subterms_goal := match goal with 
    | |- ?g => keepterms g 
    end.

Lemma app_assoc_r :  forall (A : Type) (l m n : list A),
    (l ++ m) ++ n = l ++ m ++ n .
    intros.
    erewrite <- app_assoc; eauto.
    Qed.
Lemma and_True_BlockHole : forall (P: Prop) (Q:Prop), P = True -> Q = True -> P /\ Q. Proof. intros. rewrite H, H0. eauto. Qed.
Ltac pose_prop_lemmas :=
pose proof and_True_l as and_True_l;
pose proof and_True_r as and_True_r;
pose proof and_True_BlockHole as and_consider_lr;
pose proof reify_fundamental as reify_fundamental .



Lemma app_length_r : forall (A : Type) (l l' : list A),
        (length l + length l')%nat = length (l ++ l').
        intros; erewrite app_length; eauto.
Qed.


Definition represent {A:Type} (a:A) := True.

Theorem trigger_length : forall (A : Type) (l: list A), 
    l = l -> True = represent (length l).
    eauto.
Qed.
Ltac list_lemmas :=
 pose proof app_nil_r;
 pose proof app_nil_l;
 pose proof app_assoc;
 pose proof app_assoc_r;
 pose proof app_inj_tl;
 pose proof app_inj_hd;
 pose proof cons_inj_hd;
 pose proof cons_inj_tl;
 pose proof cons_app;
 pose proof app_cons;
 pose proof length_cons;
 pose proof app_length;
 pose proof length_nil;
 pose proof trigger_length.
Ltac list_theory := list_lemmas.

Lemma add_rec :  forall n x, Nat.add (S x) n = S (Nat.add x n). lia. Qed.
Lemma init_st : (forall x y, Nat.add x y = Init.Nat.add x y). eauto. Qed.
Lemma st_init : (forall x y, Init.Nat.add x y = Nat.add x y). eauto. Qed.
Require Import Arith.
Ltac nat_without_assoc := 
    pose proof Nat.add_comm;
    pose proof Nat.add_0_r;
    pose proof add_rec;
    pose proof init_st;
    pose proof st_init.

Notation "'consider' t" := (True = represent t) (at level 200).

Tactic Notation "coquetier_exists" int(k) := 
 add_subterms_goal;
 egg_search_evars k;
  repeat ((egg_simpl_goal k) ; 
          try reflexivity;
          try lazymatch goal with 
                | [H :?a |- _] => solve [ inversion H ] end).
Tactic Notation "coquetier_simpl" int(k) := 
 add_subterms_goal;
  repeat ((egg_simpl_goal k) ; 
          try reflexivity;
          try lazymatch goal with 
                | [H :?a |- _] => solve [ inversion H ] end);simpl.
(*|
.. raw:: latex

    Let's reconsider our initial very elementary goal, but solve it without
    providing the witness manually, querying Coquetier instead.
    
.. coq:: unfold 
|*)
Lemma eggTypeEmbedding : forall (t : Type) (x y : t) (pf : x = y), x = y.
eauto.
Qed.
Goal forall x y, x = y ->
        [4;2] = y ->
        exists t q, x = t::q. (* .in *)
Proof. (* .in *)
    intros. (* .in *)
    eexists; eexists. (* .unfold *)
    list_theory; 
    pose_prop_lemmas. (* .none *)
    coquetier_exists 4. (* .no-out *)
Qed.

(*|
.. raw:: latex

    Note that the tactics \verb|coquetier_exists| takes an integer parameter, we will see later that 
    it is a bound on the width of the engine's search. Similarly, we can handle the other goals:
    
.. coq:: unfold 
|*)

Goal forall m, exists l,
    length l = (3 + (length m)) /\ 1 :: l ++ [4]= [1;2;3;7] ++ m ++ [4]. (* .in *)
Proof. (* .in *)
    intros; eexists. (* .none *)
    list_theory. (* .in *)
    pose_prop_lemmas. (* .none *)
    coquetier_exists 4. (* .no-out *)
   (* coquetier_simpl 4. (* .unfold -.h#* *)
   coquetier_simpl 4. .unfold -.h#* *)
Qed.
Require Import NArith.

(* Lemma consider_app : forall {A} (l l': list A), l = l -> l' = l'  -> consider (l ++ l').
 eauto.
 Qed. *)
  Goal forall r0, exists (l: list (N* option N )) (rhs tag : N), [(0%N, Some r0)] = l ++ [(tag, Some rhs)].
 intros; eexists. (* .none *)
 eexists.
 eexists.

 instantiate (3:= []).
 simpl.
    list_theory. (* .in *)
    pose_prop_lemmas. (* .none *)
    add_subterms_goal.
    (* pose proof @consider_app. *)
    coquetier_exists 3. (* .no-out *)
    Qed. 

(*|
.. raw:: latex


    Similarly, it works for our example that requires simplification only.
    The tactic gets stuck where we want it to get stuck.
    We do not display the hypothesis in the final goal.
.. coq:: unfold 
|*)

Axiom lset : forall {A:Type} (l : list A) (n:nat) (ne : A), list A. (* .none *)
Axiom set_ax : forall {A: Type} (l r : list A) (e ne : A), 
    lset (l ++ [e] ++ r) (length l) ne = (l ++ [ne] ++ r).  (* .none *)
Ltac list_getset :=
    pose proof @set_ax. (* .none *)

Goal forall (l1 l2 : list nat) (x y : nat) (j : nat),
   j = (length l1 + length l1) ->
   lset (l1 ++ (l1 ++ [x] ++ l2) ++ [1;2]) j y = l1 ++ l1 ++ [x] ++ l2 ++ [1;2]. (* .in *)
Proof. (* .in *)
   intros. (*  .none *)
   list_theory; list_getset. (* .in *)
   pose_prop_lemmas;
   nat_without_assoc. (* .none *)
   coquetier_simpl 4. (* .unfold -.h#* *)
Abort.
Require Import Nat.
Import Nat.

Ltac prove_eq_by_steps :=
 match goal with 
 | [ |- ?a = ?b] => 
     pattern a;
     match goal with 
     | [|-?f ?x] => 
         let yo := fresh "CurrentTerm" in
         let yo2 := fresh "EqCurrentTerm" in
         remember f as yo eqn:yo2;
         symmetry in yo2
     end
 end.
Tactic Notation "equals_to" constr_list(l) :=
    egg_simpl_to 3 l; cbv beta.
Ltac final_step := subst; reflexivity.

Goal forall (x y : nat),
    (x + y)^2 = x^2 + 2*x*y + y^2.
    (* .in *)
Proof. (* .in *)
   intros. (*  .none *)

   assert (forall x , x + x= 2*x ) by lia.
   pose proof Nat.mul_1_r.
   pose proof Nat.mul_1_l.
   assert (forall x , x^2= x*x) by (simpl;lia).
   assert (forall x , x*x = x^2) by (simpl;lia).
   assert (forall x , 0+x = x) by lia.
   assert (forall x , 0+x = x) as yo by lia.
   symmetry in yo.
   pose proof Nat.add_comm.
   pose proof Nat.mul_comm.
   pose proof Nat.mul_add_distr_l.
   pose proof Nat.mul_add_distr_l.
   symmetry in H8.
   pose proof Nat.mul_add_distr_r.
   pose proof Nat.mul_add_distr_r.
   symmetry in H10.
   pose proof Nat.add_assoc.
   pose proof Nat.add_assoc.
   symmetry in H12.
   pose proof Nat.mul_assoc.
   pose proof Nat.mul_assoc.
   symmetry in H13.

   nat_without_assoc. (* .none *)
   prove_eq_by_steps.
   equals_to (x^2) (y^2).
   Set Egg Misc Tracing.
   equals_to (x^2 + 2*x*y + y^2).
   final_step.
Qed. *)
