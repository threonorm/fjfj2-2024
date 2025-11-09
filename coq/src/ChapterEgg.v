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

Ltac egg_repeat := 
  repeat (time "Egg" (egg_simpl_goal 5) ; 
          try reflexivity;
          try lazymatch goal with 
                | [H :?a |- _] => solve [ inversion H ] end).

Tactic Notation "egg_repeat_n" int(k) := 
  repeat (time "Egg" (egg_simpl_goal k) ; 
          try reflexivity;
          try lazymatch goal with 
                | [H :?a |- _] => solve [ inversion H ] end).
 "egg_simpl" int(k) constr(x):= 
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
(*|
.. raw:: latex

    Let's consider the following very elementary goal.
 
.. coq:: unfold 
|*)

Goal forall x y, x = y ->
        [4;2] = y ->
        exists t q, x = t::q. (* .in *)
Proof. (* .in *)
    intros. (* .in *)
    eexists; eexists. (* .unfold *)

(*|
.. raw:: latex

    We can try standard Coq tactics to solve this easy goal, but they fail:

.. coq:: unfold 
|*)
    Fail congruence. (* .no-out *)
    Fail easy. (* .no-out *)
(*|
.. raw:: latex

    Note that if we are ready to instantiate the existential variables by hand,
    then the standard \verb|congruence| tactic can prove the desired equality.

.. coq:: unfold 
|*)
    instantiate (1:= [2]). (* .in *)
    instantiate (1:= 4). (* .in *)
    congruence.
Qed.

(*|
.. raw:: latex

    This minimal example illustrate a common pattern. 
    Standard Coq tactics are usually not designed to work in the presence of existential variable.
    This is a problem for us, as we are very often introducing and manipulating existential variables in our specifications.
    Note that if we embed this goal in any SMT solver, we will find that the solver can easily discharge it.

    The goal of this chapter will be to introduce a proof-search strategy that can solve automatically this kind of goals without having to instantiate the existential variables.

    Before diving into this technique, let's give two more examples.
    First an example where the theory necessary to prove the goal is slightly more sophisticated and that we would like to cover, and then
    an example to motivate a central aspect of our approach.

.. coq:: unfold 
|*)

Goal forall m, exists l,
    length l = (3 + (length m)) /\ 1 :: l ++ [4]= [1;2;3;7] ++ m ++ [4]. (* .in *)
Proof. (* .in *)
    intros; eexists. (* .none *)
(*|
.. raw:: latex


    Manually inspecting this goal will have you considering that
    \verb|l = [2;3;7] ++ 7| works.

    Though this goal is still a bit more sophisticated than the previous one, as it
    involves the structure of lists: it uses the operators \verb|++|,\verb|::| and \verb|length| and 
    the equality axioms on those operators (that we name the theory of list).

    In other words, the goal basically requires unification modulo the theory of list.
    We have defined a tactic to import the equational theory of list in the context, we display a few of those equations:
.. coq:: unfold 
|*)
    list_theory. (* .unfold -.h#* .h#H .h#H9 .h#H2 *)
    pose_prop_lemmas. (* .none *)
    (* Though the standard tactics fail to solve the goal. *)
    Fail easy. (* .no-out *)
    Fail congruence. (* .no-out *)
    (* As a side note, the [firstorder] tactics takes 36s to fail solving the goal as well. *)
    (* If we are ready to give the witness for [l], then the situation is slightly different: *)
    instantiate (1:= [2;3;7] ++ m). (* .in *)
    Fail congruence. (* .no-out *)
    (* Though firstorder succeeds instantaneously. *)
    firstorder.
Qed.


(*|
.. raw:: latex

   Our last example, showcases a typical use case we have:
   sometimes we do not want to actually solve the goal in one step, but we would
   like to simplify the goal, using the contextual hypothesis.

   This last example uses the \verb|lset| function.
   \verb|lset| is simply a function to set the nth element of a list.

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
(*|
.. raw:: latex

    This new example states an equality for an expression that uses [lset].
    To hope to prove this goal, we will need the reasoning principles to
    eliminate [lset]. This equation was not part of the theory of list we had previously
    define but can easily extend the theory. Here we display the key new lemma we added
    \verb|H14|.

.. coq:: unfold 
|*)
   list_theory; list_getset. (* .unfold -.h#* .h#H14 *)
   
   pose_prop_lemmas;
   nat_without_assoc. (* .none *)
(*|
.. raw:: latex

    We can try running \verb|firstorder congruence|. 
    This compound tactic should have a good chance of solving this simple goal as there are
    no existential variables and the goal falls within a logic fragment that the
    tactic should be able to solve.

.. coq:: unfold 
|*)
   Fail timeout 10 firstorder congruence. (* .no-out *)
(*|
.. raw:: latex

    Though, the tactic starts running without succeeding
    (we tried running it for 250s before killing it).

    There is a very good reason for the tactic not succeeding : this goal is
    false.
    
    Indeed,  the \verb|lset| expression on the left is actually equal to:
                \verb|l1 ++ l1 ++ __[y]__ ++ l2 ++ [1; 2]|
    instead of:
                \verb|l1 ++ l1 ++ [x] ++ l2 ++ [1; 2]|

    So the goal is only true if we assume an extra hypothesis: 
    \verb|x = y|. 

.. coq:: unfold 
|*)
Abort.


Goal forall (l1 l2 : list nat) (x y : nat) (j : nat),
   j = (length l1 + length l1) ->
   (* The extra hypothesis: *)
   x = y ->
   lset (l1 ++ (l1 ++ [x] ++ l2) ++ [1;2]) j y = l1 ++ l1 ++ [x] ++ l2 ++ [1;2]. (* .in *)
Proof.  (* .in *)
   intros. (*  .none *)
   list_theory; list_getset. (* .in *)
   pose_prop_lemmas;
   nat_without_assoc. (* .none *)
   firstorder congruence. (* .no-out *)
   (* Indeed, with this extra-hypothesis, the standard compound tactic
   [firstorder congruence] succeeds.  *)
Qed.


(*|
.. raw:: latex

    Why did we just give this last example? We showcased a standard tactic
    failing in proving an incorrect goal: it looks more like a feature
    than a bug.

    The issue is not that the tactic failed to prove the goal.
    The problem is that the user does not know the source of this failure. Maybe the tactic has a performance problem, or maybe the tactic
    is being tripped-off by some expressions in the context that are not quite expected by the tactics, or maybe the
    goal we are trying to prove is simply false.
    
    When the goal is complicated, manual inspection of the goal to identify the source of the problem 
    can be difficult and time-consuming.
    
    Verification tactics tend to assume that the common case is that one is always verifying a correct design,
    and is not making mistakes when going through the proof. We found ourselves
    commonly violating this assumption.
    
    Instead of producing tactics aimed at solving the goal, we aim for a tactic that \emph{simplifies} the goal to the best of its ability.

    For example, in the case of the false goal, we would like the tactics to rewrite the goal to:
    \begin{verbatim}
    l1 ++ l1 ++ [y] ++ l2 ++ [1; 2] = l1 ++ l1 ++ [x] ++ l2 ++ [1; 2]
    \end{verbatim}

    This expression is simpler than the original goal, and figuring out the missing hypothesis from this goal is significantly easier.

|*)

