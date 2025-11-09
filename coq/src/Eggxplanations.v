(*|
.. coq:: none
|*)
Require Import Lia.
Require Import Arith.
Require Import NArith.

Require Import egg.Loader.
Require Import List.
Import ListNotations.
Open Scope N.

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

Lemma add_rec :  forall n x, Nat.add (S x) n = S (Nat.add x n). lia. Qed.
Lemma init_st : (forall x y, Nat.add x y = Init.Nat.add x y). eauto. Qed.
Lemma st_init : (forall x y, Init.Nat.add x y = Nat.add x y). eauto. Qed.
Ltac nat_without_assoc := 
    pose proof Nat.add_comm;
    pose proof Nat.add_0_r;
    pose proof add_rec;
    pose proof init_st;
    pose proof st_init.

Notation "'consider' t" := (True = represent t) (at level 200).
(*|
.. raw:: latex

    The experience of writing proofs in Coq is heavily conditioned by the amount and the quality of proof automations already available or easily assembled for the domain one is tackling.

    For example, Coq has excellent support for Linear Integer Arithmetic with the tactic \verb|lia|, and when one is facing goals involving simple arithmetic equations, 
    we can often trust \verb|lia| to automatically discharge the goals very efficiently: taking a reasonable amount of time and producing.

    \section{Statement of the problem}
    Let's consider a setup in which we are working with Coq's list. For example, in our setup a queue specification primitive module is using a list internally.

    Proof of programs using list will often require us to the standard facts on list. For example, if we only use the function \verb|length| and manipulate list,
    we will often need to use the following facts from the standard library.

.. coq:: unfold 
|*)

Check app_nil_r. (* .noin *)
Check app_nil_l. (* .noin *)
Check app_assoc. (* .noin *)
Check cons_app. (* .noin *)
Check app_length. (* .noin *)
Check length_cons. (* .noin *)


(*|
.. raw:: latex

    When doing verification in Coq it is common to face subgoals which are
    following simply from such reasonably small set of fundamental theorems on the
    underlying datastructures.

.. coq:: .none 
|*)

Goal forall m, exists l,  1 :: l ++ [4] = [1;2;3] ++ m ++ [4].
    intros.
    eexists.

    pose_prop_lemmas.
    list_lemmas.
    egg_search_evars 4.
    egg_repeat.
    Qed.

Goal forall m, exists l, length l = (3 + (length m))%nat /\ 1 :: l ++ [4]= ([1;2;3;7] ++ m) ++ [4].
    intros.
    eexists.
    pose_prop_lemmas.
    list_lemmas.
    add_subterms_goal.
    Time egg_search_evars 4.
    egg_repeat.
    Qed.

Goal forall m, exists l, length l = (5 + (length m))%nat /\ 1 :: l ++ [4]= ([1;2;4;5;6;7] ++ m) ++ [4].
    intros.
    eexists.
    pose_prop_lemmas.
    list_lemmas.
    add_subterms_goal.
    Time egg_search_evars 4.
    Time egg_simpl_goal 4.
    eauto.
    eauto.
    simpl; eauto.
    Qed.

Goal forall e j m, exists l, length l = (2 + (length m))%nat /\ 1 :: l ++ [4]= (1::[e] ++ m) ++ [j;4].
    intros.
    eexists.
    pose_prop_lemmas.
    list_lemmas.
    nat_without_assoc.
    add_subterms_goal.
    egg_search_evars 5.
    egg_repeat.
    Qed.

(*|
.. raw:: latex

    Note the danger of adding arbitrary rewrites. For example if we the introduce the following theorem,
    in the presence of the commutativity of addition, we are running into trouble.     
|*)
Check app_length_r. (* .noin *)
(* Disappointing case: *)
Goal exists (l w : nat),  l = O /\ w = (l + w)%nat.
    intros.
    eexists.
    eexists.
    pose_prop_lemmas.
    list_lemmas.
    nat_without_assoc.
    add_subterms_goal.
    (* Needs a trigger *)
    assert (forall x y, y = y -> x = x -> consider (y + x)%nat) by (simpl; intros; reflexivity).
    Time egg_search_evars 5.
    egg_repeat.
    Qed.

Axiom lset : forall {A:Type} (l : list A) (n:nat) (ne : A), list A.
Axiom set_ax : forall {A: Type} (l r : list A) (e ne : A), 
    lset (l ++ [e] ++ r) (length l) ne = (l ++ [ne] ++ r).
Ltac list_getset :=
    pose proof @set_ax.

Goal forall (l1 l2 : list N) (x y : N) (j : nat),
   j = (length l1 + length l1)%nat ->
   (lset (l1 ++ (l1 ++ [x] ++ l2) ++ [1;2]) j y) = (l1 ++ l1 ++ [x] ++ l2 ++ [1;2]).
   list_getset.
    pose_prop_lemmas.
    list_lemmas.
    nat_without_assoc.
    intros.
    egg_repeat; simpl.
    (* Oh nooo it does not work, but it did simplify! *)
    Abort.

Goal forall (l1 l2 : list N) (x y : N) (j : nat),
   j = (length l1 + length l1)%nat ->
    x =y ->
   (lset (l1 ++ (l1 ++ [x] ++ l2) ++ [1;2]) j y) = (l1 ++ l1 ++ [x] ++ l2 ++ [1;2]).
   list_getset.
    pose_prop_lemmas.
    list_lemmas.
    nat_without_assoc.
    intros.
    egg_repeat4.
    (* Now it works *)
    Qed.

(* Fancier *)
Goal forall (l1 l2 l3 : list N) (x y w: N) (j : nat),
   j = (length l1 +  length l3 + 1)%nat ->
   lset (lset (l1 ++ [w] ++ (l3 ++ [x] ++ l2) ++ [1;2]) j y) (length l1) y = (l1 ++ [y] ++ l3 ++ [y] ++ l2 ++ [1;2]).
   list_getset.
    pose_prop_lemmas.
    list_lemmas.
    nat_without_assoc.
    pose proof Nat.add_assoc.
    intros.
    egg_simpl_goal 4.
    simpl.
    egg_simpl_goal 4.
    (* Now it works *)
    eauto. simpl;eauto.
    Qed.

(* (x = T -> ite T tb fb) -> (x = F -> ite x tb fb) -> (ite x tb fb)  *)

(* Alternative simplification: *)
Goal forall (l1 l2 l3 : list N) (x y w: N) (j : nat),
   j = (length l1 +  length l3 + 1)%nat ->
   lset (lset (l1 ++ [w] ++ (l3 ++ [x] ++ l2) ++ [1;2]) j y) (length l1) y = (l1 ++ [y] ++ l3 ++ [y] ++ l2 ++ [1;2]).
   list_getset.
    pose_prop_lemmas.
    list_lemmas.
    nat_without_assoc.
    pose proof Nat.add_assoc.
    intros.
    egg_simpl_goal 4.
    simpl.
    egg_simpl_goal 4.
    (* Now it works *)
    eauto. simpl;eauto.
    Qed.


(* Exemple de simplification (eliminer un identifieur) *)

(*|
.. raw:: latex

    As one can see, all those theorems are of the form:
        $$\forall v_0, \dots, v_k, hyp_1 \rightarrow \dots hyp_n \rightarrow clc $$ 
    Where all the hypotheses $hyp_j$ and the conclusion $clc$ are of one two forms:
   
    \begin{itemize}
    \item An equality between two terms that depends on a subset of the variables $v_i$
    \item A logical predicate that depends on a subset of the variable $v_i$
    \end{itemize}
 
    
    \section{Congruences: representing facts in e-graphs}
    \paragraph{Representing types}
    \paragraph{Status of equality}
    \paragraph{Dangerous set of theorems}
    \paragraph{Simplification of goal versus resolution}
    % Find an example where it would be tricky to resolve, but much easier
    % Something that occurs in real world?
    Coq theoretically does have a support for such systems using the autorewrite tactic, aimed at solving the goal. 


    \paragraph{The importance of automation}
    Let's consider that we are trying working with lists in Coq. As expected a bunch of theorem hold on. 

    \paragraph{Goals are rarely living squarely into a nice fragment}

    \paragraph{Extensibility}
        skip filter drop rev

   \paragraph{The mountain analogy}

   \paragraph{Commmutative goals}
.. coq:: unfold 
|*)

