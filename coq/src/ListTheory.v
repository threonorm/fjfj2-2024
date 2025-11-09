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


Lemma app_assoc_r :  forall (A : Type) (l m n : list A),
    (l ++ m) ++ n = l ++ m ++ n .
    intros.
    erewrite <- app_assoc; eauto.
    Qed.

Lemma app_length_r : forall (A : Type) (l l' : list A),
        (length l + length l')%nat = length (l ++ l').
        intros; erewrite app_length; eauto.
Qed.

Definition represent {A:Type} (a:A) := True.

Theorem trigger_length : forall (A : Type) (l: list A), 
    l = l -> True = represent (length l).
    eauto.
Qed.

Theorem app_nil_l' : forall (A : Type) (l : list A), l = [] ++ l .
    intros; erewrite app_nil_l. eauto.
Qed.

Theorem app_nil_r' : forall (A : Type) (l : list A), l = l ++ [] .
    intros; erewrite app_nil_r. eauto.
Qed.
Ltac pose_list_lemmas :=
 pose proof app_nil_r;
 pose proof app_nil_l;
 pose proof app_nil_r';
 pose proof app_nil_l';
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