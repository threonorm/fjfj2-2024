Require Import Lia.
Require Import String.
Require Import NArith.

Require Import LangFjfj2.
Require Import Indexification.
Require Import FjfjParsing.
Require Import List.

Local Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Require Import Fifo. 
Require FifoSpec.
Require Import Coq.Logic.PropExtensionality.
Require Import egg.Egg.
Require Import egg.Loader.
Require Import Tactics. 
Require Import TransitionNotation.

Section Correctness2.
  Open Scope N.
  Import ListNotations.
  Definition wf (ist : SModule) := exists (v d:N), ist = *[| v ; d |]*.
  Arguments wf /.

  Inductive phi : forall (ist sst : SModule), Prop :=
  (* The following inductive predicate is boilerplate, could be generated using MetaCoq. *)
    | flushed : forall (d : N), phi *[| 0; d |]* *( [] : list N )* 
    | enq : forall (ist sst  : N -> SModule) (prev_ist prev_sst : SModule), 
      indistinguishable (Fifo1Fjfj.mkFifo1) (FifoSpec.FifoSpec.mkFifoSpec) prev_ist prev_sst ->
      (* all the fibers are the actual parametrization of the state, polymorphically *)
      (forall x, 
      phi (ist x) (sst x) /\ wf (ist x) /\ wf prev_ist /\
      (prev_ist --{{Fifo1Fjfj.mkFifo1 enq (x) }}--> (ist x)) /\
      (prev_sst --{{FifoSpec.FifoSpec.mkFifoSpec enq (x) }}--> (sst x))) ->
      phi prev_ist prev_sst
    | deq : forall (ist sst : N -> SModule) (prev_ist prev_sst : SModule), 
      indistinguishable (Fifo1Fjfj.mkFifo1) (FifoSpec.FifoSpec.mkFifoSpec) prev_ist prev_sst ->
      (* all the fibers are the actual parametrization of the state, polymorphically *)
      (forall x, 
      phi (ist x) (sst x) /\ wf (ist x) /\ wf prev_ist /\
      (prev_ist --{{Fifo1Fjfj.mkFifo1 deq (x) }}--> (ist x)) /\
      (prev_sst --{{FifoSpec.FifoSpec.mkFifoSpec deq (x) }}--> (sst x))) ->
      phi prev_ist prev_sst 
      .

  Definition related2 (ist : SModule) (sst : SModule) := 
      (exists (v d : N) (opt_a : list N), 
        ist = *[| v ; d|]* /\ sst = *( opt_a )* /\
        phi ist sst).
  Arguments related2 ist sst/.
  Import Fifo1Fjfj.
  Require Import ListTheory.

  Theorem related_implies_indistinguishable : forall ist sst, related2 ist sst -> 
          indistinguishable (Fifo1Fjfj.mkFifo1) (FifoSpec.FifoSpec.mkFifoSpec) ist sst.
    intros ist sst. 
    cbn; light_clean_propagate; print_arrays.
    identify_modules.
    match goal with
    | [ H: phi ?ist ?sst |- _] => induction  H
    end.
    prove_indistinguishable; light_clean_propagate; symb_ex_split.
    pose_list_lemmas.
    assert (forall (l : list N), l=l -> represent  *(l)* ) by (intros;easy).
    rm_existentials.
    solve_easy_evars.
    eauto.
    eauto.
  Qed.

  Definition lock_step {smi sms} (impl : module smi) (spec : module sms) (n : nat) (phi  : SModule -> SModule -> Prop) (si ss : SModule):=
    match n with 
    | 0%nat => forall x ei , 
                (si --{{ impl enq ( x ) }}--> ei) -> 
                exists es, (ss --{{ spec enq ( x ) }}--> es) /\ phi ei es
    | 1%nat => forall x ei , 
                (si --{{ impl deq (x) }}--> ei) -> 
                exists es, (ss --{{ spec deq (x) }}--> es) /\ phi ei es
    | _ => True 
    end .
    
  Arguments lock_step {smi sms} impl spec !n phi si ss/.
  Ltac fiberize_goal x := 
    match goal with 
    | [ |- _ ?i ?s]  =>
      match i with 
      | context l [x] => 
        match s with 
        | context r [x] =>
          let fi := constr:(fun x => ltac:(let g := context l[x] in exact g)) in
          let fs := constr:(fun x => ltac:(let g := context r[x] in exact g)) in
          change (phi (fi x) (fs x))
        end
      end
    end.

  (* TODO add support for equality between functions to derive other stuff. *)
  (* TODO, add support for absurd cases when finding existential variables? *)
  (* TODO add support for utf8 in Coquetier *)
  (* TODO Find a way to make it work with hihgher order functions.*)
  (* TODO investigates why higher order function break the tactic symb_ex_split *)
  Theorem related_preserved : forall ist sst, related2 ist sst -> 
        forall n, lock_step (Fifo1Fjfj.mkFifo1) (FifoSpec.FifoSpec.mkFifoSpec) n related2 ist sst.
    cbn; light_clean_propagate; print_arrays.
    generalize dependent n.
    match goal with
    | [ H: phi ?ist ?sst |- _] =>
      remember ist; remember  sst; induction  H; intros
    end.
    {
      (* Flushed *)
      destruct n; simpl; intros.
      + 
        light_clean_propagate; symb_ex_split.
        extract_equality H1 1%nat 1%nat.
        light_clean_propagate.
        rm_existentials.
        split; eauto.
        rm_existentials; split; eauto.
        wrapped_arrays_equal 2%nat.
        split; eauto.
        assert (nxt_st = [|1; x|]) by custom_eq_array 2%nat.
        light_clean_propagate.
        fiberize_goal x.
        eapply (Correctness2.deq).
        prove_indistinguishable; light_clean_propagate; symb_ex_split; try solve_easy_evars.
        {
        (* Only new for the fancier spec  *)
          pose_list_lemmas.
          assert (forall (l : list N), l=l -> represent  *(l)* ) by (intros;easy).
          rm_existentials.
          solve_easy_evars.
        }

        intros.
        split.
        eapply Correctness2.flushed.
        split;eauto.
        simpl; rm_existentials.
        wrapped_arrays_equal 2%nat.
        split;eauto.
        simpl; rm_existentials.
        wrapped_arrays_equal 2%nat.
        split;eauto.
        simpl.
        rm_existentials. 
        split; eauto.
        split;eauto.
        split.
        eapply DIft;
        reconstruct_wpa.
        all: try solve[reconstruct_step; simpl; eauto].
        apply_log_fn 2%nat.
      +
        destruct n; simpl; intros.
        light_clean_propagate; symb_ex_split.
        eauto.
    }
    {
      (* Enqueue *)
      light_clean_propagate.
      destruct n; simpl; intros.
      + 
        pose proof (H0 x).
        clear H0.
        light_clean_propagate; symb_ex_split.
        rm_existentials.
        split; eauto.
        rm_existentials; split; eauto.
        wrapped_arrays_equal 2%nat.
        split; eauto.
        assert ( [| 1; x  |] = nxt_st0) as  insight.
        custom_eq_array 2%nat.
        light_clean_propagate; eauto.
      +
        destruct n; simpl; intros.
        pose proof (H0 x).
        clear H0.
        light_clean_propagate; symb_ex_split.
        eauto.
    }
    {
      (* Deq *)
      simpl in *.
      light_clean_propagate.
      destruct n; simpl; intros.
      + 
        pose proof (H0 x).
        clear H0; 
        light_clean_propagate;symb_ex_split.
      +
        destruct n; simpl; intros; eauto.
        pose proof (H0 x).
        clear H0.
        light_clean_propagate; symb_ex_split.
        rm_existentials.
        split; eauto.
        rm_existentials; split; eauto.
        wrapped_arrays_equal 2%nat.
        split; eauto.
        assert ( [| 0; d1  |] = nxt_st0).
        custom_eq_array 2%nat.
        light_clean_propagate.
        eauto.
    }
    Time Qed.

  (* For the following proof we never want to open the invariant,
   everything should be structural, there is nothing specific to that design here. *)
  Arguments related2 ist sst : simpl never.
  Theorem correct_against_1 : refines (Fifo1Fjfj.mkFifo1) (FifoSpec.FifoSpec.mkFifoSpec) related2.
  prove_refinement.
      {
        pose proof related_preserved as lem. 
        specialize (lem) with (1:= related_i_s) (n:= 0%nat).
        simpl in lem.
        specialize (lem) with (1:= init2mid_i).
        light_clean_propagate.
        rm_existentials.
        simpl.
        split; eauto.
        split. eapply existSR_done.
        split; eauto.
        eapply related_implies_indistinguishable; eauto.
      }
      {
        pose proof related_preserved as lem. 
        specialize (lem) with (1:= related_i_s) (n:= 1%nat).
        simpl in lem.
        specialize (lem) with (1:= init2mid_i).
        light_clean_propagate.
        rm_existentials.
        simpl.
        split; eauto.
        split. eapply existSR_done.
        split; eauto.
        eapply related_implies_indistinguishable; eauto.
      }
      Time Qed.
End Correctness2.