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


Section Correctness.
  Open Scope N.
  Import ListNotations.
  Definition related (ist : SModule) (sst : SModule) := 
      (exists (v d : N) (opt_a : option N), 
        ist = *[| v ; d|]* /\ 
        sst = *( opt_a )* /\
        (forall a, opt_a = Some a -> v = 1 /\ d = a) /\
        (forall a, v = 1 /\ d = a -> opt_a = Some a) /\
        (opt_a = None <-> v = 0)).
  Arguments related / ist sst.

  Import Fifo1Fjfj.
  Ltac t' :=
    match goal with 
    | [H : aget ?x ?n = ?a, H' : aget ?x ?n = ?b |- _] =>
      assert (a = b) by (rewrite <- H, H'; try reflexivity)
      end.

  Theorem correct_against_1s : refines (Fifo1Fjfj.mkFifo1) (FifoSpec.Fifo1Spec.mkFifo1) related.
  prove_refinement.
      {
          clear indistinguishable_i_s.
          simpl in related_i_s.
          cleanup.
          min_straight_line.
          simpl_applylog.
          repeat clean_arith.
          clean_propagate; cbn in *.
          print_arrays.

          do 2 eexists.
          split.
          { crush. }
          split.
          { eapply existSR_done. }
          split.
          { 
            repeat eexists; try crush.
            wrapped_arrays_equal 2%nat.
            PropLemmas.pose_lemmas; egg_repeat.
          }
          {
            prove_state_simulation;
            symb_ex_split.
            all: simpl; eauto 6.
            assert (n = arg_method).
            PropLemmas.pose_lemmas;  egg_repeat.
            eauto.
            assert (0 = 1).
            PropLemmas.pose_lemmas;  egg_repeat.
            lia.
          }
      }
      {
          clear indistinguishable_i_s.
          simpl in related_i_s.
          clean_propagate.
          straight_line; simpl_applylog; repeat clean_arith.
          clean_propagate; cbn in *.
          repeat match goal with 
              | [H: context[empty_Alog] |- _] =>
              clear H
              | [H: context[empty_Vlog] |- _] =>
              clear H
              end.
          assert (exists a, opt_a = Some a).
          existential_egg.
          repeat add_eq_refl_True; PropLemmas.pose_lemmas; 
          egg_repeat.
          clean_propagate.
          

          do 2 eexists.
          split.
          { crush. }
          split.
          { eapply existSR_done. }
          split.
          { 
            exists (0%N).
            exists (a).
            eexists.
            split.
            2:{
              crush.
            }
            { wrapped_arrays_equal 2%nat; 
              PropLemmas.pose_lemmas; egg_repeat.
            }
          }
          {
          prove_indistinguishable;
              clean_propagate; straight_line; clean_arith; t';
              crush.
         }
      }
      Unshelve.
      exact 0%N.
      Time Qed.
End Correctness.

Section Correctness2.
  Open Scope N.
  Import ListNotations.
  Definition wf (ist : SModule) := exists (v d:N), ist = *[| v ; d |]*.
  Arguments wf /.

  Inductive phi : forall (ist sst : SModule), Prop :=
  (* The following inductive predicate is boilerplate, could be generated using MetaCoq. *)
    | flushed : forall (d : N), phi *[| 0; d |]* *( None : option N )* 
    | enq : forall (ist sst prev_ist prev_sst : N -> SModule) (x : N), 
      indistinguishable (Fifo1Fjfj.mkFifo1) (FifoSpec.Fifo1Spec.mkFifo1) (prev_ist x) (prev_sst x) ->
      (* all the fibers are the actual parametrization of the state, polymorphically *)
      (forall x, 
      phi (ist x) (sst x) /\ wf (ist x) /\ wf (prev_ist x) /\
      ((prev_ist x) --{{Fifo1Fjfj.mkFifo1 enq (x) }}--> (ist x)) /\
      ((prev_sst x) --{{FifoSpec.Fifo1Spec.mkFifo1 enq (x) }}--> (sst x))) ->
      phi (prev_ist x) (prev_sst x) 
    | deq : forall (ist sst prev_ist prev_sst : N -> SModule) (x : N), 
      indistinguishable (Fifo1Fjfj.mkFifo1) (FifoSpec.Fifo1Spec.mkFifo1) (prev_ist x) (prev_sst x) ->
      (* all the fibers are the actual parametrization of the state, polymorphically *)
      (forall x, 
      phi (ist x) (sst x) /\ wf (ist x) /\ wf (prev_ist x) /\
      ((prev_ist x) --{{Fifo1Fjfj.mkFifo1 deq (x) }}--> (ist x)) /\
      ((prev_sst x) --{{FifoSpec.Fifo1Spec.mkFifo1 deq (x) }}--> (sst x))) ->
      phi (prev_ist x) (prev_sst x).

  Definition related2 (ist : SModule) (sst : SModule) := 
      (exists (v d : N) (opt_a : option N), 
        ist = *[| v ; d|]* /\ sst = *( opt_a )* /\
        phi ist sst).
  Arguments related2 ist sst/.
  Import Fifo1Fjfj.

  Theorem related_implies_indistinguishable : forall ist sst, related2 ist sst -> 
          indistinguishable (Fifo1Fjfj.mkFifo1) (FifoSpec.Fifo1Spec.mkFifo1) ist sst.
    intros ist sst.
    cbn; light_clean_propagate; print_arrays.
    identify_modules.
    match goal with
    | [ H: phi ?ist ?sst |- _] => remember ist; remember  sst; induction  H
    end.
    2-3: eauto.
    prove_indistinguishable; light_clean_propagate; symb_ex_split.
    solve_easy_evars.
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
  (* TODO add support for absurd cases when finding existential variables? *)
  (* TODO add support for utf8 in Coquetier *)
  (* TODO Find a way to make it work with hihgher order functions.*)
  (* TODO investigates why higher order function break the tactic symb_ex_split *)
  Theorem related_preserved : forall ist sst, related2 ist sst -> 
        forall n, lock_step (Fifo1Fjfj.mkFifo1) (FifoSpec.Fifo1Spec.mkFifo1) n related2 ist sst.
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
        reconstruct_wpa.
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
      pose proof (H0 x).
      light_clean_propagate.
      destruct n; simpl; intros.
      + 
        pose proof (H0 x0).
        clear H0.
        light_clean_propagate; symb_ex_split.
        rm_existentials.
        split; eauto.
        rm_existentials; split; eauto.
        wrapped_arrays_equal 2%nat.
        split; eauto.
        assert ( [| 1; x0  |] = nxt_st0) as  insight.
        custom_eq_array 2%nat.
        light_clean_propagate; eauto.
      +
        destruct n; simpl; intros.
        light_clean_propagate; symb_ex_split.
        eauto.
    }
    {
      (* Deq *)
      simpl in *.
      pose proof (H0 x).
      light_clean_propagate.
      destruct n; simpl; intros.
      + 
        clear H0; light_clean_propagate;symb_ex_split.
      +
        destruct n; simpl; intros; eauto.
        pose proof (H0 x0).
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
    Qed.

  (* For the following proof we never want to open the invariant,
   everything should be structural, there is nothing specific to that design here. *)
  Arguments related2 ist sst : simpl never.
  Theorem correct_against_1 : refines (Fifo1Fjfj.mkFifo1) (FifoSpec.Fifo1Spec.mkFifo1) related2.
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

Section Correctness3.
  Import Fifo2NonDet.

  Inductive phi' : forall (ist sst : SModule), Prop :=
  (* The following inductive predicate is boilerplate, could be generated using MetaCoq. *)
    | f : phi' *( (nil : list bool) )* *( (nil : list unit) )* 

    (* | e : forall (ist sst prev_ist prev_sst : SModule),
      indistinguishable (Fifo2NonDet.mkFifo2) (FifoSpec.Fifo2Spec.mkFifo2) prev_ist prev_sst /\
      (* all the fibers are the actual parametrization of the state, polymorphically *)
      (forall x (ist : N -> SModule),
      (prev_ist --{{ Fifo2NonDet.mkFifo2 enq (x) }}--> (ist x)) /\
      (prev_sst --{{ FifoSpec.Fifo2Spec.mkFifo2 enq (x) }}--> sst) /\ phi' (ist x) sst) ->
      phi' prev_ist prev_sst *)

    (* | eTrue : forall (ist sst prev_ist prev_sst : SModule) (x : N),
      indistinguishable (Fifo2NonDet.mkFifo2) (FifoSpec.Fifo2Spec.mkFifo2) prev_ist prev_sst /\
      (* all the fibers are the actual parametrization of the state, polymorphically *)
      (exists (l : list bool) (b : bool), prev_ist = *( l )* /\ ist = ( (true :: nil) ++ l )) /\
      (prev_sst --{{FifoSpec.Fifo2Spec.mkFifo2 enq (x) }}--> sst) /\ phi' ist sst ->
      phi' prev_ist prev_sst
    | eFalse : forall (ist sst prev_ist prev_sst : SModule) (x : N),
      indistinguishable (Fifo2NonDet.mkFifo2) (FifoSpec.Fifo2Spec.mkFifo2) prev_ist prev_sst /\
      (* all the fibers are the actual parametrization of the state, polymorphically *)
      (exists (l : list bool) (b : bool), prev_ist = *( l )* /\ ist = ( (false :: nil) ++ l )* /\
      (prev_sst --{{FifoSpec.Fifo2Spec.mkFifo2 enq (x) }}--> sst) /\ phi' ist sst ->
      phi' prev_ist prev_sst  *)
    (* unfold all possible outcomes *)

    | e : forall (ist1 ist2 sst prev_ist prev_sst : SModule) (x : N),
      indistinguishable (Fifo2NonDet.mkFifo2) (FifoSpec.Fifo2Spec.mkFifo2) prev_ist prev_sst /\
      (* all the fibers are the actual parametrization of the state, polymorphically *)
      (exists (l : list bool), prev_ist = *( l )* /\ (ist1 = *( Fifo2NonDet.enq' false l )* /\ ist2 = *( Fifo2NonDet.enq' true l )*)) /\
      (prev_sst --{{ FifoSpec.Fifo2Spec.mkFifo2 enq (x) }}--> sst) /\ phi' ist1 sst /\ phi' ist2 sst ->
      phi' prev_ist prev_sst
    | eCompact : forall (ist : bool -> SModule) (sst prev_ist prev_sst : SModule) (x : N),
      indistinguishable (Fifo2NonDet.mkFifo2) (FifoSpec.Fifo2Spec.mkFifo2) prev_ist prev_sst /\
      (* all the fibers are the actual parametrization of the state, polymorphically *)
      (forall (b : bool),
      (* ist is defined to be a function of the boolean so it's not limited by the scope *)
      (* otherwise ist can't be instatiated to anything containing b *)
      (exists (l : list bool), prev_ist = *( l )* /\ ist b = *( Fifo2NonDet.enq' b l )*) /\
      (prev_sst --{{ FifoSpec.Fifo2Spec.mkFifo2 enq (x) }}--> sst) /\ phi' (ist b) sst) ->
      phi' prev_ist prev_sst
    | eFolded : forall (ist : bool -> SModule) (sst prev_ist prev_sst : SModule) (x : N),
      indistinguishable (Fifo2NonDet.mkFifo2) (FifoSpec.Fifo2Spec.mkFifo2) prev_ist prev_sst /\
      (* all the fibers are the actual parametrization of the state, polymorphically *)
      (forall (b : bool),
      (* ist is defined to be a function of the boolean so it's not limited by the scope *)
      (* otherwise ist can't be instatiated to anything containing b *)
      (exists (l : list bool), ist b = *( Fifo2NonDet.enq' b l )* /\ (prev_ist --{{ Fifo2NonDet.mkFifo2 enq (x) }}--> (ist b))) /\
      (prev_sst --{{ FifoSpec.Fifo2Spec.mkFifo2 enq (x) }}--> sst) /\ phi' (ist b) sst) ->
      phi' prev_ist prev_sst
    | d : forall (ist sst : SModule) (prev_ist prev_sst : SModule) (x : N), 
      indistinguishable (Fifo2NonDet.mkFifo2) (FifoSpec.Fifo2Spec.mkFifo2) prev_ist prev_sst /\
      (* all the fibers are the actual parametrization of the state, polymorphically *)
      (prev_ist --{{ Fifo2NonDet.mkFifo2 deq (x) }}--> ist) /\
      (prev_sst --{{ FifoSpec.Fifo2Spec.mkFifo2 deq (x) }}--> sst) /\ phi' ist sst ->
      phi' prev_ist prev_sst.

  Print phi'_ind.

  Definition ind : forall (P : state_t -> state_t -> Prop)
  (f : P *( nil : list bool )* *( nil : list unit )*)
  (f0 : forall (ist1 ist2 sst prev_ist prev_sst : state_t) (x : N),
	    indistinguishable mkFifo2 FifoSpec.Fifo2Spec.mkFifo2 prev_ist
          prev_sst /\
        (exists l : list bool,
           prev_ist = *( l )* /\
           ist1 = *( enq' false l )* /\ ist2 = *( enq' true l )*) /\
        match index_of "enq" action_methods 0 with
        | Some x0 => aget (action_spec FifoSpec.Fifo2Spec.mkFifo2) x0 x
        | None => unexisting_rule
        end (prev_sst : state_t) (sst : state_t) /\
        phi' ist1 sst /\ phi' ist2 sst /\ P ist1 sst /\ P ist2 sst -> P prev_ist prev_sst)
  (f1 : forall (ist : bool -> state_t) (sst prev_ist prev_sst : state_t)
          (x : N),
        indistinguishable mkFifo2 FifoSpec.Fifo2Spec.mkFifo2 prev_ist
          prev_sst /\
        (forall b : bool,
         (exists l : list bool, prev_ist = *( l )* /\ ist b = *( enq' b l )*) /\
         match index_of "enq" action_methods 0 with
         | Some x0 => aget (action_spec FifoSpec.Fifo2Spec.mkFifo2) x0 x
         | None => unexisting_rule
         end (prev_sst : state_t) (sst : state_t) /\ 
         phi' (ist b) sst /\ P (ist b) sst) -> P prev_ist prev_sst)
  (f2 : forall (ist : bool -> state_t) (sst prev_ist prev_sst : state_t)
          (x : N),
        indistinguishable mkFifo2 FifoSpec.Fifo2Spec.mkFifo2 prev_ist
          prev_sst /\
        (forall b : bool,
         (exists l : list bool,
            ist b = *( enq' b l )* /\
            match index_of "enq" action_methods 0 with
            | Some x0 => aget (action_spec mkFifo2) x0 x
            | None => unexisting_rule
            end (prev_ist : state_t) (ist b : state_t)) /\
         match index_of "enq" action_methods 0 with
         | Some x0 => aget (action_spec FifoSpec.Fifo2Spec.mkFifo2) x0 x
         | None => unexisting_rule
         end (prev_sst : state_t) (sst : state_t) /\ 
         phi' (ist b) sst /\ P (ist b) sst) -> P prev_ist prev_sst)
  (f3 : forall (ist sst prev_ist prev_sst : state_t) (x : N),
        indistinguishable mkFifo2 FifoSpec.Fifo2Spec.mkFifo2 prev_ist
          prev_sst /\
        match index_of "deq" action_methods 0 with
        | Some x0 => aget (action_spec mkFifo2) x0 x
        | None => unexisting_rule
        end (prev_ist : state_t) (ist : state_t) /\
        match index_of "deq" action_methods 0 with
        | Some x0 => aget (action_spec FifoSpec.Fifo2Spec.mkFifo2) x0 x
        | None => unexisting_rule
        end (prev_sst : state_t) (sst : state_t) /\ 
        phi' ist sst /\ P ist sst -> P prev_ist prev_sst), forall (ist sst : SModule), phi' ist sst -> P ist sst.
  Admitted.

  Definition related3 (ist : SModule) (sst : SModule) := 
    phi' ist sst /\
    (exists (l : list bool) (l' : list unit), 
      ist = *( l )* /\ 
      sst = *( l' )*).
  Arguments related3 / ist sst.

  Ltac prove_precond H :=
    match type of H with
      | ?a -> ?b =>
        let newname := fresh in
        assert a as newname; [ | specialize (H newname)]; cycle 1
      end.

  Theorem phi_implies_indistinguishable : forall (ist sst : SModule), phi' ist sst -> indistinguishable (Fifo2NonDet.mkFifo2) (FifoSpec.Fifo2Spec.mkFifo2)ist sst.
  Admitted.
  (* Proof.
    intros.
    induction H using ind.
    {
      prove_indistinguishable.
      {
        rm_existentials.
        simpl.
        unfold FifoSpec.Fifo2Spec.enq.
        rm_existentials.
        split; eauto.
      }
      {
        unfold deq in impl_am_call.
        light_clean_propagate.
        apply (f_equal (@length bool)) in H0.
        rewrite last_length in H0.
        simpl in H0.
        lia.
      }
    }
    {
      light_clean_propagate.
      prove_indistinguishable.
      {
        unfold enq in impl_am_call.
        light_clean_propagate.
        simpl.
        unfold FifoSpec.Fifo2Spec.enq in HA1.
        light_clean_propagate.
        unfold FifoSpec.Fifo2Spec.enq.
        rm_existentials.
        split; eauto.
      }
      {
        unfold deq in impl_am_call.
        light_clean_propagate.
        unfold indistinguishable in HA.
        cleanup.
        specialize (H0 0 1%nat ( l0 )).
        simpl in H0.
        unfold deq in H0.
        prove_precond H0.
        2:{
          rm_existentials.
          split; eauto.
        }
        unfold FifoSpec.Fifo2Spec.deq in H0.
        light_clean_propagate.
        simpl.
        unfold FifoSpec.Fifo2Spec.deq.
        rm_existentials.
        split; eauto.
      }
    }
    {
      light_clean_propagate.
      prove_indistinguishable.
      {
        unfold FifoSpec.Fifo2Spec.deq in HA1.
        light_clean_propagate.
        simpl.
        unfold FifoSpec.Fifo2Spec.enq.
        rm_existentials.
        split; eauto.
      }
      {
        unfold FifoSpec.Fifo2Spec.deq in HA1.
        light_clean_propagate.
        simpl.
        unfold FifoSpec.Fifo2Spec.deq.
        rm_existentials.
        split; eauto.
      }
    }
  Qed. *)

  Theorem relation_preserved : forall init_i init_s, related3 init_i init_s ->
      forall i, lock_step (Fifo2NonDet.mkFifo2) (FifoSpec.Fifo2Spec.mkFifo2) i phi' init_i init_s.
  Proof.
    simpl.
    intros init_i init_s H.
    inversion H.
    clear H.
    induction H0 using ind.
    {
      intros.
      unfold lock_step.
      destruct i.
      {
        simpl.
        intros.
        unfold enq in H.
        light_clean_propagate.
        rm_existentials.
        unfold FifoSpec.Fifo2Spec.enq.
        split.
        rm_existentials.
        split; eauto.
        eapply d.
        split.
        {
          prove_indistinguishable.
          {
            unfold enq in impl_am_call.
            light_clean_propagate.
            rm_existentials.
            simpl.
            unfold FifoSpec.Fifo2Spec.enq.
            rm_existentials.
            split; eauto.
          }
          {
            unfold deq in impl_am_call.
            light_clean_propagate.
            rm_existentials.
            simpl.
            unfold FifoSpec.Fifo2Spec.deq.
            rm_existentials.
            split; eauto.
            instantiate (1 := nil).
            eauto.
          }
        }
        simpl.
        unfold deq.
        split.
        rm_existentials.
        split; [ | eauto].
        instantiate (1 := b).
        instantiate (1 := nil).
        eauto.
        unfold FifoSpec.Fifo2Spec.deq.
        split.
        rm_existentials.
        split; eauto.
        instantiate (1 := nil).
        eauto.
        eapply f.
      }
      destruct i.
      {
        simpl.
        intros.
        unfold deq in H.
        light_clean_propagate.
        apply (f_equal (@length bool)) in H1.
        rewrite last_length in H1.
        simpl in H1.
        lia.
      }
      eauto.
    }
    (* enq *)
    {
      intros.
      unfold lock_step.
      destruct i.
      {
        simpl.
        intros.
        unfold enq in H0.
        light_clean_propagate.
        unfold FifoSpec.Fifo2Spec.enq in HA1.
        light_clean_propagate.
        rm_existentials.
        unfold FifoSpec.Fifo2Spec.enq.
        split.
        rm_existentials.
        split; eauto.
        simpl.
        destruct b; eauto.
      }
      destruct i.
      {
        simpl.
        intros. 
        unfold deq in H0.
        light_clean_propagate.
        unfold FifoSpec.Fifo2Spec.deq.
        unfold indistinguishable in HA.
        cleanup.
        pose proof (H0 0 1%nat *( l0 )*).
        simpl in H1.
        unfold deq in H1.
        prove_precond H1.
        2:{
          rm_existentials.
          split; eauto.
        }
        unfold FifoSpec.Fifo2Spec.deq in H1.
        light_clean_propagate.
        unfold FifoSpec.Fifo2Spec.enq in HA1.
        light_clean_propagate.
        rm_existentials.
        split.
        rm_existentials.
        split; eauto.
        eapply e.
        split.
        {
          prove_indistinguishable.
          {
            unfold enq in impl_am_call.
            light_clean_propagate.
            rm_existentials.
            simpl.
            unfold FifoSpec.Fifo2Spec.enq.
            rm_existentials.
            split; eauto.
          }
          (* having the lower right corner being related *)
          (* but enq in the bottom allows more methods to be called *)
          {
            unfold deq in impl_am_call.
            light_clean_propagate.
            prove_precond HA4.
            2:{
              rm_existentials.
              split; eauto.
            }
            light_clean_propagate.
            specialize (HA4 1%nat).
            unfold lock_step in HA4.

            pose proof (HA4 0 *( false :: (l0 ++ b1 :: nil) )*).
            
            simpl in H1.
            unfold deq in H1.
            prove_precond H1.
            2:{
              rm_existentials.
              split; eauto.
              instantiate (1 := b).
              eauto.
            }
            light_clean_propagate.
            unfold FifoSpec.Fifo2Spec.deq in HA0.
            light_clean_propagate.
            rewrite app_comm_cons in H4.
            apply app_inj_tail in H4.
            light_clean_propagate.
            apply phi_implies_indistinguishable in HB1.
            unfold indistinguishable in HB1.
            cleanup.

            specialize (H4 0 1%nat *( false :: l0 )*).
            prove_precond H4.
            2:{
              simpl.
              unfold deq.
              rm_existentials. 
              rewrite app_comm_cons.
              split; eauto.
            }
            light_clean_propagate.
            unfold FifoSpec.Fifo2Spec.deq in H4.
            light_clean_propagate.
            simpl in H5.
            

            rm_existentials.
            simpl.
            unfold FifoSpec.Fifo2Spec.deq.
            rm_existentials.
            admit.
          }
        }
        split.
        rm_existentials.
        split; eauto.
        simpl.
        unfold FifoSpec.Fifo2Spec.enq.
        split.
        rm_existentials.
        split; eauto.
        simpl.
        split.
        {
          prove_precond HA4.
          2:{
            rm_existentials.
            split; eauto.
          }
          specialize (HA4 1%nat).
          unfold lock_step in HA4.
          specialize (HA4 0 *( false :: l )*).
          prove_precond HA4.
          2:{
            simpl.
            unfold deq.
            rm_existentials.
            rewrite app_comm_cons.
            split; eauto.
          }
          light_clean_propagate.
          unfold FifoSpec.Fifo2Spec.deq in HA0.
          light_clean_propagate.
          rewrite app_comm_cons in H4.
          apply app_inj_tail in H4.
          light_clean_propagate.
          eauto.
        }
        {
          prove_precond HB0.
          2:{
            rm_existentials.
            split; eauto.
          }
          specialize (HB0 1%nat).
          unfold lock_step in HB0.
          specialize (HB0 0 *( true :: l )*).
          prove_precond HB0.
          2:{
            simpl.
            unfold deq.
            rm_existentials.
            rewrite app_comm_cons.
            split; eauto.
          }
          light_clean_propagate.
          unfold FifoSpec.Fifo2Spec.deq in HA0.
          light_clean_propagate.
          rewrite app_comm_cons in H4.
          apply app_inj_tail in H4.
          light_clean_propagate.
          eauto.
        }
      }
      eauto.
    }
    (* eCompact *)
    {
      destruct i.
      {
        simpl.
        intros.
        unfold enq in H0.
        light_clean_propagate.
        unfold FifoSpec.Fifo2Spec.enq in *.
        specialize (HB b).
        light_clean_propagate.
        rm_existentials.
        split.
        rm_existentials.
        split; eauto.
        eauto.
      }
      destruct i.
      {
        simpl.
        intros.
        light_clean_propagate.
        unfold FifoSpec.Fifo2Spec.enq in HB.

        unfold indistinguishable in HA.
        cleanup.
        unfold deq in H0.
        light_clean_propagate.
        pose proof (H1 0 1%nat *( l0 )*).
        simpl in H0.
        unfold deq in H0.
        prove_precond H0.
        2:{
          rm_existentials.
          split; eauto.
        }
        light_clean_propagate.
        unfold FifoSpec.Fifo2Spec.deq in H0.
        light_clean_propagate.
        unfold FifoSpec.Fifo2Spec.deq.
        rm_existentials.
        split.
        rm_existentials.
        split; eauto.

        eapply eCompact.

        split.
        {
          prove_indistinguishable.
          {
            simpl.
            unfold FifoSpec.Fifo2Spec.enq.
            rm_existentials.
            split; eauto.
          }
          {
            admit.
          }
        }

        intros.
        split.
        rm_existentials.
        split; eauto.
        instantiate (1 := fun b => *( (b :: nil) ++ l )*).
        eauto.

        simpl.
        unfold FifoSpec.Fifo2Spec.enq.
        split.
        rm_existentials.
        split; eauto.
        specialize (HB b1).
        light_clean_propagate.
        prove_precond HB0.
        2:{
          rm_existentials.
          split; eauto.
        }
        specialize (HB0 1%nat).
        simpl in HB0.
        specialize (HB0 0 *( b1 :: l )*).
        unfold deq in HB0.
        prove_precond HB0.
        2:{
          rm_existentials.
          rewrite app_comm_cons.
          split; eauto.
        }
        light_clean_propagate.
        unfold FifoSpec.Fifo2Spec.deq in HA2.
        light_clean_propagate.
        rewrite app_comm_cons in H4.
        apply app_inj_tail in H4.
        light_clean_propagate.
        eauto.
      }
      simpl.
      eauto.
    }
    (* enq folded *)
    {
      destruct i.
      {
        simpl.
        intros.
        unfold enq in H0.
        light_clean_propagate.
        unfold FifoSpec.Fifo2Spec.enq in *.
        specialize (HB b).
        light_clean_propagate.
        unfold enq in HB1.
        light_clean_propagate.
        rm_existentials.
        split.
        rm_existentials.
        split; eauto.
        eauto. 
      }
      destruct i.
      {
        simpl.
        intros.
        light_clean_propagate.
        unfold FifoSpec.Fifo2Spec.enq in HB.

        unfold indistinguishable in HA.
        cleanup.
        unfold deq in H0.
        light_clean_propagate.
        pose proof (H1 0 1%nat *( l0 )*).
        simpl in H0.
        unfold deq in H0.
        prove_precond H0.
        2:{
          rm_existentials.
          split; eauto.
        }
        light_clean_propagate.
        unfold FifoSpec.Fifo2Spec.deq in H0.
        light_clean_propagate.
        unfold FifoSpec.Fifo2Spec.deq.
        rm_existentials.
        split.
        rm_existentials.
        split; eauto.

        eapply eFolded.

        split.
        {
          prove_indistinguishable.
          {
            simpl.
            unfold FifoSpec.Fifo2Spec.enq.
            rm_existentials.
            split; eauto.
          }
          {
            admit.
          }
        }

        intros.
        split.
        rm_existentials.
        split.
        2:{
          simpl.
          unfold enq.
          rm_existentials.
          split; eauto.
          simpl.
          instantiate (2 := fun b => *( (b :: nil) ++ l )*).
          simpl.
          eauto.
        }
        eauto.
        split.
        simpl.
        unfold FifoSpec.Fifo2Spec.enq.
        rm_existentials.
        split; eauto.
        specialize (HB b1).
        light_clean_propagate.
        prove_precond HB0.
        2:{
          rm_existentials.
          split; eauto.
        }
        unfold enq in HB1.
        light_clean_propagate.
        specialize (HB0 1%nat).
        simpl in HB0.
        specialize (HB0 0 *( b2 :: l )*).
        unfold deq in HB0.
        prove_precond HB0.
        2:{
          rm_existentials.
          rewrite app_comm_cons.
          split; eauto.
        }
        light_clean_propagate.
        unfold FifoSpec.Fifo2Spec.deq in HA2.
        light_clean_propagate.
        rewrite app_comm_cons in H4.
        apply app_inj_tail in H4.
        light_clean_propagate.
        eauto.
      }
      simpl.
      eauto.
    }
    {
      destruct i.
      {
        simpl.
        unfold enq.
        intros.
        light_clean_propagate.
        unfold FifoSpec.Fifo2Spec.deq in HA1.
        light_clean_propagate.
        unfold deq in HA0.
        light_clean_propagate.
        rm_existentials.
        unfold FifoSpec.Fifo2Spec.enq.
        split.
        rm_existentials.
        split; eauto.
        prove_precond HB0.
        2:{
          rm_existentials.
          split; eauto.
        }
        light_clean_propagate.
        specialize (HB0 0%nat).
        simpl in HB0.
        specialize (HB0 0 *( b :: l0 )*).
        prove_precond HB0.
        2:{
          unfold enq.
          rm_existentials.
          simpl.
          split; eauto.
        }
        light_clean_propagate.
        unfold FifoSpec.Fifo2Spec.enq in HA0.
        light_clean_propagate.
        eapply d.
        split.
        {
          prove_indistinguishable.
          {
            unfold FifoSpec.Fifo2Spec.enq.
            simpl.
            rm_existentials.
            split; eauto.
          }
          {
            simpl.
            unfold FifoSpec.Fifo2Spec.deq.
            rm_existentials.
            rewrite app_comm_cons.
            split; eauto.
          }
        }
        split.
        simpl.
        unfold deq.
        rm_existentials.
        rewrite app_comm_cons.
        split; eauto.
        simpl.
        unfold FifoSpec.Fifo2Spec.deq.
        split.
        rm_existentials.
        rewrite app_comm_cons.
        split; eauto.
        eauto.
      }
      destruct i.
      {
        simpl.
        unfold deq.
        intros.
        light_clean_propagate.
        unfold FifoSpec.Fifo2Spec.deq in HA1.
        light_clean_propagate.
        unfold deq in HA0.
        light_clean_propagate.
        rm_existentials.
        split.
        unfold FifoSpec.Fifo2Spec.deq.
        rm_existentials.
        split; eauto.
        apply app_inj_tail in H0.
        light_clean_propagate.
        eauto.
      }
      simpl.
      eauto.
    }
  Admitted.
  
  End Correctness3.