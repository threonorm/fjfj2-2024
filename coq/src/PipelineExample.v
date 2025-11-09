Require Import Lia.
Require Import String.
Require Import NArith.

Require ZArith.
Require Import egg.Loader.
Require Import egg.Egg.
Require Import LangFjfj2.
Require Import Indexification.
Require Import FjfjParsing.
Require Import Ltac2.Ltac2.
Require Import List.

Require Import Tactics.
Local Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Set Default Proof Mode "Classic".

Import ListNotations.
(* Record defined_expression  := { idx_expr : nat; dexpr : @expr varname}.
Coercion idx_expr : defined_expression >-> nat.
Coercion dexpr : defined_expression >-> expr. *)

Require Import Fifo.
Require Import reg.
Require Import FifoSpec.
Require Fifo1Correct.


Module SpecUnit.
    Open Scope string.
    Definition enq (arg : N) (st : SModule) (returnIs : SModule) : Prop :=
        exists l, st = {| T := list N; state := l|} /\
        returnIs = {| T:= list N; state :=  app l [?"g" (?"f" arg)]|}.

    Definition deq (arg : N) (st : SModule) (returnIs : SModule) : Prop :=
        exists head l, st = {| T:= list N; state := head :: l|} /\ 
        returnIs = {| T:= list N; state := l|}.

    Definition first (arg : N) (st : SModule) (returnIs : N) : Prop := 
        exists head l, st = {| T:= list N; state := head :: l|} /\ 
        returnIs = head.

    Arguments enq arg st returnIs /.
    Arguments deq arg st returnIs /.
    Arguments first arg st returnIs /.

    Global Instance mkPipelineSpec : module _ := 
    primitive_module#(
            vmet [first] amet [enq; deq]).
  
End SpecUnit.

Module ImplPipeline.
    Import Fifo1Fjfj.
    Local Instance processor_modules : instances :=
      #| 
        mkFifo1 in_fifo;
        mkFifo1 mid_fifo;
        mkFifo1 out_fifo
      |#.

    Definition enq :=
      (action_method (el)
          ((in_fifo enq) el)).

    Definition deq :=
      (action_method ()
          ((out_fifo deq))).

    Definition first :=
      (value_method ()
          ((out_fifo first))).

    Definition do_f :=
      (rule
        (begin 
          ((in_fifo deq))
          (set in_el ((in_fifo first)))
          ((mid_fifo enq) (f in_el)))) .

    Definition do_g :=
      (fjfj_action
      (begin 
          ((mid_fifo deq))
          (set mid_el ((mid_fifo first)))
          ((out_fifo enq) (g mid_el)))).

    Arguments enq /.
    Arguments deq /.
    Arguments first /.
    Arguments do_f /.
    Arguments do_g /.
  Global Instance mkPipeline : module _ := 
    module#(rules [do_f; do_g]
            vmet [first] amet [enq; deq]).
End ImplPipeline.


Module InterPipeline.

    Import FifoSpec.
    Local Instance submodules : instances :=
      #| 
        mkFifoSpec in_fifo;
        mkFifoSpec mid_fifo;
        mkFifoSpec out_fifo
      |#.

    Import ImplPipeline.

    Global Instance mkPipeline : module _ := 
        module#(rules [do_f; do_g]
                vmet [first] amet [enq; deq]).
End InterPipeline.

Section Correctness.
    (* Prototype tactic to refines hole with the refinement *)
     Theorem correct : { rfd & refines (spec_of ImplPipeline.mkPipeline) (spec_of InterPipeline.mkPipeline) rfd}.
      eexists.
      refinement_t 0%nat Fifo1Correct.correct_against_1s.
      refinement_t 1%nat Fifo1Correct.correct_against_1s.
      refinement_t 2%nat Fifo1Correct.correct_against_1s.
      refinement_t 0%nat FifoSpec.correct_1spec_nspec.
      refinement_t 1%nat FifoSpec.correct_1spec_nspec.
      refinement_t 2%nat FifoSpec.correct_1spec_nspec.
      (* TODO: wrap the following into a tactic *)
      unfold smodule, InterPipeline.mkPipeline.
      remember (ModuleTableS _ _ _).
      assert (a = @code InterPipeline.submodules) as modules_equals.
      {
          eapply ext_array; subst a; cbn; eauto.
          intros.
          repeat (try destruct x; eauto).
      }
      rewrite modules_equals.
      eapply refines_refl.
      Time Defined.

    Inductive flush : list N -> list N -> list N -> list N -> Prop :=
      | flushedAgree : forall (out : list N),
          flush [] [] out out 
      | do_F: forall i m o i' m' o',
        nth 0 (rule_spec (spec_of InterPipeline.mkPipeline)) unexisting_rule *[| i; m; o |]* *[| i'; m'; o'|]*  ->
        forall s, flush i' m' o' s ->
        flush i m o s 
      | do_G: forall i m o i' m' o',
        nth 1 (rule_spec (spec_of InterPipeline.mkPipeline)) unexisting_rule *[| i; m; o |]* *[| i'; m'; o'|]*  ->
        forall s, flush i' m' o' s ->
        flush i m o s.


    Open Scope N.
    Open Scope string.

    Lemma flush_enq :
        forall (init mid out lst : list N) x, 
        flush init mid out  lst ->
        flush (app init [x]) mid out (app lst [?"g" (?"f" x )]).
        intros.
        induction H.
        {
            unfold state_t in *.
            light_clean_propagate.
            eapply do_F.
            simpl.
            eexists.
            let y := (eexists_st_array 3%nat) in
            eexists y.
            do 3 eexists.
            split; eauto.
            simpl.
            split; eauto.
            split.
            reconstruct.
            split; eauto.
            split; eauto.
            all: try solve[reconstruct_step; simpl; eauto].
            apply_log_fn 3%nat; simpl.
            eapply do_G.
            simpl.
            eexists.
            let y := (eexists_st_array 3%nat) in
            eexists y.
            do 3 eexists.
            split; eauto.
            simpl.
            split; eauto.
            split.
            reconstruct.
            split; eauto.
            split; eauto.
            all: try solve[reconstruct_step; simpl; eauto]. 
            apply_log_fn 3%nat; simpl.
            econstructor; eauto.
        }
        {
            simpl in *.
            light_clean_propagate.
            min_straight_line.
            repeat simpl_applylog.
            eapply do_F.
            simpl.
            eexists.
            let y := (eexists_st_array 3%nat) in
            eexists y.
            do 3 eexists.
            split; eauto.
            simpl.
            split; eauto.
            split.
            reconstruct.
            split; eauto.
            split; eauto.
            all: try solve[reconstruct_step; simpl; eauto].
            apply_log_fn 3%nat; simpl.
        }
        {
            simpl in *.
            light_clean_propagate.
            min_straight_line.
            repeat simpl_applylog.
            eapply do_G.
            simpl.
            eexists.
            let y := (eexists_st_array 3%nat) in
            eexists y.
            do 3 eexists.
            split; eauto.
            simpl.
            split; eauto.
            split.
            reconstruct.
            split; eauto.
            split; eauto.
            all: try solve[reconstruct_step; simpl; eauto].
            apply_log_fn 3%nat; simpl.
        }
    Qed.

    Lemma flush_doF :
        forall (init mid out lst : list N) x, 
        flush (x::init) mid out lst ->
        flush init (mid ++ [(?"f" x)]) out lst.
        intros.
        remember (x::init).
        generalize dependent init.
        induction H; intros.
        {
            inversion Heql.
        }
        {
            simpl in *.
            light_clean_propagate.
            min_straight_line.
            repeat simpl_applylog.
            eauto.
        }
        {
            simpl in *.
            light_clean_propagate.
            min_straight_line.
            repeat simpl_applylog.
            simpl.
            eapply do_G.
            simpl.
            eexists.
            let y := (eexists_st_array 3%nat) in
            eexists y.
            do 3 eexists.
            split; eauto.
            simpl.
            split; eauto.
            split.
            reconstruct.
            split; eauto.
            split; eauto.
            split; eauto.
            apply_log_fn 3%nat; simpl.
            eapply IHflush; eauto.
        }
    Qed.

    Lemma flush_doG :
        forall (init mid out lst : list N) x, 
        flush init (x::mid) out lst ->
        flush init mid (out ++ [(?"g" x)]) lst.
        intros.
        remember (x::mid).
        generalize dependent mid.
        induction H; intros.
        {
            inversion Heql.
        }
        {
            simpl in *.
            light_clean_propagate.
            min_straight_line.
            repeat simpl_applylog.
            simpl.
            eapply do_F.
            simpl.
            eexists.
            let y := (eexists_st_array 3%nat) in
            eexists y.
            do 3 eexists.
            split; eauto.
            simpl.
            split; eauto.
            split.
            reconstruct.
            split; eauto.
            split; eauto.
            split; eauto.
            apply_log_fn 3%nat; simpl.
            eapply IHflush; eauto.
        }
        {
            simpl in *.
            light_clean_propagate.
            min_straight_line.
            repeat simpl_applylog.
            eauto.
        }
    Qed.
    Lemma flush_deq :
        forall (init mid out lst : list N) x, 
        flush init mid (x::out) (x::lst) ->
        flush init mid out lst.
        intros.
        remember (x::out).
        remember (x::lst).
        generalize dependent out.
        generalize dependent lst.
        induction H; intros.
        {
            rewrite Heql in Heql0.
            inversion Heql0.
            econstructor.
        }
        {
            simpl in *.
            light_clean_propagate.
            min_straight_line.
            repeat simpl_applylog.
            eapply do_F.
            simpl.
            eexists.
            let y := (eexists_st_array 3%nat) in
            eexists y.
            do 3 eexists.
            split; eauto.
            simpl.
            split; eauto.
            split.
            reconstruct.
            split; eauto.
            split; eauto.
            split; eauto.
            apply_log_fn 3%nat; simpl.
            eauto.
        }
        {
            simpl in *.
            light_clean_propagate.
            min_straight_line.
            repeat simpl_applylog.
            eapply do_G.
            simpl.
            eexists.
            let y := (eexists_st_array 3%nat) in
            eexists y.
            do 3 eexists.
            split; eauto.
            simpl.
            split; eauto.
            split.
            reconstruct.
            split; eauto.
            split; eauto.
            split; eauto.
            apply_log_fn 3%nat; simpl.
            eapply IHflush; eauto.
        }
    Qed.

    Definition related (ist : SModule) (sst : SModule) := 
        exists (inp mid out s: list N),
        (* Note: it is important to write the following equation in that order
        for automatization reasons *) 
        ist = *[| inp; mid; out |]* /\
        sst = *( s )* /\
        flush inp mid out s .
    Arguments related / ist sst.

    Lemma flush_obs_simulate :
        forall (i s: SModule), 
        related i s ->
        indistinguishable (InterPipeline.mkPipeline) (SpecUnit.mkPipelineSpec) i s.
        intros.
        simpl in H.
        light_clean_propagate.
        induction HB0.
        {
            identify_modules.
            prove_indistinguishable.
            {
                light_clean_propagate.
                min_straight_line.
                repeat econstructor.
            }
            {
                light_clean_propagate.
                min_straight_line.
                repeat econstructor.
            }
            {
                light_clean_propagate.
                min_straight_line.
                repeat econstructor.
            }
        }
        {
            light_clean_propagate.
            min_straight_line.
            repeat simpl_applylog.
            destruct IHHB0.
            identify_modules.
            prove_indistinguishable.
            {
                eapply H0.
                simpl in *.
                light_clean_propagate.
                symb_ex_split.
                repeat econstructor.
            }
            {
                light_clean_propagate.
                min_straight_line.
                repeat simpl_applylog.
                (* specialize (H4 arg 0%nat). *)
                eapply H1 with (new_st_i:= *( _)* ).
                simpl.
                eexists.
                let y := (eexists_st_array 3%nat) in
                eexists y.
                do 3 eexists.
                split;eauto.
                split;eauto.
                split.
                reconstruct_wpa.
                all: try solve[reconstruct_step; simpl; eauto].
                apply_log_fn 3%nat.
            }
            {
                light_clean_propagate.
                symb_ex_split.
                (* specialize (H4 arg 0%nat). *)
                eapply H1 with (new_st_i:= *( _)* ) (method_id := 1%nat) .
                simpl.
                eexists.
                let y := (eexists_st_array 3%nat) in
                eexists y.
                do 3 eexists.
                split;eauto.
                split;eauto.
                split.
                reconstruct_wpa.
                all: try solve[reconstruct_step; simpl; eauto].
                split; eauto.
                apply_log_fn 3%nat.
            }
        }
        {
            simpl in *.
            light_clean_propagate.
            min_straight_line.
            repeat simpl_applylog.
            destruct IHHB0.
            prove_indistinguishable.
            {
                eapply H.
                simpl in *.
                light_clean_propagate.
                min_straight_line.
                repeat econstructor.
            }
            {
                light_clean_propagate.
                min_straight_line.
                repeat simpl_applylog.
                (* specialize (H4 arg 0%nat). *)
                eapply H0 with (new_st_i:= *( _)* ).
                simpl.
                
                eexists.
                let y := (eexists_st_array 3%nat) in
                eexists y.
                do 3 eexists.
                split;eauto.
                split;eauto.
                split.
                reconstruct.
                split;eauto.
                apply_log_fn 3%nat.
            }
            {
                light_clean_propagate.
                min_straight_line.
                repeat simpl_applylog.
                (* specialize (H4 arg 0%nat). *)
                eapply H0 with (new_st_i:= *( _)* ).
                simpl.
                
                eexists.
                let y := (eexists_st_array 3%nat) in
                eexists y.
                do 3 eexists.
                split;eauto.
                split;eauto.
                split.
                reconstruct.
                split;eauto.
                apply_log_fn 3%nat.
            }
        }
        Unshelve.
        exact 0.
    Qed.

    Ltac pre_method' related_i_s indistinguishable_i_s := 
        simpl in related_i_s;
        light_clean_propagate;
        clear indistinguishable_i_s;
        simpl in *|-;
        min_straight_line;
        repeat  simpl_applylog;
        min_straight_line;
        simpl in * |-;
        repeat clean_arith;
        light_clean_propagate.

    Theorem correct' : refines  (spec_of InterPipeline.mkPipeline) (spec_of SpecUnit.mkPipelineSpec) related.
    prove_refinement.
    {
        (* Case ENQ *)
        pre_method' related_i_s indistinguishable_i_s.
        do 2 eexists.
        (* It is possible to do a step on the implementation side, trivially *)
        split; [ eexists; split; eauto | ..].
        (* Do no extra rules the spec side on enq *)
        split;[ eapply existSR_done |..].
        assert_related flush_obs_simulate.
        {
            simpl.
            do 4 eexists.
            split.
            wrapped_arrays_equal 3%nat.
            split.
            reflexivity.
            eapply flush_enq.
            eauto.
        }
    }
    {
        pose proof (flush_obs_simulate _ _ related_i_s).
        pre_method' related_i_s indistinguishable_i_s.
        light_clean_propagate.
        destruct H.
        specialize (H 0 0%nat head0).
        simpl in H.

        assert (exists (head : N) (l : list N), *( s )* = *( head :: l )* /\ head0 = head).
        {
            apply H.
            do 3 eexists.
            split;eauto.
            reconstruct.
            split; eauto.
        }
        light_clean_propagate.
        do 2 eexists.
        split.
            repeat econstructor.
        (* Do no extra rules the spec side on enq *)
        split;[ eapply existSR_done |..].
        assert_related flush_obs_simulate.
        {
            simpl.
            do 4 eexists.
            split; eauto.
            wrapped_arrays_equal 3%nat.
            split; eauto.
            eapply flush_deq.
            eapply HB1.
        }
    }
    {
        pre_method' related_i_s indistinguishable_i_s.
        light_clean_propagate.
        eexists.
        (* Do no extra rules the spec side on enq *)
        split;[ eapply existSR_done |..].
        assert_related flush_obs_simulate.
        {
            simpl.
            do 4 eexists.
            split.
            wrapped_arrays_equal 3%nat.
            split; eauto.
            eapply flush_doF; eauto.
        }
    }
    {
        pre_method' related_i_s indistinguishable_i_s.
        light_clean_propagate.
        eexists.
        (* Do no extra rules the spec side on enq *)
        split;[ eapply existSR_done |..].
        assert_related flush_obs_simulate.
        {
            simpl.
            do 4 eexists.
            split.
            wrapped_arrays_equal 3%nat.
            split; eauto.
            eapply flush_doG; eauto.
        }
    }
   Time Qed. 

   Theorem toplevel_correct : {related & refines (spec_of ImplPipeline.mkPipeline) (spec_of SpecUnit.mkPipelineSpec)  related }.
    pose proof correct.
    pose proof correct'.
    destruct X.
    eexists.
    eapply @trans_refinement with (1:= r).
    eapply @trans_refinement with (1:= H).
    eapply refines_refl.
    Time Defined.

End Correctness.