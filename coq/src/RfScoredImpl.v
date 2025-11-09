Require Import Lia.
Require Import String.
Require Import NArith.

Require Import LangFjfj2.
Require Import Indexification.
Require Import FjfjParsing.
Require Import List.
Import ListNotations.

Local Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(* Set Default Goal Selector "!". *)

Open Scope N.
Require Import Tactics.

Require Import egg.Loader.
Require Import RfSpec.

Local Instance rf_submodules : instances := 
#|
    mkRf rf;
    mkRf scoreboard 
|#.

Definition read1 :=
  (value_method (idx)
    (begin
      (set dependency {read1 scoreboard idx})
      (if (= dependency 0)
        {read1 rf idx} 
        abort))).
Arguments read1 /.

Definition read2 :=
  (value_method (idx)
    (begin 
      (set dependency {read2 scoreboard idx})
      (if (= dependency 0)
        {read2 rf idx} 
        abort))).
Arguments read2 /.

Definition declare_write :=
  (action_method (idx)
    (begin 
      (set dependency {read3 scoreboard idx})
      (if (= dependency 0)
        {write scoreboard (# idx 1)}
        abort))).
Arguments declare_write /.
        
Definition write :=
  (action_method (idx val)
    (begin 
      (set dependency {read3 scoreboard idx})
      (if (= dependency 1)
        (begin 
          {write scoreboard (# idx 0) }
          {write rf (# idx val)})
        abort))).
Arguments write /.

Definition withdraw_write :=
  (action_method (idx)
    (begin 
      (set dependency {read3 scoreboard idx})
      (if (= dependency 1)
        {write scoreboard (# idx 0) }
        abort)
        pass)).
Arguments withdraw_write /.
 
Global Instance mkScoredRf : module _ := 
    module#(vmet [ read1; read2 ] amet [ declare_write; write; withdraw_write ]).

Definition ϕ (ist : SModule) (sst : SModule) := 
    exists 
        (rfs: N -> (bool * N))
        (rf: N -> N) 
        (scoreboard: N -> N), 
        sst = *( rfs )* /\
        ist = *[| rf; scoreboard |]* /\
        forall n, 
          (scoreboard n = 0 <-> fst (rfs n) = true) /\
          (scoreboard n = 1 <-> fst (rfs n) = false) /\
          (rf n) = snd (rfs n) .

Require Import RfScored.
Arguments ϕ / ist sst.
Arguments RfSpec.read'  rf idx /.
Notation "a '<|' b" := (indistinguishable (spec_of mkScoredRf)  (spec_of RfScored.mkRf) a b) (at level 20, only parsing).
Notation " '('  a '<|' b ')' " := (indistinguishable _  _ a b) (at level 20, only printing).
Notation " '(' a  '→*'  b ')' " := (existSR _ a b) (at level 20, only printing).
Close Scope string_scope.

Lemma ϕ_implies_state_simul :
  forall ist sst, ϕ ist sst -> ist <| sst. (* .in *)  
  prove_state_simulation. (* .in *)
  { 
    specialize (HB1 arg).
    symb_ex_split; light_clean_propagate; repeat auto_specialize.
    rm_existentials; firstorder.
    destruct (rfs arg) eqn:?; simpl in *; subst; eauto.
  }
  { 
    specialize (HB1 arg).
    symb_ex_split; light_clean_propagate; repeat auto_specialize.
    rm_existentials; firstorder.
    destruct (rfs arg) eqn:?; simpl in *; subst; eauto.
  }
  { 
    specialize (HB1 arg).
    symb_ex_split; light_clean_propagate; repeat auto_specialize.
    rm_existentials; firstorder.
    destruct (rfs arg) eqn:?; simpl in *; subst; eauto.
  }
  { 
    specialize (HB1 (split1 arg)).
    symb_ex_split; light_clean_propagate; repeat auto_specialize.
    rm_existentials; firstorder.
  }
  { 
    specialize (HB1 (arg)).
    symb_ex_split; light_clean_propagate; repeat auto_specialize.
    unfold withdraw_write.
    rm_existentials; firstorder.
    destruct (rfs arg) eqn:?; simpl in *; subst; eauto.
  }
  Qed.

Theorem correct : refines mkScoredRf RfScored.mkRf ϕ.
  prove_refinement.
  {
    clear indistinguishable_i_s; light_clean_propagate.
    simpl in related_i_s.
    symb_ex_split. 
    merge_simpl. 
    rm_existentials; merge_simpl; simpl. 
    split.
    {
      specialize (HB1 arg_method).
      rm_existentials; firstorder.
      light_clean_propagate.
      repeat auto_specialize.
      destruct (rfs arg_method); simpl in *; subst; eauto.
    }
    split.
    { eapply existSR_done. }
    assert_related ϕ_implies_state_simul.
    {
      pose proof (HB1 arg_method).
      light_clean_propagate.
      rm_existentials.
      repeat auto_specialize.
      split; eauto.
      split.
      { wrapped_arrays_equal 2%nat; prove_outside nxt_st; eauto. }
      intros.
      specialize (HB1 n).
      destruct (N.eq_dec _ _) eqn:?; subst; rewrite Heqs.
      simpl in *.
      split; eauto; easy.
      light_clean_propagate.
      repeat auto_specialize.
      split; eauto; easy.
    }
  }
  {
    clear indistinguishable_i_s; light_clean_propagate.
    simpl in related_i_s.
    symb_ex_split. 
    merge_simpl. 
    rm_existentials; merge_simpl; simpl. 
    split.
    {
      specialize (HB1 (split1 arg_method)).
      rm_existentials; firstorder.
      light_clean_propagate.
      repeat auto_specialize.
      destruct (rfs (split1 arg_method)); simpl in *; subst; eauto.
    }
    split.
    { eapply existSR_done. }
    assert_related ϕ_implies_state_simul.
    {
      pose proof (HB1 (split1 arg_method)).
      light_clean_propagate.
      repeat auto_specialize.
      rm_existentials.
      split; eauto.
      split.
      { wrapped_arrays_equal 2%nat; prove_outside nxt_st; eauto. }
      simpl.
      intros.
      destruct (N.eq_dec (split1 arg_method) n); subst; simpl. 
      (* The following alternative crashes the kernel *)
      (* destruct (N.eq_dec (split1 arg_method) n) eqn:?; subst; simpl.  *)
      split; eauto; easy.
      specialize (HB1 n).
      light_clean_propagate.
      split; eauto; easy.
    }
  }
  {
    clear indistinguishable_i_s; light_clean_propagate.
    simpl in related_i_s.
    symb_ex_split. 
    merge_simpl. 
    rm_existentials; merge_simpl; simpl. 
    split.
    {
      unfold withdraw_write.
      specialize (HB1 (arg_method)).
      rm_existentials; firstorder.
      light_clean_propagate.
      repeat auto_specialize.
      destruct (rfs (arg_method)); simpl in *; subst; eauto.
    }
    split.
    { eapply existSR_done. }
    assert_related ϕ_implies_state_simul.
    {
      pose proof (HB1 (arg_method)).
      light_clean_propagate.
      repeat auto_specialize.
      rm_existentials.
      split; eauto.
      split.
      { wrapped_arrays_equal 2%nat; prove_outside nxt_st; eauto. }
      intros.
      simpl.
      specialize (HB1 n).
      destruct (N.eq_dec _ _) eqn:?; subst. 
      simpl in *.
      split; eauto; easy.
      light_clean_propagate.
      repeat auto_specialize.
      split; eauto; easy.
    }
  }
  Qed.