Require Import Lia.
Require Import NArith.

Require Import LangFjfj2.
Require Import Indexification.
Require Import FjfjParsing.
Require Import List.
Import ListNotations.

Require String.

Local Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Open Scope N.
Set Default Goal Selector "!".


Module FifoSpec.
  Notation state_t := SModule.

  Definition enq (arg : N) (st : SModule) (new_st: SModule) :=
     exists l, 
     (st = {| T := list N; state := l|} /\
      new_st = ({| T:= list N; state := app l [arg] |})).

  Definition first (arg : N) (st : state_t) (ret : N) := 
    exists head l, st = {| T:= list N; state := cons head l|} /\ 
    ret = head.

  Definition deq (arg : N) (st : SModule) (new_st : SModule ) :=
    exists head l, st = {| T:= list N; state := cons head l|} /\ 
    new_st = {| T:= list N; state := l|} .


  Definition spec : spec_module_t :=
      {|
        value_spec := list_to_array unexisting_vmethod [first];
        action_spec := list_to_array unexisting_amethod [enq; deq];
        rule_spec := [];
        subrules_spec := [];
      |}.

  Global Instance mkFifoSpec : module spec := 
  primitive_module#( vmet [first] amet [enq; deq]).
End FifoSpec.

Arguments FifoSpec.first arg st / ret.
Arguments FifoSpec.deq arg st/ new_st.
Arguments FifoSpec.enq arg st/ new_st.

Module FifoF.

  Definition first (arg : N) st ret  := 
    exists head l, st = {| T:= list N; state := cons head l |} /\ 
    ret = head.
  Arguments first arg st ret/.

  Definition assume_empty (arg : N) st ret  := 
    st = {| T:= list N; state := []|} /\ ret = 0.
  Arguments assume_empty arg st ret/.

  Definition deq (arg : N) (st : SModule) (ret : SModule ) :=
    exists head l, st = {| T:= list N; state := cons head l|} /\ 
    ret = {| T:= list N; state := l|} .
  Arguments deq arg st ret /.

  Definition enq (arg : N) (st : SModule) (ret : SModule) :=
    (* We can only push in this queue if there is no load in there *)
     exists l, 
     (st = {| T := list N; state := l|} /\
      ret = ({| T:= list N; state := app l [arg] |})).
  Arguments enq arg st ret /.

  Global Instance mkFifoFSpec: module _ := 
    primitive_module#(vmet [ first; assume_empty] amet [enq; deq ]).
End FifoF.


Module Fifo1Spec.
  Notation state_t := SModule.
 
  Definition first (arg : N) (st : state_t) (ret : N ) := 
    exists n, st = {| T:= option N; state := Some n |} /\ ret = n.

  Definition deq (arg : N) (st : SModule) (ret : SModule ) :=
     exists n, st = {|T := option N; state := Some n |} /\
     ret = {| T:= option N; state := None|}.

  Definition enq (arg : N) (st : SModule) (ret : SModule ):=
     st = {| T := option N; state := None |} /\
     ret = {| T:= option N; state := Some arg|}.

  Global Instance mkFifo1 : module _ := 
    primitive_module#(vmet [ first ] amet [enq; deq]).

End Fifo1Spec.

Module Fifo2Spec.
  Notation state_t := SModule.

  Definition deq (_arg : N) (st : SModule) (ret : SModule ) :=
     exists (l : list unit), st = *( l ++ [tt] )* /\
     ret = *( l )*.

  Definition enq (arg : N) (st : SModule) (ret : SModule ):=
     exists (l : list unit), st = *( l )* /\
     ret = *( [tt] ++ l )*.

  Global Instance mkFifo2 : module _ := 
    primitive_module#(amet [enq; deq]).

End Fifo2Spec.

Arguments Fifo1Spec.first arg st / ret.
Arguments Fifo1Spec.deq arg st / ret.
Arguments Fifo1Spec.enq arg st / ret.
Definition related (ist : SModule) (sst : SModule) := 
  (forall (a:N), sst = generic_embed([a]) <-> ist = generic_embed(Some a))
  /\
  (sst = generic_embed([]:list N) <-> ist = generic_embed(None:option N))
  . 
Arguments related / ist sst.

Section Correctness.
  Context {uninterp : Uninterpreted_Functions}.
  Theorem correct_1spec_nspec : refines (spec_of Fifo1Spec.mkFifo1) (spec_of FifoSpec.mkFifoSpec) related.
    prove_refinement.
    {
      simpl in related_i_s. light_clean_propagate. 
      do 2 eexists.
      split.
      { crush. } 
      split.
      {  eapply existSR_done. }
      split.
      { 
        simpl. crush.
      }
      {
        prove_indistinguishable; crush.
      }
    }
    {
      simpl in related_i_s.  clean_propagate.
      (* Little help needed: *)
      specialize (HA n).
      clean_propagate. 
      do 2 eexists.
      split.
      { crush. }
      split.
      { eapply existSR_done. }
      split.
      {
        simpl.
        crush.
      }
      {
        prove_indistinguishable; crush.
      }
    }
    Time Qed.

End Correctness.