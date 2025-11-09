Require Import LangFjfj2.
Require Import NArith.
Require Import List.
Import List.ListNotations.
Local Set Universe Polymorphism.

Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

Definition state_t := N.

Definition write_method' (arg : N) (st : SModule) (ret : SModule) : Prop :=
   ret = {| T := N; state := arg |}.
Arguments write_method' arg st / ret.

Definition read_method' (arg : N) (st : SModule) (ret : N ) := 
   exists n, st = {| T := N; state := n|} /\ ret = n .
Arguments read_method' arg st / ret.

Definition spec_reg : spec_module_t := {|
      value_spec := list_to_array unexisting_vmethod [read_method'];
      action_spec := list_to_array unexisting_amethod [write_method'];
      rule_spec := [] ;
      subrules_spec := [] ;
    |}.
Require Import String.
Open Scope string.

Global Instance interface : module spec_reg:= 
(* DEPRECATED name *)
  {| 
    value_methods := ["read"] ;
    action_methods := ["write"];
    rule_names := []
  |}.

Global Instance mkReg : module spec_reg:= 
  {| 
    value_methods := ["read"] ;
    action_methods := ["write"];
    rule_names := []
  |}.
Close Scope string.


