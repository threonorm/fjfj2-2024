Require Import Lia.
Require Import String.
Require Import NArith.

Require ZArith.

Require Import LangFjfj2.
Require Import Indexification.
Require Import FjfjParsing.
Require Import List.

Local Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Open Scope N.
Import ListNotations.

Definition choose (arg : N) (st : SModule) (ret : N) : Prop := 
    exists n, 
      ret = n.
Arguments choose arg st / ret.

Definition choose_between(arg : N) (st : SModule) (ret : N) : Prop := 
    exists n, 
      dlet {min max} := arg in 
      min <= n /\
      n < max /\
      ret = n.
Arguments choose_between arg st / ret.

Definition choose_above (arg : N) (st : SModule) (ret : N) : Prop := 
    exists n, 
      arg <= n /\
      ret = n.
Arguments choose_above arg st / ret.

Definition spec : spec_module_t :=
  {|
    value_spec := list_to_array unexisting_vmethod [choose; choose_above; choose_between];
    action_spec := list_to_array unexisting_amethod [];
    rule_spec := [] ;
    subrules_spec := [] ;
  |}.

Local Open Scope string_scope.
Global Instance mkND : module spec := 
{| 
  value_methods := ["choose"; "choose_above"; "choose_between"] ;
  action_methods := [];
  rule_names := []
|}.