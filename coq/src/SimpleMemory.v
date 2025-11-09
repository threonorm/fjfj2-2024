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

Set Default Goal Selector "!".

Require reg. 
Record memory_state := 
  { 
      mem : N -> N;
      resps : list N;
  }.

Open Scope N.

(* 
Request are made of 3 fields:

    is_write, addr,  data 

Responses are addr, data 
No response on write *)
Definition enq_req (arg : N) (st : SModule) (new_st: SModule) : Prop  := 
    exists (mem_st : memory_state),
    st = *( mem_st )* /\ 
    dlet {is_write addr data} := arg in 
    if (is_write =? 1) then
      new_st = *( {| mem := (fun addr' => if addr' =? addr then data else mem mem_st addr');
                      resps := resps mem_st |} )* 
    else 
      new_st = *( {| mem := mem mem_st; resps := resps mem_st ++ [ (mem mem_st addr) ] |} )* 
    .
Arguments enq_req arg st / new_st.

Definition deq_resp (arg : N) (st : SModule) (new_st: SModule ) := 
  exists (mem_st : memory_state),
    st = *( mem_st )* /\ 
      new_st = *( {| mem := mem mem_st; resps := tl (resps mem_st) |} )* .
Arguments deq_resp arg st / new_st.

Definition resp (arg : N) (st : SModule) (ret: N) := 
  exists (mem_st : memory_state),
    st = *( mem_st )* /\ 
    exists hd tl, resps mem_st = hd :: tl /\
      ret = hd.
Arguments resp arg st / ret.

Definition mem_spec : spec_module_t :=
  {|
    value_spec := list_to_array unexisting_vmethod [resp];
    action_spec := list_to_array unexisting_amethod [enq_req; deq_resp];
    rule_spec := [] ;
    subrules_spec := [] ;
  |}.

Local Open Scope string_scope.
Global Instance mkMem : module mem_spec := 
{| 
  value_methods := ["resp"] ;
  action_methods := ["enq_req"; "deq_resp"];
  rule_names := nil
|}.

