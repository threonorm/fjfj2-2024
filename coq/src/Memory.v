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
Request are made of 4 fields:
is_write, addr, req_id, data 
*)

(* Responses are addr, data req_id *)
Definition enq_req (arg : N) (st : SModule) (new_st: SModule) : Prop  := 
    exists (mem_st : memory_state),
    st = *( mem_st )* /\ 
    dlet {is_write addr req_id data} := arg in 
    if (is_write =? 1) then
      new_st = *( {| mem := (fun addr' => if addr' =? addr then data else mem mem_st addr');
                      resps := resps mem_st |} )* 
    else 
      new_st = *( {| mem := mem mem_st; resps := resps mem_st ++ [ {# addr (mem mem_st addr) req_id} ] |} )* 
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
  action_methods := ["enq_req"; "deq_resp"]
|}.


(* 
Request are made of 4 fields:
is_write, addr, req_id, data 
*)
Module WritableMemory.
  (* A 0 initialized writable memory specification *)

  Record memory_state := 
    { 
        mem : N -> N;
        resps : list N;
    }.

    Definition perform_load (mi : memory_state) (addr : N) (reqid: N) (mi' : memory_state)
      := 
      let currentmem := Memory.WritableMemory.mem mi in  
      let currentresps := Memory.WritableMemory.resps mi in  
      mi' = 
        {|
          Memory.WritableMemory.mem := currentmem ; 
          Memory.WritableMemory.resps := currentresps ++ [{# 0 addr (currentmem addr) reqid}]
        |}.
    Arguments perform_load mi addr reqid / mi'.

    Definition perform_store (mi : memory_state) (addr : N) (data : N) (reqid: N) (mi' : memory_state)
      := 
      let currentmem := Memory.WritableMemory.mem mi in  
      let currentresps := Memory.WritableMemory.resps mi in  
      mi' = 
        {|
          Memory.WritableMemory.mem := (fun a => if (a =? addr)%N then data else currentmem a) ; 
          Memory.WritableMemory.resps := currentresps ++ [{# 1 addr data reqid}]
        |}.
    Arguments perform_store mi addr data reqid / mi'.

    Definition remove_resp (mi : memory_state) (resp : N) (mi' : memory_state)
      := 
      let currentmem := Memory.WritableMemory.mem mi in  
      let currentresps := Memory.WritableMemory.resps mi in  
      exists tl, 
      currentresps = resp :: tl /\
      mi' = 
        {|
          Memory.WritableMemory.mem := currentmem; 
          Memory.WritableMemory.resps := tl
        |}.
    Arguments remove_resp mi resp / mi'.

  (* Responses are confirmation, addr, data req_id *)
  Definition enq_req (arg : N) (st : SModule) (new_st: SModule) : Prop  := 
      exists (mem_st : memory_state) (newmem_st : memory_state),
      st = *( mem_st )* /\ 
      dlet {is_write addr req_id data} := arg in 
      if (is_write =? 1)%N then
        perform_store mem_st addr data req_id newmem_st /\
        new_st = *( newmem_st )* 
      else 
        perform_load mem_st addr req_id newmem_st /\
        new_st = *( newmem_st )* .
  Arguments enq_req arg st / new_st.

  Definition deq_resp (arg : N) (st : SModule) (new_st: SModule ) := 
    exists (mem_st newmem_st: memory_state) (resp : N),
      st = *( mem_st )* /\ 
      remove_resp mem_st resp newmem_st /\
      new_st = *( newmem_st )* .
  Arguments deq_resp arg st / new_st.

  Definition resp (arg : N) (st : SModule) (ret: N) := 
    exists (mem_st newmem_st: memory_state) (resp : N),
      st = *( mem_st )* /\ 
      remove_resp mem_st resp newmem_st /\
      ret = resp.
  Arguments resp arg st / ret.

  Global Instance mkMem : module _:= 
  primitive_module#(vmet [resp] amet [enq_req; deq_resp]).
End WritableMemory.