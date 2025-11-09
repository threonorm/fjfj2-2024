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

Import ListNotations.
Require reg.
Require RfSpec.
Require FifoSpec.
Require Nondet.
Require Import egg.Loader.
Require Import Tactics.
Require Import Coq.Sets.Ensembles.
From extructures Require Import ord fmap.

Open Scope N.



(* Developement that gives two generalization of a client (req/resp): 

  Pipelined generalization
  Out-of-order generalization
  
  We prove that the out-of-order generalization, once controlled by a Completion Buffer, is a refinement of the pipelined generalization.
*)
Require Import String.
Definition generic_client (sm : spec_module_t) : module sm := 
  {| value_methods := ["get_result"%string]; 
    action_methods := ["enq"%string;"deq"%string];
    rule_names := []|}.

Module Type GenericReqResp_t. 
  Parameter (T: Type).
  Parameter (req : T -> N -> T).
  Parameter (deq: T -> T).
  Parameter (get_resp : T -> N).

  Inductive buffered_input := 
    | None 
    | Done.
  Record st := 
    { 
      module_state : T;
      inp : buffered_input 
      }.
End GenericReqResp_t.

Module GenericReqResp (p : GenericReqResp_t).
  Import p.
  (* Experimentation with using locally *)
  Definition c : st -> SModule := fun x => *( x )*.
  Coercion c : st >-> SModule.
  Arguments c/.

  Definition enq (arg : N) (st : SModule) (st' : SModule) :=
    exists sm, st = {| module_state := sm; inp := None |} /\
    st'= {| module_state := p.req sm arg ; inp := Done |}.
  Arguments enq /.

  Definition deq (tag : N) (st : SModule) (st' : SModule) := 
     exists sm ,
     st = {| module_state := sm; inp := Done |} /\
     st' = {| module_state := p.deq sm; inp := None |} .
  Arguments deq /.
 
  Definition get_result (_arg : N) (st : SModule) (res : N) := 
     exists sm res ,
     st = {| module_state := sm; inp := Done |} /\
     res = p.get_resp sm.
  Arguments get_result/.

  Definition empty_mod (s : p.T) := 
    {| module_state := s; inp := None |}.

  Global Instance mkGenericReqResp : module _ := 
    primitive_module#(vmet [ get_result ] amet [ enq; deq ]).

End GenericReqResp.



(* Calling from Axiomatic module *)
Module TestM (gen_m : GenericReqResp_t).
  Module m := GenericReqResp gen_m.
  Import m.
  Definition m := mkGenericReqResp .

  Definition enq (arg : N) (st : SModule) (st' : SModule) :=
    exists (b : N) sm sm', st = *( (b, sm) )* /\
    (aget (action_spec m) 0 (* enq method is the number 0 *) 
           arg sm  sm')  (* sm -[ enq(i) ]-> sm' *)
           /\
    st'= *( (b, sm') )*.
  Arguments enq /.

  Definition get_result (_arg : N) (st : SModule) (res : N) := 
    (* Some nonsense for exercising our understanding *)
    exists ret (b : N) sm, st = *( (b, sm) )* /\ 
    ret mod 2 = 0 /\
    (aget (value_spec m) 0 _arg sm ret) /\
     res = ret.
  Arguments get_result/.
  Global Instance mkGenericReqResp : module _ := 
    primitive_module#( vmet [get_result] amet [ enq]).

End TestM.


(* Calling from Fjfj *)
Module Test2 (gen_m : GenericReqResp_t).
    Module m := GenericReqResp gen_m.
    Import m.
    Definition m := mkGenericReqResp .
    Local Instance sub_modules : instances :=
      #| 
        mkGenericReqResp m;
        reg.mkReg v
      |#.

    Open Scope N.
    Definition enq :=
      (action_method (el)
        (begin 
          (set tag {read v})
          {enq m tag})).
    Arguments enq /.
    Definition get_result:=
      (value_method (el)
        (begin 
          {get_result m}
          )).
    Arguments get_result/.

  Global Instance mkTest2: module _ := 
    module#(vmet [get_result] amet [enq ]).
End Test2.