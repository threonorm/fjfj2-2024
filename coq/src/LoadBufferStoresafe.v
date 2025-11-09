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

Record Entry := 
  {
    res : list N;
    outV : nat;
    outI : nat
  }.

Definition invalidate' (e : Entry) : Entry :=
  {| res := tl (res e); outV := outV e ; outI := outI e|}.
Arguments invalidate' e /.

Definition storeReq' (e : Entry) : Entry :=
  {| res := []; outV := 0 ; outI := outI e + outV e|}.
Arguments storeReq'  e /.

Definition loadReq' (e : Entry) : Entry :=
  {| res := res e; outV := outV e + 1; outI := outI e|}.
Arguments loadReq' e /.

Definition loadResp' (e : Entry) (data : N) : Entry :=
  match outI e with 
  | O => match outV e with 
    | O =>
      {| res := res e; outV := O; outI := O |}
      (* e *)
     (* Impossible case  *)
    | S n => 
         {| res := res e ++ [data] ; outV := n; outI := O |}
        end
  | S n => 
     {| res := res e; outV := outV e; outI := n |}
  end.
Arguments loadResp' e data /. 

Definition lossy_map_state := 
  N -> Entry.

(* Downgrade content of the map for a random address *)
Definition downgrade (st : SModule) (new_st : SModule) :=
  exists (map_st : lossy_map_state) (addr_killed : N), 
    st = *( map_st )* /\ 
    new_st = *( fun addr => if addr =? addr_killed then invalidate' (map_st addr) else map_st addr )*.
Arguments downgrade st / new_st.


(* We need a sum type, for that we use even and odd number *)
Definition lookup (arg : N) (st : SModule) (ret : N) : Prop  := 
    exists (map_st : lossy_map_state),
    st = *( map_st )* /\ 
    match res (map_st arg) with 
    | h::_ => ret = {# 1 h}
    | _ => ret = {# 0 0}
    end.
Arguments lookup arg st / ret.


Definition loadReq (addr : N) (st : SModule) (ret : SModule ) := 
  exists (map_st : lossy_map_state),
    st = *( map_st )* /\ 
    ret = *( fun new_addr => if new_addr =? addr then loadReq' (map_st addr) else map_st new_addr )*.
Arguments loadReq addr st / ret.

Definition storeReq (addr : N) (st : SModule) (ret : SModule ) := 
  exists (map_st : lossy_map_state),
    st = *( map_st )* /\ 
    ret = *( fun new_addr => if new_addr =? addr then storeReq' (map_st addr) else map_st new_addr )*.
Arguments storeReq addr st / ret.

Definition loadResp (arg : N) (st : SModule) (ret : SModule ) := 
  exists (map_st : lossy_map_state),
    st = *( map_st )* /\ 
    dlet {addr data} := arg in
    (outI (map_st addr) + outV (map_st addr))%nat <> O%nat /\
    ret = *( fun new_addr => if new_addr =? addr then loadResp' (map_st addr) data else map_st new_addr )*.
Arguments loadResp arg st / ret.


Global Instance mkLB : module _ := 
    primitive_module#(rules [downgrade] vmet [ lookup] amet [loadReq; storeReq; loadResp]).