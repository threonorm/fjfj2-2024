Require Import Lia.
Require Import String.
Require Import NArith.

Require ZArith.

Require Import Indexification.
Require Import FjfjParsing.
Require Import LangFjfj2.
Require Import List.

Local Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Open Scope N.
Import ListNotations.

Definition lossy_map_state := 
          N -> list N.
(* Downgrade content of the map for a random address *)
Definition downgrade (st : SModule) (new_st : SModule) :=
  exists (map_st : lossy_map_state) (addr_killed : N), 
    st = *( map_st )* /\ 
    new_st = *( fun addr => if addr =? addr_killed then tl (map_st addr) else map_st addr )*.

Arguments downgrade st / new_st.

(* We need a sum type, for that we use even and odd number *)
Definition lookup (arg : N) (st : SModule) (ret : N) : Prop  := 
    exists (map_st : lossy_map_state),
    st = *( map_st )* /\ 
    match map_st arg with 
    | h :: _t => ret = {# 1 h}
    | nil => ret = {# 0 0}
    end.
Arguments lookup arg st / ret.

Definition insert (arg : N) (st : SModule) (ret : SModule ) := 
  exists (map_st : lossy_map_state),
    st = *( map_st )* /\ 
    dlet {addr data} := arg in
    ret = *( fun new_addr => if new_addr =? addr then  map_st addr ++ [data] else map_st new_addr )*.
Arguments insert arg st / ret.

Definition clear (arg : N) (st : SModule) (ret : SModule ) := 
  exists (map_st : lossy_map_state),
    st = *( map_st )* /\ 
    ret = *( fun new_addr => if new_addr =? arg then  [] else map_st new_addr )*.
Arguments clear arg st / ret.


Global Instance mkLB : module _ := 
    primitive_module#(rules [downgrade] vmet [ lookup] amet [insert; clear]).
