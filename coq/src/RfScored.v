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

Open Scope N.

Definition read1 idx st ret := 
    exists (rf: N -> (bool * N)) v, st = *( rf )* /\
    (true,v) = rf idx /\ 
    ret = v.
Arguments read1 idx st / ret.

Definition read2 idx st ret := 
    exists (rf: N -> (bool * N)) v, st = *( rf )* /\
    (true,v) = rf idx /\ 
    ret = v.
Arguments read2 idx st / ret.

Definition write' (rf : N -> bool * N) (idx : N) (newval : bool * N) :=
fun x => if N.eq_dec idx x then newval else rf x.
Arguments write' rf idx newval /.


Definition write (arg :N) (st : SModule) (ret : SModule ):=
    (* We can only write if the dependency had been declared. *)
    exists (rf: N -> bool * N) , st = *( rf )* /\ 
    dlet {idx val} := arg in
    (fst (rf idx) = false) /\
    ret = *( write' rf idx (true, val) )*.
Arguments write arg st / ret.

Definition declare_write idx (st : SModule) (ret : SModule):=
    (* To insert a dependency it needs to be the case that there was none before. 
    (this way we handle waw *)
    exists (rf: N -> bool * N) x, st = *( rf )* /\ 
    rf idx = (true, x) /\
    ret = *( write' rf idx (false, x))*.
Arguments declare_write idx st / ret.

Definition withdraw_write idx (st : SModule) (ret : SModule):=
    (* To insert a dependency it needs to be the case that there was none before. 
    (this way we handle waw *)
    exists (rf: N -> bool * N) x, st = *( rf )* /\ 
    rf idx = (false, x) /\
    ret = *( write' rf idx (true, x))*.
Arguments declare_write idx st / ret.
  
Global Instance mkRf : module _ := 
    primitive_module#(vmet [ read1; read2 ] amet [declare_write; write; withdraw_write ]).
