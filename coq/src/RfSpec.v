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
Definition read'  (rf : N -> N) idx := rf idx.
Arguments read' / rf idx .

Definition write' (rf : N -> N) (idx : N) (newval : N) :=
fun x => if N.eq_dec idx x then newval else rf x.
Arguments write' / rf idx newval .

Definition read1 idx st ret := 
    exists (rf: N -> N), st = *( rf )* /\
     ret = (read' rf idx).
Arguments read1 / idx st ret.

Definition read2 idx st ret := 
    exists (rf: N -> N), st = *( rf )* /\
    ret = (read' rf idx).
Arguments read2 / idx st ret.

Definition read3 idx st ret := 
    exists (rf: N -> N), st = *( rf )* /\
     ret = (read' rf idx).
Arguments read3 / idx st ret.

Definition write (arg :N) (st : SModule) (ret : SModule ):=
    exists (rf: N -> N), st = *( rf )* /\ 
    dlet {idx val} := arg in 
    ret = *( write' rf idx val )*.
Arguments write arg st / ret.
  
Global Instance mkRf : module _ := 
    primitive_module#(vmet [ read1; read2; read3 ] amet [write]).

