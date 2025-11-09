
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
Arguments read' rf idx /.
Definition write' (rf : N -> N) (idx : N) (val : N):=
fun x => if N.eq_dec idx x then val else rf x.
Arguments write' rf idx val /.

Definition ready1 idx st ret := 
    exists (rf: N -> N), st = *( rf )* /\
    read' rf idx = 0 /\
    ret = 1.
Arguments ready1 idx st / ret.

Definition ready2 idx st ret := 
         exists (rf: N -> N), st = *( rf )* /\
    read' rf idx = 0 /\
    ret = 1.
Arguments ready2 idx st / ret.

Definition insert idx (st : SModule) (ret : SModule ):=
    exists (rf: N -> N), st = *( rf )* /\ 
    ret = *( write' rf idx (1 + (rf idx)))*.
Arguments insert idx st / ret.
  
Definition remove (idx :N) (st : SModule) (ret : SModule ):=
    exists (rf: N -> N) pred, st = *( rf )* /\ 
    rf idx = 1 + pred /\
    ret = *( write' rf idx pred )*.
Arguments remove idx st / ret.
 
Global Instance mkScoreboard : module _ := 
    primitive_module#(vmet [ ready1; ready2 ] amet [insert; remove]).

