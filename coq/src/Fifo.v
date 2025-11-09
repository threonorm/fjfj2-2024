Require Import Lia.
Require Import String.
Require Import NArith.


Require Import LangFjfj2.
Require Import Indexification.
Require Import FjfjParsing.
Require Import List.

Local Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Set Default Goal Selector "!".

Import ListNotations.
Require reg.


Open Scope N.
Module Fifo1Fjfj.
  Context {uninterp : Uninterpreted_Functions}.

  Local Instance fifo_submodules : instances := 
    #| reg.mkReg valid ; reg.mkReg data |#.

  Definition enq :=
    (action_method (e)
      (begin
        (if (= {read valid} 0)
          (begin
            {write data e}
            {write valid 1})
          abort))).
  Arguments enq /.

  Definition deq :=
    (action_method ()
      (begin
        (if (= {read valid} 1)
            {write valid 0}
          abort))).
  Arguments deq /.

  Definition first :=
    (value_method ()
        (if (= {read valid} 1)
            {read data}
            abort)).
  Arguments first /.

  Global Instance mkFifo1 : module _ := 
    module#(vmet [ first ] amet [enq; deq]).
End Fifo1Fjfj.

Module Fifo2NonDet.
  Notation state_t := SModule.

  Definition deq (_arg : N) (st : SModule) (ret : SModule ) :=
     exists (l : list bool) (b : bool), st = *( l ++ [b] )* /\
     ret = *( l )*.

  Definition enq' (b : bool) (l : list bool) : list bool :=
      b :: l.
  Arguments enq' /.

  Definition enq (_arg : N) (st : SModule) (ret : SModule ):=
     exists (l : list bool) b, st = *( l )* /\
     ret = *( enq' b l )*.

  Global Instance mkFifo2 : module _ := 
    primitive_module#( amet [enq; deq]).

End Fifo2NonDet.