
(* DEPRECATED, NOT CURRENTLY COMPILED? *)
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
Require LoadBuffer.
Require Nondet.
Open Scope N.

Context (fns : Uninterpreted_Functions).
Local Instance nouninterp : Uninterpreted_Functions := fns.
Axiom define_minus : ? "minus" = fun x => dlet {a b}:= x in a - b .

Module GCDSpec.
    (* TODO we can add a constraint on the fact that a and b are smaller than 2^nbits *)
    Definition req arg st ret := 
        st = *((None  : option (N * N)))* /\
        dlet {a b} := arg in ret = *( Some (a,b) )*.
    Arguments req arg st / ret.

    Definition isGCD p n m := 
    (* Classic predicate for GCD:*)
        (* p divides both n and m *)
         (p | n) /\ (p | m) /\
         (* any other divider of n and m necessarily divides p *)
        (forall q : N, (q | n) -> (q | m) -> (q | p)).

    Definition resp (arg :N) (st : SModule) (ret : N):=
        exists (a b : N), st = *( Some(a,b) )* /\ 
        isGCD ret a b.
    Arguments resp arg st / ret.

    (* Consume the request, allowing to send a further request *)
    Definition deq_resp (arg :N) (st : SModule) (new_st: SModule):=
        exists (a b : N), st = *( Some(a,b) )* /\ 
        new_st = *( None : option (N * N))*.
    Arguments deq_resp arg st / new_st.
End GCDSpec.

Module GCDImpl1.
  (* First implementations machine: using substraction *)
  Local Instance processor_modules : instances :=
      #| 
        reg.mkReg a;
        reg.mkReg b;
        reg.mkReg valid
      |#.

    Definition req :=
      (fjfj_action
          (if (~ 1 ((valid read))) 
              (begin 
                  ((valid write) 1)
                  (set (na nb) met_arg)
                  ((a write) na)
                  ((b write) nb))
              abort)).
    Arguments req /.
    Definition size := 32.
    Definition do_compute :=
      (fjfj_action
        (if ((valid read)) 
          (begin 
            (set av ((a read)))
            (set bv ((b read)))
            (if (< av bv)
              (begin 
                ((a write) bv)
                ((b write) av)) 
              (begin 
                ((a write) bv)
                ((b write) (@ minus (# av bv)))
                )))
            abort)).
  Arguments do_decode /.
