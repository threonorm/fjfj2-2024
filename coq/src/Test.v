Require Import List.
Record foo' := { 
        domain' : nat ; data' : nat -> nat; }.
Definition bar := 
        {| domain' := 2; data' := fun x => 42 |} .
Record foo := { 
        domain : nat ; data : nat -> nat; view : nat }.                
Definition yo (x:foo') : foo :=
 {| domain := @domain' x; data := @data' x; view := (data' x) (domain' x) |}.

Definition f (x : foo) : foo' :=
        {| domain' := @domain x; data' := @data x|}.

Coercion yo : foo' >-> foo. 

Definition plop (x:foo): Prop :=
        x = bar.

Notation "v" := ({|domain := _; data := _ ; view := v|}) (only printing, at level 200).

Goal plop bar.
cbv [yo]; simpl.
