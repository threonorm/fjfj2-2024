Require Import Lia.
Require Import String.
Require Import NArith.

Require Import LangFjfj2.
Require Import Indexification.
Require Import FjfjParsing.
Require Import Ltac2.Ltac2.
Require Import List.
Import ListNotations.
Require Import SopProp.
Require Import BaseTactics.

Local Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Set Default Proof Mode "Classic".
Require reg. 
Require Import RfSpec. 
Section ExploreRf.
  Context {uninterp : Uninterpreted_Functions}.

  Section RF.
    Definition nb_register := 32.
    Open Scope N.
    Definition rf : N->nat := N.to_nat.
    Definition write_rf : @action varname  :=
      Eval cbv in (fjfj_action
        (begin 
          #(set idx (@unpack_idx met_arg))
          #(set val (@unpack_val met_arg))
          (if (= idx 0)
            (((rf 0) write) val) 
            pass)
          (if (= idx 1)
            (((rf 1) write) val) 
            pass)
          (if (= idx 2)
            (((rf 2) write) val) 
            pass)
          (if (= idx 3)
            (((rf 3) write) val) 
            pass)
          (if (= idx 4)
            (((rf 4) write) val) 
            pass)
          (if (= idx 5)
            (((rf 5) write) val) 
            pass)
          (if (= idx 6)
            (((rf 6) write) val) 
            pass)
          (if (= idx 7)
            (((rf 7) write) val) 
            pass)
          (if (= idx 8)
            (((rf 8) write) val) 
            pass)
          (if (= idx 9)
            (((rf 9) write) val) 
            pass)
          (if (= idx 10)
            (((rf 10) write) val) 
            pass)
          (if (= idx 11)
            (((rf 11) write) val) 
            pass)
          (if (= idx 12)
            (((rf 12) write) val) 
            pass)
          (if (= idx 13)
            (((rf 13) write) val) 
            pass)
          (if (= idx 14)
            (((rf 14) write) val) 
            pass)
          (if (= idx 15)
            (((rf 15) write) val) 
            pass)
          (if (= idx 16)
            (((rf 16) write) val) 
            pass)
          (if (= idx 17)
            (((rf 17) write) val) 
            pass)
          (if (= idx 18)
            (((rf 18) write) val) 
            pass)
          (if (= idx 19)
            (((rf 19) write) val) 
            pass)
          (if (= idx 20)
            (((rf 20) write) val) 
            pass)
          (if (= idx 21)
            (((rf 21) write) val) 
            pass)
          (if (= idx 22)
            (((rf 22) write) val) 
            pass)
          (if (= idx 23)
            (((rf 23) write) val) 
            pass)
          (if (= idx 24)
            (((rf 24) write) val) 
            pass)
          (if (= idx 25)
            (((rf 25) write) val) 
            pass)
          (if (= idx 26)
            (((rf 26) write) val) 
            pass)
          (if (= idx 27)
            (((rf 27) write) val) 
            pass)
          (if (= idx 28)
            (((rf 28) write) val) 
            pass)
          (if (= idx 29)
            (((rf 29) write) val) 
            pass)
          (if (= idx 30)
            (((rf 30) write) val) 
            pass)
          (if (= idx 31)
            (((rf 31) write) val) 
            pass)
          )).
    Definition read_rf@{u}  :=
      Eval cbv in (fjfj_expr
        (begin 
          (set idx (@unpack_idx met_arg))
          (set res 0)
          (if (= idx 0)
            (set res (((rf 0) read) ))
            pass)
          (if (= idx 1)
            (set res (((rf 1) read) ))
            pass)
          (if (= idx 2)
            (set res (((rf 2) read) ))
            pass)
          (if (= idx 3)
            (set res (((rf 3) read) ))
            pass)
          (if (= idx 4)
            (set res (((rf 4) read) ))
            pass)
          (if (= idx 5)
            (set res (((rf 5) read) ))
            pass)
          (if (= idx 6)
            (set res (((rf 6) read) ))
            pass)
          (if (= idx 7)
            (set res (((rf 7) read) ))
            pass)
          (if (= idx 8)
            (set res (((rf 8) read) ))
            pass)
          (if (= idx 9)
            (set res (((rf 9) read) ))
            pass)
          (if (= idx 10)
            (set res (((rf 10) read) ))
            pass)
          (if (= idx 11)
            (set res (((rf 11) read) ))
            pass)
          (if (= idx 12)
            (set res (((rf 12) read) ))
            pass)
          (if (= idx 13)
            (set res (((rf 13) read) ))
            pass)
          (if (= idx 14)
            (set res (((rf 14) read) ))
            pass)
          (if (= idx 15)
            (set res (((rf 15) read) ))
            pass)
          (if (= idx 16)
            (set res (((rf 16) read) ))
            pass)
          (if (= idx 17)
            (set res (((rf 17) read) ))
            pass)
          (if (= idx 18)
            (set res (((rf 18) read) ))
            pass)
          (if (= idx 19)
            (set res (((rf 19) read) ))
            pass)
          (if (= idx 20)
            (set res (((rf 20) read) ))
            pass)
          (if (= idx 21)
            (set res (((rf 21) read) ))
            pass)
          (if (= idx 22)
            (set res (((rf 22) read) ))
            pass)
          (if (= idx 23)
            (set res (((rf 23) read) ))
            pass)
          (if (= idx 24)
            (set res (((rf 24) read) ))
            pass)
          (if (= idx 25)
            (set res (((rf 25) read) ))
            pass)
          (if (= idx 26)
            (set res (((rf 26) read) ))
            pass)
          (if (= idx 27)
            (set res (((rf 27) read) ))
            pass)
          (if (= idx 28)
            (set res (((rf 28) read) ))
            pass)
          (if (= idx 29)
            (set res (((rf 29) read) ))
            pass)
          (if (= idx 30)
            (set res (((rf 30) read) ))
            pass)
          (if (= idx 31)
            (set res (((rf 31) read) ))
            pass)
          res)).

    Context (lst : list N).
    Context {lst_is_32 : length lst = 32%nat}.

    Definition module_axiom : array spec_module_t:= 
      list_to_array
        unexisting_spec_module
        (repeat reg.spec_reg 32).

    Definition rf_impl := 
      build_module 
        module_axiom
        []
        (list_to_array Skip [write_rf])
        (list_to_array Abort [snd read_rf]).
  End RF.

  Ltac rf_wf :=
    first [ eapply amdirect | eapply vmdirect | eapply vmweakening | eapply amweakening].
  Ltac clean_arith := 
    match goal with 
    | [ H : context[N.eqb _] |- _] => goto_n H
    | [ |- context[N.eqb _]] => rm_b2n_chenil
    end.

  Ltac step_2m := first[  Marteller symb1 | eapply DIf2 | split]; cbn in *; try clean_arith.  
  Ltac merge H H0 := 
      let n := fresh in 
      pose proof (conj H H0) as n;
      clear H H0;
      rename n into H.
  Ltac cleanup := 
      repeat match goal with 
      | H: _ /\ _ |- _ => destruct H
      | H: exists _, _  |- _ => destruct H
      | H: True  |- _ => clear H
      | H : ?a = ?b, H' : ?a = ?b |- _ => clear H'
      | H : ?P, H' : ?P |- _ =>
        let t := type of P in
        assert_succeeds(constr_eq t Prop); 
        clear H'
      end.
  Ltac semi_appla := cbn;intros;
  (* cleanup; subst;cleanup; *)
          match goal with
          | [H: _ = _ , H' : _ = _|- _] => solve [congruence] 
          | [H: _ = _ , H' : _ <> _|- _] => clear H' 
          | [H: (N.b2n _) mod _ = _ |- _] => goto_n H 
          | |- _ /\ _ => split 
          | [ |- wpa _ _ _ _ _ _ _ _ ] =>
             first [ eapply DIf | symb1 ]
          | [ |- wp  _ _ _ _ _ _ _ ] =>
             symb1
          end.
  Ltac semi_appla_no_remove := cbn;intros;
  (* cleanup; subst;cleanup; *)
          match goal with
          | [H: _ = _ , H' : _ = _|- _] => solve [congruence] 
          | [H: (N.b2n _) mod _ = _ |- _] => goto_n H 
          | |- _ /\ _ => split 
          | [ |- wpa _ _ _ _ _ _ _ _ ] =>
             first [ eapply DIf | symb1 ]
          | [ |- wp  _ _ _ _ _ _ _ ] =>
             symb1
          end.
    Definition write_1s : @action varname  :=
      Eval cbv in (fjfj_action
            (if (= idx 0)
            (((rf 0) write) val)
            pass)
          ).
  
    Ltac boom :=
      cbn;
      (* repeat right; *)
      (* subst; *)
      lazymatch goal with
      | [ |- ?Mid ?a ?b ?c] =>
        let na := fresh in 
        first [
               let name_evar := fresh in
               set Mid as name_evar;
               is_var a; nameIsInCtx a Mid;
               instantiate (1:= fun x y z=> x = a /\ _ x y z) in (value of name_evar);
               subst name_evar;
               cbv beta; split; [apply eq_refl|..]
              |remember a as na]
        end;
        lazymatch goal with
        | [ |- ?Mid ?a ?b ?c] =>
          let nb := fresh in 
          first [
                 let name_evar := fresh in
                 set Mid as name_evar;
                 is_var b; nameIsInCtx b Mid;
                 instantiate (1:= fun x y z => y = b /\ _ x y z) in (value of name_evar);
                 subst name_evar;
                 cbv beta; split; [apply eq_refl|..]
                |remember b as nb] 
          end;
        lazymatch goal with
        | [ |- ?Mid ?a ?b ?c] =>
          let nc := fresh in 
          first [
                 let name_evar := fresh in
                 set Mid as name_evar;
                 is_var c; nameIsInCtx c Mid;
                 instantiate (1:= fun x y z => z = c /\ _ x y z) in (value of name_evar);
                 subst name_evar;
                 cbv beta; split; [apply eq_refl|..]
                |remember c as nc]
          end
          ;
        match goal with 
        |  |- ?Mid ?na ?nb ?nc => 
              let fn := fresh in
              assert True as fn; [easy|];
              repeat (getSPred1 fn);
              repeat (getSPred2 fn);
              let name_evar := fresh in
              set Mid as name_evar;
              instantiate (1:= fun x y z =>  _) in (value of name_evar);
              subst name_evar;
              cbn;
              try (refine (or_intror (_ na nb nc ) fn ); shelve)
              (* exact fn *)
              (* pattern na, nb, nc in fn; *)
              (* exact fn *)
        end
        .

  Definition mappingctx : mapping_t := (2, fun x =>
                                                if eqb x "idx" then 1
                                                else if eqb x "val" then 2
                                                else
                                                 0)%nat.
  Definition onestepwrite i : @action varname  :=
      Eval cbn in snd (fjfj_action_wm
            (if (= idx `(ZOp (Cst i)))
            (((rf i) write) val)
            pass) mappingctx).

  Lemma onestepwrite_rf_symb :
    (forall called_args st B A i b j post,
        i < 32 ->
        A (rf i) = None ->
        B 1%nat = j ->
        j <> i ->
        wpa st called_args (hideId module_axiom) B A empty_Vlog b post ->
        wpa st called_args (hideId module_axiom) B A empty_Vlog
            (Seq (onestepwrite i) b)
            post).
    intros.
    econstructor.
    unfold onestepwrite.
    eapply DIf.
    Marteller semi_appla_no_remove.
    boom.
    cbn.
    intros.
    instantiate (1:= fun x y z => False) in H4.
    cbn in H4.
    gsop_prop H4.
    cleanup.
    subst.
    eauto.
  Qed.
  Definition mappingctxread : mapping_t := (2, fun x =>
                                                if eqb x "idx" then 1
                                                else if eqb x "res" then 2
                                                else
                                                 0)%nat.

 Definition onestepread i : @expr varname  :=
      Eval cbn in snd (fjfj_expr_wm
          (if  (= idx `(ZOp (Cst i)))
            (set res (((rf i) read) ))
            pass)
             mappingctxread).

  Ltac semi_appla_no_remove' := cbn;intros;
  (* cleanup; subst;cleanup; *)
          match goal with
          | [H: sem_uninterp _ _ = _ , H' : sem_uninterp _ _ = _|- _] => solve [congruence] 
          | [H: (N.b2n _) mod _ = _ |- _] => goto_n H 
          | |- _ /\ _ => split 
          | [ |- wp _ _ _ _ _ _ _] =>
             first [ eapply DTernary | symb1 ]
          end.

  Ltac semi_appla' := cbn;intros;
  (* cleanup; subst;cleanup; *)
          match goal with
          | [H: _ = _ , H' : _ = _|- _] => solve [congruence] 
          | [H: _ = _ , H' : _ <> _|- _] => clear H' 
          | [H: (N.b2n _) mod _ = _ |- _] => goto_n H 
          | |- _ /\ _ => split 
          | [ |- wp _ _ _ _ _ _ _] =>
             first [ eapply DTernary | symb1 ]
          end.

  Lemma onestepread_rf_symb :
    (forall called_args st B V i b j post,
        i < 32 ->
        B 1%nat = j ->
        j <> i ->
        wp st called_args (hideId module_axiom) B V b post ->
        wp st called_args (hideId module_axiom) B V  
            (BOp ESeq (onestepread i) b)
            post).
    intros.
    econstructor.
    unfold onestepread.
    Marteller semi_appla_no_remove'.
    lia.
    lia.
    Marteller semi_appla_no_remove'.
    boom.
    cbn.
    intros.
    instantiate (1:= fun x y z => False) in H3.
    cbn in H3.
    gsop_prop H3.
    cleanup.
    subst.
    eauto.
  Qed.

  Lemma read_rf_symb : (forall called_args st (pf :  sem_uninterp "unpack_idx" called_args < 32),
        (forall (i:nat), (i < 32)%nat -> exists vreg, aget st i = {| T:=N; state := vreg |}) ->
        {post & 
          wp st called_args (hideId module_axiom) empty_B empty_Vlog 
               (snd read_rf)
              post }).
    intros.
    eexists.
    cbn.
    Ltac instantiate_all H n  := 
      match n with 
      | O => 
       let name := fresh  in 
       assert (n < 32)%nat as name by lia;
      pose proof (H n name); clear name
      | S ?m => 
        let name := fresh  in 
        assert (n < 32)%nat as name by lia;
        pose proof (H n name); clear name; instantiate_all H m
      end.
    instantiate_all H 31%nat.
    clear H.
    cleanup.
    Ltac c' called_args:= match goal with 
              | [  H' : sem_uninterp "unpack_idx" called_args = ?a |- _] => 
              match goal with 
              | [H : aget  _ ?b  = _ |- _] =>
                let prereduced := constr:(N.of_nat b) in
                let reduced := eval cbv in prereduced in 
                assert_fails(constr_eq a reduced);
                clear H
              end
              | [ H :  _ <>  _ |- _] => clear H 
              end.
    Ltac r := Marteller semi_appla_no_remove'; eauto.
    Ltac s called_args := repeat (eapply onestepread_rf_symb; eauto; try lia);
          econstructor;
          repeat (first [left | split; try reflexivity]); repeat (c' called_args); boom.
    Ltac t called_args:= Marteller r;[eexists;split; eauto;s called_args|].
    do 31 time (t called_args). 
    t called_args.
    r.
    repeat left.
    Ltac clearNeq := repeat 
          match goal with
          | [H: _ = _ |- _] => clear H 
          end.
    clearNeq.
    instantiate (1:= fun x y z => False).
    lia.
    Time Defined.
 
  Lemma read_rf_symb_compact : (forall called_args st (pf :  sem_uninterp "unpack_idx" called_args < 32),
        (forall (i:nat), (i < 32)%nat -> exists vreg, aget st i = {| T:=N; state := vreg |}) ->
        {post & 
          wp st called_args (hideId module_axiom) empty_B empty_Vlog 
               (snd read_rf)
              post }).
    intros.
    pose proof (projT2 (read_rf_symb _ _ pf H)) as hyp.
    exists (fun x y z => exists (n:N), sem_uninterp "unpack_idx" called_args < 32 /\ 
              z = n /\
              aget st (N.to_nat (sem_uninterp "unpack_idx" called_args)) = {| T := N; state := z |} /\
              x = setb (setb (setb empty_B 1%nat (sem_uninterp "unpack_idx" called_args)) 2 0) 2 z /\
              y = setvlog empty_Vlog (N.to_nat (sem_uninterp "unpack_idx" called_args)) 0 0).
    eapply wp_weakening.
    eapply vmweakening.
    exact hyp.
    intros.
    exists arg.
    clear hyp.
    cbn in H0.
    repeat match goal with 
    | [ H: _ \/ _ |- _] => destruct H 
    end.
    contradiction H0.
    all: cleanup;
      subst;
      rewrite H3 in *;
      repeat split; eauto.
    Defined.

    
  Lemma write_rf_symb : (forall called_args st (pf : sem_uninterp "unpack_idx" called_args < 32),

        (* (forall (i:nat), (i < 32)%nat -> exists vreg, aget st i = {| T:=N; state := vreg |}) -> *)
        {post & 
          wpa st called_args (hideId module_axiom) empty_B empty_Alog empty_Vlog 
               write_rf
              post }).
    intros.
    eexists.
    unfold write_rf.
    Ltac r' := Marteller semi_appla_no_remove; eauto;
    unfold reg.write_method'.
    Ltac s' := repeat (eapply onestepwrite_rf_symb;
    cbn; eauto; try lia); Marteller semi_appla; eauto;
          repeat (first [left | split; try reflexivity]); boom.
    Ltac t' := r';[s'|].
    do 31 time t'. 
    Marteller semi_appla_no_remove.
    eauto.
    repeat semi_appla.
    unfold reg.write_method'.
    cbn.
    repeat (first [left | split; try reflexivity]) .
    boom.
    Marteller semi_appla_no_remove.
    repeat (first [left | split; try reflexivity]) .
    instantiate (1:= fun x y z => False).
    lia.
  Time Defined.

  Lemma write_rf_symb_compact : 
      (forall called_args st (pf : sem_uninterp "unpack_idx" called_args < 32),
        {post & 
          wpa st called_args (hideId module_axiom) empty_B empty_Alog empty_Vlog 
               write_rf
              post }).
    intros.
    pose proof (projT2 (write_rf_symb _ st pf)) as hyp. 
    cbn in hyp.
    exists (fun x y z => 
              sem_uninterp "unpack_idx" called_args < 32 /\ 
              x = setb (setb empty_B 1%nat (sem_uninterp "unpack_idx" called_args)) 2 (sem_uninterp "unpack_val" called_args) /\
              y = setalog empty_Alog (N.to_nat (sem_uninterp "unpack_idx" called_args)) 0 (sem_uninterp "unpack_val" called_args) /\
              z = empty_Vlog).
    eapply wpa_weakening.
    eapply vmweakening.
    eapply amweakening.
    exact hyp.
    intros.
    clear hyp.
    cbn in H.
    repeat match goal with 
    | [ H: _ \/ _ |- _] => destruct H 
    end.
    contradiction H.
    all: cleanup;
      subst;
      rewrite H0 in *;
      repeat split; eauto.
    Defined.
End ExploreRf.
