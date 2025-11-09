Require Import egg.Loader.
Require Import egg.Egg.
Require Import NArith.
Require Import Arith.
Require String.
Require Import List.
Import List.ListNotations.
  Axiom merge : N -> N -> N.
  Axiom split1 : N -> N.
  Axiom split2 : N -> N.

  Axiom merge_of_split: forall n, merge (split1 n) (split2 n) = n.
  Axiom merge_split1 : forall n1 n2, split1 (merge n1 n2) = n1.
  Axiom merge_split2 : forall n1 n2, split2 (merge n1 n2) = n2.
Local Set Universe Polymorphism.
Unset Universe Minimization ToSet.
(* Set Polymorphic Inductive Cumulativity. *)
Require Import Eqdep.
Global Hint Rewrite
   Nat.eqb_eq Nat.eqb_neq
   Nat.leb_le Nat.leb_gt
   Nat.ltb_lt Nat.ltb_ge
   N.eqb_eq N.eqb_neq
   N.leb_le N.leb_gt
   N.ltb_lt N.ltb_ge
: fwd_rewrites.

Require Import Lia.
Require Import FunctionalExtensionality.
Tactic Notation "rpn" constr(i) ident(name) :=
      match goal with 
      | [H: context[i] |- _] => 
      rename H into name
      end.
Ltac auto_specialize' H' :=
  match goal with
  | H:?a, H':?a -> _
	|- _ => let t := type of a in
            constr_eq t Prop; specialize (H' H)
  | H:?a
    |- _ =>
        let t := type of a in
        constr_eq t Prop; specialize H' with (1 := H)
  | H':_ |- _ => specialize H' with (1 := eq_refl)
  end.
  
Section Array.
  Universe V_univ.
  Context {V : Type@{V_univ}}.
  Record array := { alength : nat; default: V; values :(nat -> V)}.
  Definition list_to_array d l := {| alength := length l; default := d; values := fun x => List.nth x l d|}.
  Definition empty_array d := {| alength := 0; default := d; values := fun x => d|}.
  Open Scope nat.
  Definition aget (a : array) i := values a i.
  Definition aset (a : array) i v :=
    {| alength := alength a;
       default := default a;
       values :=
         if i <? alength a then
         (fun idx => if  i =? idx then v else values a idx)
         else values a|}.
  Lemma get_set_eq : forall (a : array) i v, i < alength a -> aget (aset a i v) i = v.
    intros.
    unfold aset, aget.
    cbn.
    destruct (alength _) eqn:?.
    inversion H.
    destruct (_ <=? _) eqn:?; eauto.
    destruct (_ =? _) eqn:?; eauto.
    all: autorewrite with fwd_rewrites in *;
    lia.
  Qed.
  Lemma set_set_eq : forall (a : array) i v1 v2,  aset (aset a i v1) i v2 = aset a i v2 .
    intros.
    unfold aset.
    cbn.
    destruct (alength _) eqn:?.
    eauto.
    destruct (_ <=? _) eqn:?; eauto.
    f_equal.
    (* Search (forall x, ?f x = ?g x -> ?f = ?g). *)
    eapply functional_extensionality.
    intros.
    destruct (i =? _) eqn:?; eauto.
  Qed.
  Lemma set_set_neq : forall (a : array) i j v1 v2, i <>j -> aset (aset a i v1) j v2 = aset (aset a j v2) i v1 .
    intros.
    unfold aset.
    cbn.
    destruct (alength _) eqn:?.
    eauto.
    destruct (_ <=? _) eqn:?; eauto.
    f_equal.
    eapply functional_extensionality.
    intros.
    destruct (j =? _) eqn:?; eauto;
    destruct (i <=? _) eqn:?; eauto;
    try destruct (i =? _) eqn:?; eauto;
    try destruct (j =? _) eqn:?; eauto; try lia.
    autorewrite with fwd_rewrites in *.
    lia.
  Qed.
  Lemma get_set_neq : forall (a : array) i v j, i <> j -> aget (aset a i v) j = aget a j.
    intros.
    unfold aset, aget.
    cbn.
    destruct (alength _) eqn:?;eauto.
    destruct (_ <=? _) eqn:?; eauto.
    destruct (i <=? _) eqn:?; eauto.
    destruct (i =? _) eqn:?; eauto.
    all: autorewrite with fwd_rewrites in *;
    lia.
  Qed.
  Lemma set_get_eq : forall (a : array) i, i < alength a -> aset a i (aget a i) = a.
    intros.
    unfold aset, aget.
    cbn.
    destruct a.
    cbn.
    f_equal.
    destruct (alength0) eqn:?; eauto.
    cbn in H.
    destruct (_ <=? _) eqn:?; eauto.
    eapply functional_extensionality.
    intros.
    destruct (_ =? _) eqn:?; eauto.
    autorewrite with fwd_rewrites in *.
    subst.
    eauto.
  Qed.

  Lemma ext_array' : forall  (a b : array ),
      default a = default b -> alength a = alength b ->
      (forall x, values a x = values b x) -> a = b.
      intros.
      destruct a; destruct b.
      cbn in *.
      subst.
      f_equal.
      eapply functional_extensionality; eauto.
  Qed.
  Lemma ext_array : forall  (a b : array ),
       alength a = alength b ->
       default a = default b -> 
      (forall x, aget a x = aget b x) -> a = b.
      intros.
      destruct a; destruct b.
      cbn in *.
      subst.
      f_equal.
      eapply functional_extensionality; eauto.
  Qed.

  Close Scope nat.
End Array.

Arguments aget {V} !a !i /.
Arguments array V : clear implicits.
Arguments list_to_array {_} / d l.

Section MapArray.
  Definition amap {V V'} d (f : V -> V') (a : array V) : array V' :=
    {| alength := alength a; default := d ; values := fun x => if x <? alength a then f (values a x) else d  |}.
  Lemma amap_amap {V V' V''} d d' (f : V -> V') (f' : V' -> V'') (a : array V) :
    amap d' f' (amap d f a) = amap d' (fun x => f' (f x)) a.
    unfold amap; eauto.
    simpl.
    f_equal.

      eapply functional_extensionality; eauto.
    intros.
    simpl.
    destruct (x  <? alength a) ; eauto.
  Qed.
  Lemma get_amap_in {V V'} d (f : V -> V') (a : array V) :
     forall i, i< alength a -> aget (amap d f a) i = f (aget a i).
     intros.
     unfold amap, aget.
     cbn.
     destruct (alength _).
     inversion H.
     eauto.
     assert (i <=? n = true).
     eapply Nat.leb_le.
     lia.
     eauto.
     rewrite H0; eauto.
  Qed.

  Lemma get_amap_out {V V'} d (f : V -> V') (a : array V) :
     forall i, i >= alength a -> aget (amap d f a) i = d.

     intros.
     unfold amap, aget.
     cbn.
     destruct (alength _);eauto.
     assert (i <=? n = false ).
     eapply Nat.leb_gt.
     lia.
     eauto.
     rewrite H0; eauto.
  Qed.

End MapArray.


Inductive SModule :=
  { T : Type ; state : T}.

Record array_with_view V := { alength' : nat; default': V; values' :(nat -> V) ; view' : list V}.

Definition add_view V (x: array V) : array_with_view V:=
 {| alength' := alength x; default' := default x; values':= values x;
    view' := List.map (fun idx => values x idx) (List.seq 0%nat (alength x)) |}.

Definition rm_view {V} (x: array_with_view V) :=
 {| alength := alength' _ x; default := default' _ x; values:= values' _ x;
    |}.
(* Coercion add_view : array >-> array_with_view.  *)
Coercion rm_view : array_with_view >-> array .

Notation "'array:' v" := ({|alength':= _; default' := _ ; values' := _; view':= v|}) 
     (only printing, at level 2, right associativity). 

Ltac print_arrays := 
(* Useful tactic to properly print arrays *)
    repeat match goal with 
    | [H : context[ Build_array ?a ?d ?v ] |- _ ] =>
         let eq := fresh "eq_array" in
          let el:= fresh "array_modules" in
          change (Build_array a d v) with (rm_view (add_view _ (Build_array a d v))) in H;
          cbv [add_view] in H; simpl in H
    | |- context[ Build_array ?a ?d ?v ]  =>
         let eq := fresh "eq_array" in
          let el:= fresh "array_modules" in
          change (Build_array a d v) with (rm_view (add_view _ (Build_array a d v))) ;
          cbv [add_view] ; simpl 
    end.
  
Definition value_method_spec_t@{u}  :=
    N -> SModule@{u}  -> N  -> Prop.

Definition unexisting_vmethod  : value_method_spec_t :=
     fun _ _ _ => False.

Definition action_method_spec_t@{u} :=
      N -> SModule@{u} -> SModule@{u} -> Prop.

Definition unexisting_amethod : action_method_spec_t :=
     fun _ _ _ => False.

Definition rule_spec_t@{u} :=
      SModule@{u} -> SModule@{u} -> Prop.

Definition unexisting_rule  : rule_spec_t :=
     fun _ _ => False.

Definition unexisting_module : SModule :=
  {| T := unit ; state := tt|}.

Definition inversion_type (s : SModule) : { t & t} :=
  existT _ (T s) (state s).

Ltac inverseS H :=
  apply (f_equal inversion_type) in H;
  cbn in H;
  apply inj_pair2 in H.

Ltac inverseAll :=
  match goal with 
  | H : {| T := ?a ; state := ?b |} = {| T:= ?c ; state := ?d|} |- _=> inverseS H; cbn in H; inversion H; clear H
  end.
Lemma smodule_inj : forall (t : Type) (x y : t), 
    Build_SModule t x = Build_SModule t y -> 
    x = y.
        intros.
        apply (f_equal inversion_type) in H.
        apply inj_pair2 in H.
        cbn in H.
        eauto.
    Qed. 
Lemma smodule_injS : forall (t : Set) (x y : t), 
    Build_SModule t x = Build_SModule t y -> 
    x = y.
        intros.
        apply (f_equal inversion_type) in H.
        apply inj_pair2 in H.
        cbn in H.
        eauto.
    Qed. 

Lemma some_inj : forall (t : Type) (x y :t),
  Some x = Some y -> x = y .
  intros; inversion H; eauto.
  Qed.
Definition generic_embed {T'} (s:T') :=
  {| T:= T'; state :=s |}.
Arguments generic_embed {_} / s.

Arguments List.nth_error {_} !l !n.

Section Syntax.
  Inductive Zprimitive :=
  | Cst (c : N)
  .

  Inductive Uprimitive :=
  | Fn (s : String.string)
  | BwNot (c : N)
  | BwSize (c : N)
  | Split1 
  | Split2 
  | PassCst
  .

  Inductive Bprimitive :=
  | Plus
  | Lt 
  | Gt 
  | Leq 
  | Geq 
  | Eq
  | Merge
  | BwAnd
  | BwOr
  | ESeq
  .

  Record varname := { idxvar : nat; stringvar : String.string }.

  Inductive expr {var : Type} :=
  | Var (v : var)
  | Arg
  | ZOp (prim : Zprimitive)
  | UOp (prim : Uprimitive) (arg1 : expr)
  | BOp (prim : Bprimitive) (arg1 : expr) (arg2 : expr)
  | SetVar (v : var) (e : expr)
  | Ternary (c : expr) (t : expr) (f : expr)
  | Abort
  | ValMethod
              (instance : varname)
              (met : varname)
              (args : expr)
  with action {var : Type} :=
  | If (c : expr) (t : action) (f : action)
  | Expr (e : expr)
  | Skip
  | Seq (s1 : action) (s2 : action)
  | ActionMethod
    (instance : varname)
    (met : varname)
    (arg : expr).

End Syntax.

Record spec_module_t@{u v w} := {
    value_spec : array@{w} value_method_spec_t@{u};
    action_spec : array@{w} action_method_spec_t@{u};
    rule_spec : list rule_spec_t@{u};
    subrules_spec : list (list rule_spec_t@{v})
  }.
Definition unexisting_spec_module := 
  {| value_spec := empty_array unexisting_vmethod; 
     action_spec := empty_array unexisting_amethod;
     rule_spec := [];
     subrules_spec := [];
     |}.
Class Uninterpreted_Functions := { sem_uninterp : String.string -> N -> N }.
Ltac cleanup := intros;
  repeat match goal with
  | H: _ /\ _ |- _ => destruct H
  | H: exists _, _  |- _ => destruct H
  | H: True  |- _ => clear H
  | H : ?a = ?b, H' : ?a = ?b |- _ => clear H'
  | H : N.of_nat ?a = N.of_nat ?b |- _ =>
    apply Nat2N.inj in H
  (* | H : ?P, H' : ?P |- _ =>
    let t := type of P in
    assert_succeeds(constr_eq t Prop);
    clear H' *)
  end.
Ltac cleanup_preserve_names := intros;
  repeat match goal with
  | H: _ /\ _ |- _ => destruct H
  | H: exists i, _  |- _ => let n := fresh i in destruct H as [n]
  | H: True  |- _ => clear H
  | H : ?a = ?b, H' : ?a = ?b |- _ => clear H'
  | H : N.of_nat ?a = N.of_nat ?b |- _ =>
    apply Nat2N.inj in H
  (* | H : ?P, H' : ?P |- _ =>
    let t := type of P in
    assert_succeeds(constr_eq t Prop);
    clear H' *)
  end.
Ltac auto_specialize :=
match goal with
| H : ?a,  H' : ?a -> _  |- _ =>
  let t := type of a in
  constr_eq t Prop;
  specialize( H' H)
| H : ?a,  H' :  _  |- _ =>
  let t := type of a in
  constr_eq t Prop;
  specialize H' with (1:= H)
|  H' :  _  |- _ =>
  specialize H' with (1:= eq_refl)
end.

Ltac blast_arith :=  Zify.zify;
      PreOmega.Z.quot_rem_to_equations;
      lia.

Lemma nth_error_seq : forall j i, i < j -> 
 nth_error (seq 0 j) i = Some i.
 induction j; intros.
 -
   destruct i; eauto; try lia.
 -
   destruct i; eauto; try lia.
   replace (S j) with (j +  1) by lia.
   erewrite seq_app.
   cbn.
   destruct (S i <? j) eqn:?.
   autorewrite  with fwd_rewrites in Heqb. 
   erewrite nth_error_app1; eauto.
   rewrite seq_length; eauto.
   autorewrite  with fwd_rewrites in Heqb. 
   erewrite nth_error_app2; eauto.
   rewrite seq_length; eauto.
   replace (S i) with j by lia.
   replace (j - j)  with 0 by lia.
   eauto.
   rewrite seq_length; eauto.
 Qed.
 
Lemma nth_seq : forall x y i, x < y ->nth x (seq 0 y) i = x.
 intros.
 eapply nth_error_nth.
 eapply nth_error_seq; eauto.
 Qed.

Section Interp.
  Definition state_t := array SModule.

  Context {uninterp : Uninterpreted_Functions}.
  Context (st : state_t).
  Context (called_args : N).

  Context (ModuleTable : array spec_module_t).

  Definition Binders := nat -> N.
  Definition setb (b : Binders) x y idx := if Nat.eq_dec x idx then y else b idx.
  Definition empty_B: Binders := fun i => 0%N.
  Definition Vlog := forall (inst:nat) (met:nat), option N.
  Definition setvlog nV (inst met:nat) (varg : N) i m :=
      if andb (Nat.eqb met m) (Nat.eqb inst i)
        then
          Some varg
        else
          nV i m.
  Definition empty_Vlog : Vlog := fun i m => None.
  Definition Alog := (forall (inst:nat), option (nat*N)).
  Definition setalog nA (inst met : nat) (varg : N) i :=
      if (Nat.eqb inst i)
        then
          Some (met,varg)
        else
          nA i.
  Definition empty_Alog : Alog := fun i  => None.

  Lemma get_setalog_neq : forall l x y z i, x <> i -> (setalog l x y z) i = l i. 
    intros.
    unfold setalog.
    destruct (PeanoNat.Nat.eqb _ _) eqn:?.
    eapply Nat.eqb_eq in Heqb.
    lia.
    reflexivity.
  Qed.

  Open Scope N.

  Definition funop unop input :=
      match unop with
      | Fn s =>  sem_uninterp s input
      | PassCst => 0
      | Split1 => split1 input
      | Split2 => split2 input
      | BwNot i => N.lnot input i
      | BwSize i => N.modulo input (N.pow 2 i)
      end.

  Definition fbinop binop e1_result e2_result :=
      match binop with
      | Plus => e1_result + e2_result
      | Eq => N.b2n (N.eqb e1_result e2_result)
      | Lt => N.b2n (N.ltb e1_result e2_result)
      | Leq => N.b2n (N.leb e1_result e2_result)
      | Gt => N.b2n (negb (N.leb e1_result e2_result))
      | Geq => N.b2n (negb (N.ltb e1_result e2_result))
      | Merge => merge e1_result e2_result
      | BwAnd => N.land e1_result e2_result
      | BwOr => N.lor e1_result e2_result
      | ESeq => e2_result
      end.

  Implicit Type P : (Binders -> Vlog -> N -> Prop).
  Inductive step
    : Binders -> Vlog -> @expr varname -> Binders -> Vlog -> N -> Prop :=
  | DCst :
    forall B V n,
    step B V (ZOp (Cst n)) B V n
  | DArg :
    forall B V,
    step B V (Arg) B V called_args
  | DVar :
    forall B V v ,
    step B V (Var v) B V (B (idxvar v))
  | DSetVar :
    forall B V v e nB nV ret,
    step B V e nB nV ret -> 
    step B V (SetVar v e) (setb nB (idxvar v) ret) nV ret
  | DTernaryT :
    forall B V c t f nB nV cond nnB nnV ret ,
    step B V c nB nV cond->
    N.modulo cond 2 = 1 ->
    step nB nV t nnB nnV ret 
    -> step B V (Ternary c t f) nnB nnV ret
 | DTernaryF :
    forall B V c t f nB nV cond nnB nnV ret ,
    step B V c nB nV cond->
    N.modulo cond 2 = 0 ->
    step nB nV f nnB nnV ret 
    -> step B V (Ternary c t f) nnB nnV ret
  | DUnop' :
    forall B V unop e nB nV ret,
    step B V e nB nV ret 
    -> step B V (UOp unop e) nB nV (funop unop ret)
  | DBinop' :
    forall B V e1 e2 nB1 nV1 ret1 nB2 nV2 ret2 binop ,
    step B V e1 nB1 nV1 ret1 ->
    step nB1 nV1 e2 nB2 nV2 ret2 
    -> step B V (BOp binop e1 e2) nB2 nV2 (fbinop binop ret1 ret2)
  | DCall :
    forall B V (instance met : varname) arg nB nV varg rret,
    step B V arg nB nV varg ->
    (let spec := aget ModuleTable (idxvar instance) in
    let method_spec := aget (value_spec spec) (idxvar met) in
    nV (idxvar instance) (idxvar met) = None /\ 
    method_spec varg (aget st (idxvar instance)) rret)
    -> step B V (ValMethod instance met arg) nB (setvlog nV (idxvar instance) (idxvar met) varg) rret.

Fixpoint interp_step (B : Binders) (V : Vlog) (exp: @expr varname) (B' : Binders) (V' : Vlog) (ret : N) : Prop :=
  match exp with
  | ZOp (Cst n) =>
    (B = B') /\ (V' = V) /\ (ret = n)
  | Arg =>
    (B' = B) /\ (V' = V) /\ (ret = called_args)
  | Var v =>
    (B' = B) /\ (V' = V) /\ (ret = B (idxvar v))
  | SetVar v e =>
    exists nB nV, (interp_step B V e nB nV ret) /\ (B' = (setb nB (idxvar v) ret)) /\ (V' = nV)
  | Ternary c t (Abort) =>
    exists nB nV cond, (interp_step B V c nB nV cond) /\
    (N.modulo cond 2 = 1) /\ (interp_step nB nV t B' V' ret)
  | Ternary c t f =>
    exists nB nV cond, (interp_step B V c nB nV cond) /\
    (if N.modulo cond 2 =? 1 then (interp_step nB nV t B' V' ret) else (interp_step nB nV f B' V' ret))
  | UOp unop e =>
    exists ret', (interp_step B V e B' V' ret') /\ (ret = funop unop ret')
  | BOp binop e1 e2 =>
    exists nB nV ret1 ret2, (interp_step B V e1 nB nV ret1) /\ (interp_step nB nV e2 B' V' ret2) /\ (ret = fbinop binop ret1 ret2)
  | ValMethod instance met arg =>
    exists nV (varg : N), (interp_step B V arg B' nV varg) /\
    let spec := aget ModuleTable (idxvar instance) in
    let method_spec := aget (value_spec spec) (idxvar met) in ((nV (idxvar instance) (idxvar met) = None) /\ (method_spec varg (aget st (idxvar instance)) ret)) /\ (V' = (setvlog nV (idxvar instance) (idxvar met) varg))
  | Abort => False
  end.

Fixpoint interp_step_cps (B : Binders) (V : Vlog) (exp: @expr varname) (k: forall (B' : Binders) (V' : Vlog) (ret : N), Prop) : Prop :=
  match exp with
  | ZOp (Cst n) =>
    k B V n
  | Arg =>
    k B V called_args 
  | Var v =>
    k B V (B (idxvar v))
  | SetVar v e =>
    interp_step_cps B V e 
      (fun nB nV ret => k (setb nB (idxvar v) ret) nV ret)
  | Ternary c t (Abort) =>
    interp_step_cps B V c (fun nB nV cond =>
      (N.modulo cond 2 = 1) /\ (interp_step_cps nB nV t k))
  | Ternary c t f =>
    interp_step_cps B V c (fun nB nV cond =>
      (* (if N.modulo cond 2 =? 1 then (interp_step_cps nB nV t k) else (interp_step_cps nB nV f k))) *)
      (N.modulo cond 2 = 1 /\ (interp_step_cps nB nV t k)) \/
       N.modulo cond 2 = 0 /\ (interp_step_cps nB nV f k))
  | UOp unop e =>
    interp_step_cps B V e (fun B' V' ret' => k B' V' (funop unop ret'))
  | BOp binop e1 e2 =>
    interp_step_cps B V e1 
      (fun nB nV ret1 => interp_step_cps nB nV e2 (fun B' V' ret2 => k B' V' (fbinop binop ret1 ret2)))
  | ValMethod instance met arg =>
    interp_step_cps B V arg 
      (fun B' nV varg =>
        let spec := aget ModuleTable (idxvar instance) in
        let method_spec := aget (value_spec spec) (idxvar met) in 
        (* Find a way to remove this nv *)
        match  (nV (idxvar instance) (idxvar met)) with 
        | None => exists ret, 
        (method_spec varg (aget st (idxvar instance)) ret) /\
        k B' (setvlog nV (idxvar instance) (idxvar met) varg) ret
        | _ => False
        end)
  | Abort => False
  end.

Fixpoint interp_wpa_cps (B : Binders) (A : Alog) (V : Vlog) (act: @action varname) (k : forall (B' : Binders) (A' : Alog) (V' : Vlog), Prop) : Prop :=
  match act with
  | Expr e =>
    interp_step_cps B V e (fun B V ret => k B A V)
  | Seq s1 s2 =>
    interp_wpa_cps B A V s1 (fun nB nA nV => interp_wpa_cps nB nA nV s2 k)
  | Skip =>
     k B A V
  | If c t (Expr Abort) =>
    interp_step_cps B V c (fun nB nV cond =>
    N.modulo cond 2 = 1 /\ (interp_wpa_cps nB A nV t k))
  | If c t f =>
    interp_step_cps B V c (fun nB nV cond =>
    (* (if N.modulo cond 2 =? 1 then (interp_wpa_cps nB A nV t k) else (interp_wpa_cps nB A nV f k))) *)
    (N.modulo cond 2 = 1 /\ (interp_wpa_cps nB A nV t k)) \/
    (N.modulo cond 2 = 0 /\ (interp_wpa_cps nB A nV f k)))
  | ActionMethod instance met arg =>
    (* TODO call k*)
    (* (fun B' A' V' =>  *)
    interp_step_cps B V arg (fun B' V' varg =>
    (let spec := aget ModuleTable (idxvar instance) in
     let method_spec := aget (action_spec spec) (idxvar met) in
      match  A (idxvar instance) with 
      | None => 
      (* The guard is true (the method is callable) *)
      exists x, method_spec varg (aget st (idxvar instance)) x
      /\ k B' (setalog A (idxvar instance) (idxvar met) varg) V'
      | _ => False 
  end))
  end.


  Lemma inv_DSetVar: forall B V v e nB' nV' ret',
    step B V (SetVar v e) nB' nV' ret' ->
    exists nB nV ret, 
    step B V e nB nV ret 
    /\ nB' = (setb nB (idxvar v) ret)
    /\ nV'= nV 
    /\ ret' = ret.
    cleanup.
    inversion H.
    repeat eexists; eauto.
    Qed.

  Lemma inv_DCst: forall B V n nB' nV' ret',
    step B V (ZOp (Cst n)) nB' nV' ret' ->
    nB' = B 
    /\ nV'= V 
    /\ ret' = n.
    cleanup.
    inversion H.
    repeat eexists; eauto.
    Qed.

  Lemma inv_DAbort: forall B V nB' nV' ret',
    step B V (Abort) nB' nV' ret' ->
    False.
    cleanup.
    inversion H.
    Qed.


  Lemma inv_DArg :
    forall B V nB nV ret,
    step B V (Arg) nB nV ret -> 
    nB = B /\
    nV = V /\
    ret = called_args.
    cleanup; inversion H; repeat eexists; eauto.
    Qed.

  Lemma inv_DVar :
    forall B V v nB nV ret,
    step B V (Var v) nB nV ret ->
    nB = B /\
    nV = V /\
    ret = (B (idxvar v)).
    cleanup; inversion H; repeat eexists; eauto.
    Qed.
  
  Lemma inv_DUnop' :
    forall B V unop e nB nV ret',
    step B V (UOp unop e) nB nV ret' -> 
    exists ret,
    step B V e nB nV ret 
    /\ ret' = (funop unop ret).
    cleanup; inversion H; repeat eexists; eauto.
    Qed.
    
  Lemma inv_DBinop' :
    forall B V e1 e2 nB nV ret binop,
    step B V (BOp binop e1 e2) nB nV ret -> 
    exists nB1 nV1 ret1 ret2 ,
    step B V e1 nB1 nV1 ret1 /\
    step nB1 nV1 e2 nB nV ret2 /\
    ret = (fbinop binop ret1 ret2).
    cleanup; inversion H; repeat eexists; eauto.
    Qed.

  Lemma inv_DCall :
    forall B V instance met arg  nB nV' ret,
    step B V (ValMethod instance met arg) nB nV' ret ->
    exists varg nV,
    step B V arg nB nV varg /\
    nV' = (setvlog nV (idxvar instance) (idxvar met) varg) /\
    nV (idxvar instance) (idxvar met) = None /\ 
    (let spec := aget ModuleTable (idxvar instance) in
    let method_spec := aget (value_spec spec) (idxvar met) in
    method_spec varg (aget st (idxvar instance)) ret).
    cleanup; inversion H; repeat eexists; eauto.
    simpl in H9.
    cleanup.
    eauto.
    simpl in H9.
    cleanup.
    eauto.
    Qed.
    (* Useful inversion *)
  Lemma inv_DWhenExpr :
      forall B V c t nnB nnV ret ,
      step B V (Ternary c t Abort) nnB nnV ret ->
      exists ct nB nV,
      step B V c nB nV ct /\
      N.modulo ct 2 = 1 /\
      step nB nV t nnB nnV ret.
      cleanup.
     inversion H.
     cleanup; subst; clear H.
     2:{ 
        subst. inversion H10. }
       eexists; eauto.
    Qed.

 Lemma inv_DTernary :
  forall B V c t f nnB nnV ret ,
      step B V (Ternary c t f) nnB nnV ret ->
       exists nB nV cond,
      step B V c nB nV cond /\
      if N.eqb (N.modulo cond 2) 1 then 
      step nB nV t nnB nnV ret
      else 
      step nB nV f nnB nnV ret
      .
    cleanup; inversion H; repeat eexists; eauto; subst.
    rewrite H9.
    simpl; eauto.
    rewrite H9.
    simpl; eauto.
    Qed.

  Implicit Type Q : (Binders -> Alog -> Vlog -> Prop).
  Inductive wpa :
   Binders ->  Alog -> Vlog ->  @action varname -> Binders -> Alog -> Vlog -> Prop :=
    | DExpr' :
      forall B A V e nB nV ret,
      step B V e nB nV ret
      -> wpa B A V (Expr e) nB A nV 
    | DSeq' :
      forall B A V s1 s2 nB nA nV nnB nnA nnV,
      wpa B A V s1 nB nA nV ->
      wpa nB nA nV s2 nnB nnA nnV 
      -> wpa B A V (Seq s1 s2)  nnB nnA nnV
    | DSkip :
      forall B A V,
      wpa B A V Skip B A V
    | DIft :
      forall B A V c nB nV cond t f nnB nA nnV,
      step B V c nB nV cond ->
      N.modulo cond 2 = 1 -> 
      wpa nB A nV t nnB nA nnV 
      -> wpa B A V (If c t f) nnB nA nnV
    | DIff :
      forall B A V c nB nV cond t f nnB nA nnV ,
      step B V c nB nV cond ->
      N.modulo cond 2 = 0 -> 
      wpa nB A nV f nnB nA nnV 
      -> wpa B A V (If c t f) nnB nA nnV
    | DACall :
      forall B A V instance met arg nB nV varg ,
      step B V arg nB nV varg ->
      (let spec := aget ModuleTable (idxvar instance) in
      let method_spec := aget (action_spec spec) (idxvar met) in
        (A (idxvar instance) = None /\
        (* The guard is true (the method is callable) *)
        exists x, method_spec varg (aget st (idxvar instance)) x)
        )
      -> wpa B A V (ActionMethod instance met arg) nB (setalog A (idxvar instance) (idxvar met) varg) nV.

  Lemma inv_DExpr' :
      forall B A V e nB nA nV ,
      wpa B A V (Expr e) nB nA nV ->
    exists ret,
    step B V e nB nV ret /\
    nA = A.
    cleanup; inversion H; repeat eexists; eauto.
    Qed.

 Lemma inv_DSeq' :
      forall B A V s1 s2  nnB nnA nnV,
       wpa B A V (Seq s1 s2) nnB nnA nnV ->
       exists nB nA nV,
      wpa B A V s1 nB nA nV /\
      wpa nB nA nV s2 nnB nnA nnV.
    cleanup; inversion H; repeat eexists; eauto.
    Qed.

 Lemma inv_DIf  :
      forall B A V c t f nnB nnA nnV,
       wpa B A V (If c t f) nnB nnA nnV ->
       exists nB nV cond,
      step B V c nB nV cond /\
      if N.eqb (N.modulo cond 2) 1 then 
      wpa nB A nV t nnB nnA nnV
      else 
      wpa nB A nV f nnB nnA nnV
      .
    cleanup; inversion H; repeat eexists; eauto.
    rewrite H10.
    simpl; eauto.
    rewrite H10.
    simpl; eauto.
    Qed.

 Lemma inv_DSkip :
      forall B A V nnB nnA nnV,
       wpa B A V (Skip) nnB nnA nnV ->
       nnB = B /\ nnA = A /\ nnV = V.
    cleanup; inversion H; repeat eexists; eauto.
    Qed.
  
 Lemma inv_DACall :
      forall B A V instance met arg nB nnA nnV,
       wpa B A V (ActionMethod instance met arg) nB nnA nnV ->
       A (idxvar instance) = None /\
       exists nV varg, 
       step B V arg nB nV varg /\
       nnA = (setalog A (idxvar instance) (idxvar met) varg) /\
       nnV = nV /\
       (let spec := aget ModuleTable (idxvar instance) in
       let method_spec := aget (action_spec spec) (idxvar met) in
         exists x, method_spec varg (aget st (idxvar instance)) x).
    cleanup; inversion H.
    simpl in *.
    cleanup.
    split; eauto.
    subst.
    eexists.
    eexists.
    split; eauto.
    Qed.

    (* Useful inversion *)
  Lemma inv_DWhen :
      forall B A V c t nnB nnA nnV ,
      wpa B A V (If c t (Expr Abort)) nnB nnA nnV ->
      exists ct nB nV,
      step B V c nB nV ct /\
      N.modulo ct 2 = 1 /\
      wpa nB A nV t nnB nnA nnV.
      cleanup.
     inversion H.
     cleanup; subst; clear H.
     2:{ 
        subst. inversion H11.
        subst. inversion H4. }
       eexists; eauto.
    Qed.

  End Interp.

Section NewModule.
  Universe u.
  Universe v.
  Universe w.
  Definition lift_to submod (r : SModule@{w} -> SModule@{w} -> Prop)
    (bigs : SModule@{v}) 
    (nxt_bigs : SModule@{v}) : Prop :=
      exists (small:state_t@{v _}), 
        bigs = ({| T:= state_t@{v _}; state:=small:state_t@{v _}|}) /\
      exists (change_submod_small:SModule),
        (* nxt_bigs = ({| T:= state_t@{u _}; state:=nxt_small:state_t@{u _}|}) *)
        nxt_bigs = ({| T:= state_t@{v _}; state := aset small submod change_submod_small:state_t@{v _}|})
         /\
      r (aget small submod) change_submod_small 
      .

  (* First a one rule at a time description of the system *)
  Context {uninterp : Uninterpreted_Functions}.

  Context (ModuleTable : array (spec_module_t@{v _ _})).
  Definition nb_submodules := alength ModuleTable.
  Context (local_rules : list (@action varname)).
  Context (local_amethods: array (@action varname)).
  Context (local_vmethods: array (@expr varname)).

 Definition apply_alog st alog nxt_st :=
  (forall i, i < alength st ->
    match alog i with 
    | None =>  
        (aget st i) = (aget nxt_st i)
    | Some (id,arg) => 
      let small_module := aget ModuleTable i in 
      let small_module_step := aget (action_spec small_module) id in 
      small_module_step arg (aget st i) (aget nxt_st i)
    end) /\
    (forall x, (x >= alength nxt_st) -> values nxt_st x = default nxt_st) /\
    alength nxt_st = alength st /\
    default nxt_st = default st.


  Definition build_module : spec_module_t :=
  {|
      value_spec := amap unexisting_vmethod
        (fun vexpr =>
            fun arg (box_st : SModule@{u}) returned_value =>
            exists (st : state_t@{u _}) nB nV, box_st = {| T:= state_t@{u _} ; state := st|} /\
        (* exists (small:state_t@{u _}),  *)
        (* bigs = ({| T:= state_t@{u _}; state:=small:state_t@{u _}|}) /\ *)
            step st arg ModuleTable empty_B empty_Vlog vexpr nB nV returned_value)
        local_vmethods;
      action_spec :=
        amap unexisting_amethod
        (fun vexpr =>
          fun arg (box_st : SModule@{u}) (box_nxt_st : SModule@{u}) =>
            exists (st : state_t@{u _}) nxt_st nB nA nV, 
            (box_st = {| T:= _ ; state := st|})/\
            box_nxt_st = {| T:= _ ; state := nxt_st|} /\
            wpa st arg ModuleTable empty_B empty_Alog empty_Vlog vexpr nB nA nV  /\
            apply_alog st nA nxt_st) 
        local_amethods;
      rule_spec :=
        List.map
        (fun vexpr =>
          fun (box_st : SModule@{u}) (box_nxt_st : SModule@{u}) =>
            exists (st : state_t@{u _}) (nxt_st : state_t@{u _}) nB nA nV, box_st = {| T:= _ ; state := st|} /\
            box_nxt_st = {| T:= _ ; state := nxt_st |} /\
            wpa st 0 ModuleTable empty_B empty_Alog empty_Vlog vexpr nB nA nV /\
            apply_alog st nA nxt_st)
        local_rules;
      subrules_spec :=
      (* lift_to *)
      List.map (fun submod =>
        let sr_submod := (subrules_spec (aget ModuleTable submod)) in
        let all_sm_rules := rule_spec (aget ModuleTable submod)
          ++ concat 
          (List.map (fun el =>
           map (lift_to el)
           (List.nth el sr_submod [])) (seq 0 (length sr_submod))) 
          in
        all_sm_rules) (seq 0 (alength ModuleTable))|}.

  Lemma simplify_map : forall l l',
          map
          (fun el => map (lift_to el) (nth el (l ++ l') []))
          (seq 0 (length l)) = 
          map
          (fun el => map (lift_to el) (nth el l []))
          (seq 0 (length l)).
        induction l using rev_ind; cbn; intros; eauto.
        {
          rewrite !app_length.
          rewrite !seq_app.
          rewrite !map_app.
          rewrite <- app_assoc.
          cbn.
          rewrite !IHl.
          rewrite app_nth2 with (l:= l) (l' := x::l'); try lia.
          rewrite app_nth2 with (l:= l) (l' := [x]); try lia.
          replace (length l - length l) with 0 by lia.
          cbn.
          reflexivity.
        }
  Qed.
  Lemma simplify_concat :
    forall l i s nxt_S,
          nth i 
              (concat
               (map 
                (fun el =>
                  map
                    (lift_to el)
                    (nth el l []))
                (seq 0 (length l))))
                unexisting_rule s nxt_S ->
          exists sub_i sm_i, lift_to sub_i (nth sm_i (nth sub_i l []) unexisting_rule) s nxt_S .
      induction l using rev_ind; cbn.
      -
        intros.
        destruct i; contradiction H.
      -
        intros.
        erewrite app_length in H.
        erewrite seq_app in H.
        erewrite map_app in H.
        rewrite concat_app in H.
        cbn in H.
        rewrite app_nil_r in H.
        rewrite simplify_map in H.
        rewrite app_nth2 with (l:= l) (l' := [x]) in H; try lia.
        replace (length l - length l) with 0 in H by lia.
        cbn in H.
        remember (concat 
                        (map 
                          (fun el => map (lift_to el) (nth el l []))
                          (seq 0 (length l)))).
        assert (i < length l0 \/ i >= length l0) by lia.
        destruct H0.
        {
          erewrite app_nth1 in H; eauto.
          auto_specialize.
          cleanup.
          exists x0.
          exists x1.
          assert (x0 < length l \/ x0 >= length l) by lia.
          destruct H2.
          erewrite app_nth1; eauto.
          erewrite nth_overflow with (l := l) in H1; eauto.
          destruct x1; cbv in H1; cleanup; contradiction H4.
        }
        exists (length l).
        erewrite app_nth2 in H; eauto.
        erewrite app_nth2 ; eauto.
        replace (length l - length l) with 0 by lia.
        cbn.
        (* Search (nth _ (map _ _)). *)
        remember (i - length l0).
        assert (nth n (map (lift_to (length l)) x) (lift_to (length l) unexisting_rule) s nxt_S).
        assert (n < length x \/ n >= length x); try lia.
        destruct H1.
        2:{
          rewrite nth_overflow in H; try rewrite map_length; try lia.
          cbv in H; cleanup. contradiction H.
        }
        (* Search (nth). *)
        erewrite nth_indep; eauto.
        rewrite map_length; eauto.
        rewrite map_nth in H1.
        exists n.
        eauto.
  Qed.
    Lemma rewrite_concat :
    forall l i ,
    let lconcat := (concat
               (map 
                (fun el =>
                  map
                    (lift_to el)
                    (nth el l []))
                (seq 0 (length l)))) in
     exists sub_i sm_i, (i < length lconcat -> sub_i < length l) /\ 
          (forall s P,
            nth i 
             lconcat 
                unexisting_rule s P <->  
          lift_to sub_i (nth sm_i (nth sub_i l []) unexisting_rule) s P).
      induction l using rev_ind; cbn.
      -
        intros.
        eexists 0.
        eexists 0.
        split.
        intros.
        destruct i; lia.
        intros; split.
        intros.
        destruct i; contradiction H.
        cbn; eauto.
        unfold lift_to.
        intros.
        cleanup.
        rpn unexisting_rule wrong.
        contradiction wrong.
      -
        intros.
        erewrite app_length .
        erewrite seq_app .
        erewrite map_app .
        rewrite concat_app.
        (* rewrite app_nil_r . *)
        rewrite !simplify_map .
        specialize (IHl i).
        cbn in IHl.
        cleanup.
        remember (concat 
                        (map 
                          (fun el => map (lift_to el) (nth el l []))
                          (seq 0 (length l)))).
        assert (i < length l0 \/ i >= length l0) as case by lia.
        destruct case.
        {
          erewrite app_nth1; eauto.
          exists x0.
          exists x1.
          split.
          rewrite app_length.
          cbn; lia.
          intros.
          split.
          {
            intros.
            eapply H0 in H2.
            erewrite app_nth1; eauto.
          }
          {
            intros.
            eapply H0.
            erewrite app_nth1 in H2; eauto.
          }
        }
        {
          rewrite app_length.
          rewrite app_nth2; eauto.
          cbn.
          rewrite app_nth2; try lia.
          replace (length l - length l) with 0 by lia.
          cbn.
          rewrite app_nil_r. 
          rewrite map_length.
          exists (length l).
          eexists.
          split; intros; try lia.
          split.
          {
            rewrite app_nth2; try lia.
            replace (length l - length l) with 0 by lia.
            cbn.
            intros.
            unfold lift_to.
            erewrite nth_indep in H2.
            rewrite map_nth in H2.
            unfold lift_to in H2.
            cleanup.
            eexists.
            split; eauto.
            assert (i - length l0 < length (map (lift_to (length l)) x) \/
                  i - length l0 >= length (map (lift_to (length l))x) ) by lia.
            destruct H3; eauto.
            rewrite nth_overflow in H2; eauto.
            contradiction H2.
          }
          {
            intros.
            erewrite nth_indep.
            erewrite map_nth.
            unfold lift_to in H2 |- *.
            cleanup.
            instantiate (1:= unexisting_rule).
            erewrite app_nth2 in n; try lia.
            replace (length l - length l) with 0 in n by lia.
            cbn in n.
            eexists; split; eauto.
            unfold lift_to in H2.
            rewrite map_length.
            cleanup.
            erewrite app_nth2 in H4; try lia.
            replace (length l - length l) with 0 in H3 by lia.
            cbn in H3.
            assert ( i - length l0 < length x \/ i - length l0 >= length x) as case by lia.
            destruct case; eauto.
            rpn nth nth_ov.
            erewrite nth_overflow in nth_ov; eauto.
            contradiction nth_ov.
            simpl.
            assert (length l - length l = 0) as useq by lia. 
            rewrite useq.
            lia.
          }
        }
        Qed.
 
  Lemma nth_map : forall {T T'}  (l : list T)r (f : T -> T') (d : T') (d' : T),
     r < length l -> nth r (map f l) d = f (nth r l d').
     induction l; intros.
     -
     inversion H.
     -
     cbn in *.
     destruct r; eauto.
     assert (r < length l) by lia.
     eapply IHl; eauto.
  Qed.

  Lemma simplify_concat_rev:
    forall l s P,
    forall sub_i sm_i, 
    lift_to sub_i (nth sm_i (nth sub_i l []) unexisting_rule) s P ->
      exists i, 
          nth i 
              (concat
               (map 
                (fun el =>
                  map
                    (lift_to el)
                    (nth el l []))
                (seq 0 (length l))))
                unexisting_rule s P .
    induction l using rev_ind.
    {
      intros.
      unfold lift_to in H.
      cleanup.
      cbn in H0 |- *.
      rpn unexisting_rule wrong.
      destruct sub_i; destruct sm_i; cbv in wrong; contradiction wrong.
    }
    {
      intros.
      cbn in H.
      assert ( sub_i < length l \/ sub_i >= length l) as case by lia.
      destruct case.
      {
        rpn lift_to lift. 
        erewrite app_nth1 in lift; eauto.
        auto_specialize.
        rewrite app_length.
        rewrite seq_app.
        rewrite map_app.
        rewrite concat_app.
        cleanup.
        rewrite simplify_map.
        exists x0.
        match type of H with 
        | nth _ ?l _ _ _ => remember l
        end.
        assert (x0 < length l0 \/ x0 >= length l0) as case by lia.
        destruct case.
        {
          subst l0.
          erewrite app_nth1; eauto.
        }
        {
          rewrite nth_overflow in H; eauto.
          cbv in H.
          contradiction H.
        }
      }
      assert ( sub_i = length l \/ sub_i > length l) as case by lia.
      destruct case.
      {
        subst.
        rewrite app_nth2 in H; eauto.
        replace (length l - length l) with 0 in H by lia.
        cbn in H.
        unfold lift_to in H.
        cleanup.
        rewrite app_length.
        rewrite seq_app.
        rewrite map_app.
        rewrite concat_app.
        cbn.
        rewrite app_nth2 with (n:= length l); eauto.
        replace (length l - length l) with 0 by lia.
        cbn.
        rewrite app_nil_r.
        match goal with 
        | |- context[nth _ (?l ++ _) _ _ _] => remember l
        end.
        exists (length l0 + sm_i).
        rewrite app_nth2; try lia.
        replace (length l0 + sm_i - length l0) with sm_i by lia.
        assert (sm_i < length x \/ sm_i >= length x) as case by lia.
        destruct case.
        2:{
          rpn unexisting_rule wrong.
          erewrite nth_overflow in wrong; eauto.
          cbv in wrong.
          contradiction wrong.
        }
        erewrite nth_map; eauto.
        unfold lift_to.
        eexists; split; eauto.
      }
      erewrite nth_overflow with (n:= sub_i) in H.
      destruct sm_i; cbv in H.
      cleanup.
      contradiction H3.
      cleanup.
      contradiction H3.
      rewrite app_length; cbn. lia.
    }
  Qed.

End NewModule.

Definition vmethod_interaction :=
  (* method_id, arg , res  *)
(N * N * N)%type .
Definition amethod_interaction :=
  (* method_id, arg *)
(N * N)%type.

Record uomaat_t :=
   { vmethod_call: list vmethod_interaction;
     amethod_call: option amethod_interaction }.
(* TODO report bug: the universe are conservatively added *)

Section Trace.
  Universe u.
  Universe v.

  Context {uninterp : Uninterpreted_Functions}.
  Context (current_mod : spec_module_t).

  (* There exists a sequence of rules or subrules *)
  Inductive existSR :
      SModule@{u}  -> SModule@{u} -> Prop :=
    | existSR_done : forall initial, existSR initial initial 
    | existSR_substep :
      forall (initial:SModule@{u}) instance_i (mid : SModule@{u}) final subrules r spec_r,
      List.nth_error (subrules_spec current_mod) instance_i = Some subrules ->
      List.nth_error subrules r = Some spec_r ->
      (*  spec_r is acting on the submodule and not on initial and Mid so we lift it   *)
      (lift_to instance_i spec_r) initial mid ->
      (* spec_r initial true Mid -> *)
      existSR mid final ->
      existSR initial final 
    | existSR_step :
      forall initial r mid final,
      nth r (rule_spec current_mod) unexisting_rule initial mid ->
      existSR mid final ->
      existSR initial final.
End Trace.

Section Refines.
  Universe u v.
  Context (mi: spec_module_t@{u _ _}).
  Context (ms: spec_module_t@{v _ _}).
  (* Context (pf_dir_a : module_am_direct ms). *)

  Definition indistinguishable (init_i : SModule@{u}) (init_s : SModule@{v}) :=
    (forall arg method_id ret,
      (aget (value_spec mi) method_id) arg init_i ret ->
      (aget (value_spec ms) method_id) arg init_s ret) /\
    (forall arg method_id new_st_i,
      (aget (action_spec mi) method_id) arg init_i new_st_i ->
      exists new_st_s,
      (aget (action_spec ms) method_id) arg init_s new_st_s).

  Definition refines (relation : SModule@{u} -> SModule@{v} -> Prop) :=
    forall (init_i : SModule@{u}) (init_s : SModule@{v}),
    relation init_i init_s ->
    indistinguishable init_i init_s ->
    (* Any action method preserve the indistinguishability *)
    (forall method_id arg mid_i,
      (aget (action_spec mi) method_id) arg init_i mid_i ->
      exists almost_mid_s mid_s, 
      (aget (action_spec ms) method_id) arg init_s almost_mid_s /\
      existSR ms almost_mid_s mid_s /\
      relation mid_i mid_s /\ indistinguishable mid_i mid_s)
    /\
    (* Any rule preserve the indistinguishability *)
    (forall r mid_i,
      (List.nth r (rule_spec mi) unexisting_rule) init_i mid_i ->
      exists mid_s, 
      existSR ms init_s mid_s /\
      relation mid_i mid_s /\ indistinguishable mid_i mid_s) /\
    (* Any subrule preserve the indistinguishability *)
    (forall sm r mid_i,
      (lift_to sm (List.nth r (List.nth sm (subrules_spec mi) []) unexisting_rule)) init_i mid_i ->
      exists mid_s,
      existSR ms init_s mid_s /\
      relation mid_i mid_s /\ indistinguishable mid_i mid_s).
End Refines.

Section LemmaNth.
  Lemma nth_error_notNoneIsSome : forall {T : Type} n (l : list T) ,
    nth_error l n <> None ->
    exists x, nth_error l  n = Some x .
    induction n; intros.
    -
      destruct l.
      cbn in *.
      contradiction H.
      reflexivity.
      exists t.
      reflexivity.
    -
      destruct l.
      cbn in *.
      contradiction H.
      reflexivity.
      cbn in *.
      eapply IHn;eauto.
    Qed.
End LemmaNth.

Section RefinementTheorem.
  Context {uninterp : Uninterpreted_Functions}.

  Context (local_rules : list (@action varname)).
  Context (local_amethods: array (@action varname)).
  Context (local_vmethods: array (@expr varname)).
  Context (ModuleTableI : array (spec_module_t)).

  Context (hole_idx : nat).
  Context (hole_reasonable : PeanoNat.Nat.lt hole_idx (alength ModuleTableI)).
  Definition mi : spec_module_t:=
    aget ModuleTableI hole_idx.
  Hint Unfold mi : refinement.

  Context (ms: spec_module_t).

  Context (v_same_length : alength(value_spec ms) =  alength (value_spec mi)).
  Context (a_same_length : alength(action_spec ms) = alength (action_spec mi)).
  Context (v_same_default : default(value_spec ms) =  default(value_spec mi)).
  Context (a_same_default : default(action_spec ms) = default(action_spec mi)).

  Context (relation: SModule -> SModule -> Prop).

  Definition ModuleTableS :
   array (spec_module_t) :=
     aset ModuleTableI hole_idx ms.
  Definition relation_big (xl: state_t) (yl: state_t) :=
                    alength xl = alength ModuleTableI /\
                    alength yl = alength ModuleTableS /\
                    default xl = default yl /\
                    (forall instance, instance <> hole_idx ->
                     aget xl instance = aget yl instance) /\
                      (let xh := aget xl hole_idx in
                       let yh := aget yl hole_idx in
                       relation xh yh /\ indistinguishable mi ms xh yh).
  Hint Unfold relation_big : refinement.


  Definition smodule := build_module ModuleTableS local_rules local_amethods local_vmethods.
  Definition imodule := build_module ModuleTableI local_rules local_amethods local_vmethods.


  Lemma v_length_equal : forall instance,
    alength (value_spec (aget ModuleTableS instance))  = alength (value_spec (aget ModuleTableI instance)).
    unfold ModuleTableS.
    intros.
    destruct (Nat.eq_dec hole_idx instance).
    rewrite e.
    erewrite get_set_eq; try lia.
    rewrite v_same_length.
    unfold mi.
    rewrite e; eauto.
    erewrite get_set_neq; try lia.
  Qed.

  Lemma a_length_equal : forall instance,
    alength (action_spec (aget ModuleTableS instance))  = alength (action_spec (aget ModuleTableI instance)).
    unfold ModuleTableS.
    intros.
    destruct (Nat.eq_dec hole_idx instance).
    rewrite e.
    erewrite get_set_eq; try lia.
    rewrite a_same_length.
    unfold mi.
    rewrite e; eauto.
    erewrite get_set_neq; try lia.
  Qed.
  Hint Resolve v_length_equal a_length_equal : refinement.

  Lemma v_default_equal : forall instance,
    default (value_spec (aget ModuleTableS instance))  = default (value_spec (aget ModuleTableI instance)).
    unfold ModuleTableS.
    intros.
    destruct (Nat.eq_dec hole_idx instance).
    rewrite e.
    erewrite get_set_eq; try lia.
    rewrite v_same_default.
    unfold mi.
    rewrite e; eauto.
    erewrite get_set_neq; try lia; eauto.
  Qed.

  Lemma a_default_equal : forall instance,
    default (action_spec (aget ModuleTableS instance))  = default (action_spec (aget ModuleTableI instance)).
    unfold ModuleTableS.
    intros.
    destruct (Nat.eq_dec hole_idx instance).
    rewrite e.
    erewrite get_set_eq; try lia.
    rewrite a_same_default.
    unfold mi.
    rewrite e; eauto.
    erewrite get_set_neq; try lia; eauto.
  Qed.
  Hint Resolve v_length_equal a_length_equal : refinement.

  Lemma wp_I_to_S: forall x0 arg action P b v nB nV ,
    step x0 arg ModuleTableI b v action nB nV P  ->
    forall x1,
    relation_big x0 x1  ->
    step x1 arg ModuleTableS b v action nB nV P.
    induction 1; try solve [econstructor; eauto].
    intros.
    econstructor; eauto.
    unfold ModuleTableS in *.
    cleanup.
    split; eauto.
    remember (idxvar instance) as instance'.
    destruct (Nat.eq_dec  instance' hole_idx) eqn:?.
    {
      unfold relation_big, indistinguishable, mi in *.
      subst.
      rewrite <- e.
      rewrite get_set_eq; try lia.
      auto_specialize.
      cleanup.
      rewrite <- e in H7.
      repeat (try auto_specialize; cleanup).
      eauto.
    }
    {
      unfold relation_big, indistinguishable, mi in *.
      repeat split; eauto.
      intros; repeat (try auto_specialize; cleanup).
      rewrite get_set_neq; try lia.
      rewrite <- H5; eauto.
    }
    Qed.

  Lemma wpa_I_to_S: forall x0 arg action nB nA nV,
    wpa x0 arg ModuleTableI empty_B empty_Alog empty_Vlog action nB nA nV ->
    forall x1,
    relation_big x0 x1  ->
    wpa x1 arg ModuleTableS empty_B empty_Alog empty_Vlog action nB nA nV.
    induction 1; try solve [econstructor; eauto].
    intros.
    -
      econstructor; try eapply wp_I_to_S; eauto.
    -
      econstructor; try eapply wp_I_to_S; eauto.
    -
      intros.
      unfold relation_big in H0.
      unfold indistinguishable in H0.
      cleanup.
      eapply DIff.
      eauto.
      eapply wp_I_to_S; eauto.
      eauto.
      repeat auto_specialize.
      eauto.
    -
      intros.
      unfold relation_big in H0.
      unfold indistinguishable in H0.
      cleanup.
      econstructor.
      eapply wp_I_to_S; eauto.
      split; eauto.
      rpn relation_big rl.
      unfold relation_big in rl.
      cleanup.
      unfold indistinguishable in *.
      cleanup.
      destruct (Nat.eq_dec hole_idx (idxvar instance)) eqn:?.
      {
        subst.
        repeat auto_specialize.
        unfold ModuleTableS.
        rewrite e.
        rewrite get_set_eq; try lia.
        rewrite e in H8.
        eapply H8.
        unfold mi.
        rewrite e.
        exact H2.
      }
      {
        clear Heqs.
        eapply not_eq_sym in n.
        unfold ModuleTableS.
        rewrite get_set_neq; try lia.
        repeat auto_specialize.
        rpn (aget x0 (idxvar instance) = aget x1 (idxvar instance)) eq.
        rewrite <- eq.
        eauto.
      }
      Qed.

  Context (i_refines_s : refines mi ms
                               (fun x y => relation x y)).

  Lemma access_rule : forall {A} (l : list (list A)) i sr r s,
        nth_error l i = Some sr ->
        nth_error sr r = Some s ->
        exists ir, nth_error (concat l) ir = Some s.
     induction l.
     -
       intros.
       destruct i; inversion H.
     -
       intros.
       destruct i; simpl in H.
       inversion H.
       subst.
       exists r.
       unfold concat.
       rewrite nth_error_app1; eauto.
       eapply nth_error_Some.
       erewrite H0.
       easy.
       rewrite concat_cons.
       auto_specialize.
       auto_specialize.
       cleanup.
       exists (x + length a).
       erewrite nth_error_app2.
       replace (x + length a - length a) with x by lia.
       eauto.
       lia.
  Qed.

  
  Lemma exist_list : forall (x : state_t) (end_x_i : state_t) ,
      default x = default end_x_i ->
      alength x = alength ModuleTableS ->
      alength end_x_i = alength ModuleTableI ->
      (forall instance : nat,
          instance <> hole_idx -> aget end_x_i instance = aget x instance) ->
      forall mid_s,
      existSR ms (aget x hole_idx) mid_s ->
      relation (aget end_x_i hole_idx) mid_s ->
      indistinguishable mi ms (aget end_x_i hole_idx) mid_s ->
      exists mid, 
      existSR smodule {| T := state_t; state := x |} {| T := state_t; state := mid |} /\
      relation_big end_x_i mid /\
      indistinguishable imodule smodule {| T := state_t; state := end_x_i |} {| T := state_t; state := mid |}.
    intros.
    remember (aget x hole_idx) in H3.
    generalize dependent end_x_i.
    generalize dependent x.
    match goal with
    | H:existSR _ _ ?f|- _ => induction H; intros
    end.
    {
      subst.
      exists x.
      split.
      econstructor.
      split.
      {
        unfold relation_big.
        do 3 (split; eauto).
      }
      {
        unfold indistinguishable in *.
        split.
        {
          intros.
          unfold smodule in *.
          unfold imodule in *.
          simpl in *.
          rpn ModuleTableI precond.
          destruct (method_id <? alength local_vmethods) eqn:?; autorewrite with fwd_rewrites in *; eauto.
          2:{ erewrite get_amap_out in precond; eauto; contradiction precond. }
          rewrite get_amap_in in precond |- *; eauto. 
          cleanup.
          inverseAll.
          subst.
          do 3 eexists.
          split;eauto.
          eapply wp_I_to_S; eauto.
          repeat split; eauto.
        }
        {
          intros.
          unfold smodule in *.
          unfold imodule in *.
          simpl in *.
          rpn ModuleTableI precond.
          destruct (method_id <? alength local_amethods) eqn:?; autorewrite with fwd_rewrites in *; eauto.
          2:{ erewrite get_amap_out in precond; eauto; contradiction precond. }
          rewrite get_amap_in in precond |- *; eauto. 
          cleanup.
          inverseAll.
          subst.
          rpn apply_alog alog.
          cleanup.
          unfold apply_alog in *.
          cleanup.
          assert (hole_idx < alength x0) as ineq by lia.
          rpn ModuleTableI alog.
          pose proof (alog _ ineq) as alog_hole.
          (* A little bit painful, case analysis if actually is an update *)
          destruct (x3 hole_idx) eqn:eq_h.
          {
            destruct p.
            rpn (action_spec mi) aspec. 
            rpn ModuleTableI pr. 
            pose proof (aspec _ _ _ pr).
            cleanup. 
            do 2 eexists.
            eexists (aset x1 hole_idx x5).
            do 3 eexists.
            split;eauto.
            split;eauto.
            split;eauto.
            eapply wpa_I_to_S; eauto.
            repeat split; eauto.
            split.
            {
              intros.
              rewrite H0 in H6.
              rewrite  H1 in alog.
              repeat auto_specialize' alog.
              destruct (x3 i) eqn:eqn2.
              {
                destruct p.
                destruct (Nat.eq_dec i hole_idx).
                {
                  subst.
                  rewrite get_set_eq; try lia.
                  unfold ModuleTableS.
                  rewrite get_set_eq; try lia.
                  eauto.
                  repeat auto_specialize' H5.
                  rewrite eq_h in eqn2.
                  inversion eqn2.
                  subst; eauto.
                }
                {
                  rewrite get_set_neq; eauto.
                  unfold ModuleTableS.
                  rewrite get_set_neq; eauto.
                  erewrite <- H2; eauto.
                }
              }
              {
                destruct (Nat.eq_dec i hole_idx).
                {
                  subst.
                  rewrite eqn2 in eq_h; inversion eq_h.
                }
                {
                  rewrite get_set_neq; eauto.
                  erewrite <- H2; eauto.
                }
              }
            }
            {
              repeat split;simpl; eauto; try lia.
              assert (hole_idx <? alength x1 = true) .
              eapply Nat.ltb_lt.
              lia.
              rewrite H6.
              intros.
              assert (hole_idx =? x6 = false).
              eapply Nat.eqb_neq.
              lia.
              rewrite H12.
              eapply H7; eauto.
              rewrite H10.
              eauto.
            }
          }
          {
            rpn (action_spec mi) aspec. 
            rpn ModuleTableI pr. 
            do 2 eexists.
            eexists (aset x1 hole_idx (aget x hole_idx) ).
            do 3 eexists.
            split;eauto.
            split;eauto.
            split;eauto.
            eapply wpa_I_to_S; eauto.
            repeat split; eauto.
            split.
            2:{
              repeat split;simpl; eauto; try lia.
              rpn (default x1 = default x0) rw.
              intros.
              assert (hole_idx <? alength x1 = true) .
              eapply Nat.ltb_lt.
              lia.
              rewrite H6.
              assert (hole_idx =? x5 = false).
              eapply Nat.eqb_neq.
              lia.
              rewrite H10.
              eapply H7; eauto.
              rewrite H10.
              eauto.
            }
            {
              intros.
              rewrite H0 in H5.
              rewrite  H1 in pr.
              repeat auto_specialize' pr.
              destruct (x3 i) eqn:eqn2.
              {
                destruct p.
                destruct (Nat.eq_dec i hole_idx).
                {
                  subst.
                  rewrite eqn2 in eq_h; inversion eq_h.
                }
                {
                  unfold ModuleTableS.
                  rewrite get_set_neq; eauto.
                  rewrite get_set_neq; eauto.
                  erewrite <- H2; eauto.
                }
              }
              {
                eauto.
                destruct (Nat.eq_dec i hole_idx).
                {
                  subst.
                  rewrite get_set_eq; try lia.
                  eauto.
                }
                {
                  rewrite get_set_neq; try lia.
                  erewrite <- H2; eauto.
                }
              }
            }
          }
        }
      }
    }
    {
      pose proof @access_rule.
      auto_specialize.
      auto_specialize.
      assert (exists lss, nth_error (subrules_spec smodule) hole_idx = Some lss).
      {
        unfold smodule.
        eapply nth_error_notNoneIsSome.
        eapply nth_error_Some.
        cbn.
        rewrite map_length.
        rewrite seq_length.
        lia.
      }
      cleanup.
      assert (x0 = rule_spec ms 
            ++ concat ( map 
                (fun el => map (lift_to el) (nth el (subrules_spec ms) [])) 
                (seq 0 (length (subrules_spec ms))))).
      {
        rpn (subrules_spec smodule) s.
        simpl in s.
        erewrite map_nth_error with (d:= hole_idx) in s.
        inversion s.
        unfold ModuleTableS.
        rewrite !get_set_eq.
        reflexivity.
        lia.
        eapply nth_error_seq.
        lia.
      }
      pose proof @access_rule as ar.
      rewrite H11 in H10.
      match type of H10 with 
      |  context[concat ?l] => assert (nth_error l instance_i =Some (map (lift_to instance_i) (nth instance_i (subrules_spec ms) [])))
      end.
      erewrite map_nth_error.
      reflexivity.
      eapply nth_error_seq; eauto.
      eapply nth_error_Some; try congruence.
      clear H11.
      specialize (ar) with (1:= H12).
      specialize (ar r (lift_to instance_i spec_r)).
      replace (nth _ _ _) with  subrules in ar.
      erewrite map_nth_error in ar; eauto.
      specialize (ar eq_refl).
      cleanup.
      2:{
          erewrite nth_error_nth' in H.
          inversion H.
          reflexivity.
          assert (nth_error (subrules_spec ms) instance_i <> None).
          rewrite H.
          easy.
          eapply nth_error_Some in H11.
          eauto.
      }
      pose proof H1 as lift_to_original. (* original lift_to instance_i spec_r initial mid*) 
      unfold lift_to in H1.
      cleanup.
      subst.
      (* specialize (IHexistSR (aset end_x_i hole_idx ({| T := state_t; state := x4 |} ))). *)
      specialize (IHexistSR (aset x hole_idx {| T:=_ ; state:=(aset x3 instance_i x4) |} )).
      simpl in IHexistSR.
      repeat auto_specialize' IHexistSR.
      erewrite get_set_eq in IHexistSR.
      repeat auto_specialize' IHexistSR.
      assert ((forall instance : nat,
             instance <> hole_idx ->
             aget end_x_i instance = aget (aset x hole_idx {| T := state_t; state := aset x3 instance_i x4 |}) instance)).
      {
        intros. erewrite get_set_neq; eauto.
      }
      repeat auto_specialize' IHexistSR.
      cleanup.



      eexists x5.
      split.
      eapply (existSR_substep ) with (r:= x2 + length (rule_spec ms)).
      eauto.
      instantiate (1:= lift_to instance_i spec_r).
      rewrite nth_error_app2.
      replace (x2 + _ - _) with x2 by lia.
      eauto.
      lia.
      {
         unfold lift_to in *.
         cleanup.
         subst.
         eexists.
         split.
         reflexivity.
         eexists ({| T:= _; state:= aset x3 instance_i x4|}).
         split.
         eauto.
         eexists.
         split; eauto.
      }
      eauto.
      split; eauto.
      rewrite H2.
      unfold ModuleTableS; simpl; lia.
    }
    {
     pose proof existSR_substep as gen.
     specialize (gen) with 
          (instance_i := hole_idx)
          (r:= r)
          (current_mod := smodule).
      unfold smodule in gen.
      simpl in gen.


      erewrite map_nth_error with (d:= hole_idx) in gen.
      2:{ eapply nth_error_seq; eauto. }
      destruct (r <? length (rule_spec ms)) eqn:?; autorewrite with fwd_rewrites in *; eauto.             
      2:{erewrite nth_overflow in H; eauto.
        contradiction H.
      }
      specialize (gen) with (1:= eq_refl).
      erewrite nth_error_app1 in gen; eauto.
      erewrite nth_error_nth' with (d:= unexisting_rule) in gen; eauto.
      all: unfold ModuleTableS.
      all: try rewrite get_set_eq.
      all: eauto.
      specialize (gen) with (1:= eq_refl).
      unfold lift_to in gen.

      specialize (IHexistSR (aset x hole_idx mid)).
      specialize (IHexistSR) with (1:= H0).
      specialize (IHexistSR) with (2:= H1).
      specialize (IHexistSR) with (2:= H2).
      assert ((forall instance : nat, instance <> hole_idx -> aget end_x_i instance = aget (aset x hole_idx mid) instance)) as frl.
      {
        intros.
        erewrite get_set_neq;eauto.
      }
      specialize (IHexistSR) with (2:= frl).
      specialize (IHexistSR) with (2:= H5).
      specialize (IHexistSR) with (2:= H6).
      erewrite get_set_eq in IHexistSR.
      2:{ rewrite H0; unfold ModuleTableS; simpl; lia. }
      specialize (IHexistSR eq_refl).
      cleanup.


      specialize (gen {| T := state_t; state := x |} ).
      eexists x0.
      split; eauto.
      eapply gen.
      2:{ eapply H7. }
      eexists; split ;eauto.
      eexists; split ;eauto.
      {

        unfold ModuleTableS.

        erewrite get_set_eq.
        2:{ lia. }
        rewrite <- Heqs.
        eauto.
      }
    }
    Qed.


  Lemma indistinguishable_preserved : forall x1 x0 x sm (sm_in : sm < alength ModuleTableI)
    (length_eq: alength x0 = alength x1) , 
    sm <> hole_idx ->
    indistinguishable imodule smodule {| T:=state_t; state := x1 |} {| T:=state_t; state := x0 |} ->
    relation_big (aset x1 sm x) (aset x0 sm x) ->
    indistinguishable imodule smodule 
        {| T:=state_t; state := aset x1 sm x |}
        {| T:=state_t; state := aset x0 sm x |}.
      intros.
      unfold indistinguishable.
      split; unfold imodule, smodule.
      {
        simpl.
        intros.
        assert (method_id < alength local_vmethods \/ method_id >= alength local_vmethods) as method_id_eq by lia.
        destruct method_id_eq. 
        2:{
         rewrite get_amap_out in *; eauto.
        }
        rewrite get_amap_in in *; eauto.
        cleanup.
        inverseAll.
        subst.
        do 3 eexists.
        split; eauto.
        eapply wp_I_to_S; eauto.

      }
      {
        simpl.
        unfold apply_alog in *.
        intros.

        assert (method_id < alength local_amethods \/ method_id >= alength local_amethods) as method_id_eq by lia.
        destruct method_id_eq. 
        2:{
          rpn unexisting_amethod absurd.
          unshelve rewrite get_amap_out in absurd; eauto.
          contradiction.
        }
        rewrite get_amap_in in *; eauto.

        cleanup.
        inverseAll.
        subst.
        cleanup.
        unfold refines in i_refines_s.
        {
          pose proof H1 as rlbig.
          unfold relation_big in H1.
          cleanup.
          erewrite !get_set_neq in H11; eauto.
          erewrite !get_set_neq in H12; eauto.

          repeat auto_specialize' i_refines_s.
          destruct i_refines_s.
          clear H14.
          rpn wpa rm. 
          move rm at top.

          rpn x5 carac.
          pose proof (carac hole_idx).
          simpl in *.
          rewrite  H1 in H5.
          specialize H5 with (1:= hole_reasonable).
          destruct (x5 hole_idx) eqn:?rmeq.
          {
            destruct p.
            rewrite get_set_neq in H5; eauto.
            repeat auto_specialize' H13.
            clear i_refines_s.
            cleanup.
            do 2 eexists.
            exists (aset x3 hole_idx x2).
            do 3 eexists.
            split; eauto.
            split; eauto.
            split.
            eapply wpa_I_to_S; eauto.
            split; eauto.
            {
              intros ? lt.
              simpl in *.
              rewrite H2 in lt; rewrite H1 in carac.
              specialize (carac _ lt).
              destruct (x5 i) eqn:sndeq.
              {
                destruct p.
                unfold ModuleTableS.
                destruct (Nat.eq_dec i hole_idx).
                {
                  subst; erewrite get_set_eq; try lia.
                  rewrite sndeq in rmeq; inversion rmeq.
                  subst.
                  erewrite get_set_neq; eauto.
                  erewrite get_set_eq; eauto.
                  lia.
                }
                {
                  erewrite get_set_neq; eauto.
                  erewrite <- H10; eauto.
                  (* Remember subexp to avoid spurious matching *)
                  remember (aset x1 sm x). 
                  erewrite get_set_neq ; eauto.
                }
              }
              {
                unfold ModuleTableS.
                destruct (Nat.eq_dec i hole_idx).
                {
                  subst; erewrite get_set_eq; try lia.
                  rewrite sndeq in rmeq; inversion rmeq.
                }
                {
                  remember (aset x0 sm x). 
                  erewrite get_set_neq; eauto.
                  subst a.
                  erewrite <- H10; eauto.
                }
              }
            }
            {
              repeat split; simpl; try congruence; eauto.
              assert (hole_idx <? alength x3 = true).
              rewrite H8.
              eapply Nat.ltb_lt.
              lia.
              rewrite H16.
              intros.
              assert (hole_idx =? x8 = false).
              eapply Nat.eqb_neq. 
              lia.
              rewrite H18.
              eauto.
            }
          }
          {
            do 2 eexists.
            exists (aset x3 hole_idx (aget x0 hole_idx)).
            do 3 eexists.
            split; eauto.
            split; eauto.
            split.
            eapply wpa_I_to_S; eauto.
            split; eauto.
            {
              intros ? lt.
              simpl in *.
              rewrite H2 in lt; rewrite H1 in carac.
              specialize (carac _ lt).
              destruct (x5 i) eqn:sndeq.
              {
                destruct p.
                unfold ModuleTableS.
                destruct (Nat.eq_dec i hole_idx).
                {
                  subst; erewrite get_set_eq; try lia.
                  rewrite sndeq in rmeq; inversion rmeq.
                }
                {
                  erewrite get_set_neq; eauto.
                  erewrite <- H10; eauto.
                  (* Remember subexp to avoid spurious matching *)
                  remember (aset x1 sm x). 
                  erewrite get_set_neq ; eauto.
                }
              }
              {
                unfold ModuleTableS.
                destruct (Nat.eq_dec i hole_idx).
                {
                  subst; erewrite get_set_eq; try lia.
                  erewrite get_set_neq; try eauto.
                }
                {
                  remember (aset x0 sm x). 
                  erewrite get_set_neq; eauto.
                  subst a.
                  erewrite <- H10; eauto.
                }
              }
            }
            {
              repeat split; simpl; try congruence; eauto.
              assert (hole_idx <? alength x3 = true).
              rewrite H8.
              eapply Nat.ltb_lt.
              lia.
              rewrite H6.
              intros.
              assert (hole_idx =? x2 = false).
              eapply Nat.eqb_neq. 
              lia.
              rewrite H15.
              eauto.
            }
          }
        }
      }
      
      Qed.


  Theorem refinenement_theorem : refines imodule smodule
                  (fun x y =>
                    exists xl, exists yl, x = {| T := state_t; state := xl|} /\ y = {| T:= state_t; state := yl|}
                    /\
                  relation_big xl yl).
    unfold refines.
    intros.
    cleanup.
    split.
    {
      intros.
      unfold imodule in *.
      unfold smodule in *.
      simpl in *.
      unfold apply_alog in *.
      destruct (method_id <? alength local_amethods) eqn:?;
      autorewrite with fwd_rewrites in *.
      2:{
        rewrite get_amap_out in H3 .
        contradiction H3.
        lia.
      }
      rewrite get_amap_in in H3; eauto.
      rewrite get_amap_in ; eauto.
      cleanup.
      subst.
      rpn relation_big bigr.
      pose proof bigr as bigr'.
      unfold relation_big in bigr'.
      cleanup.
      unfold refines in i_refines_s.
      repeat auto_specialize' i_refines_s.
      destruct i_refines_s.
      clear i_refines_s.
      clear H13.
      inverseAll.
      subst.
      unshelve epose proof (H6 hole_idx _).
      { lia. }
      destruct (x4 hole_idx) eqn:rmb1.
      {
        destruct p.
        repeat auto_specialize' H12. 
        cleanup.
        epose proof (exist_list (aset x2 hole_idx x) x2) as key_lemma.
        simpl in key_lemma.
        erewrite get_set_eq in key_lemma.
        specialize (key_lemma) with (5:= H13).
        specialize (key_lemma) with (5:= H14).
        specialize (key_lemma) with (5:= H15).
        assert ((forall instance : nat, instance <> hole_idx -> aget x2 instance = aget (aset x2 hole_idx x) instance)).
        {
          intros.
          erewrite get_set_neq; eauto.
        }
        rewrite !H8 in key_lemma.
        2:{ rewrite H8; lia.  }
        repeat auto_specialize' key_lemma.
        clear H16.
        cleanup.
        do 2 eexists.
        split.
        2:{
          split.
          2:{
            split.
            2:{
              eapply H18.
            }
            repeat split; eauto.
          }
          eauto.
        }
        do 5 eexists.
        repeat split; eauto.
        eapply wpa_I_to_S.
        eauto.
        eauto.
        all: simpl. 
        intros.
        {
          specialize (H6 i).
          rewrite H1 in H19; rewrite H in H6.
          simpl in *.
          specialize (H6 H19).
          destruct (x4 i) eqn:rmb.
          {
            destruct p.
            destruct (Nat.eq_dec hole_idx i).
            {
              subst.
              erewrite get_set_eq; try lia.
              rewrite rmb1 in rmb; inversion rmb.
              subst.
              unfold ModuleTableS.
              erewrite get_set_eq; try lia.
              eapply H12.
            }
            {
              unfold ModuleTableS.
              erewrite !get_set_neq; try lia.
              erewrite <- H4; eauto.
            }
          }
          {
            destruct (Nat.eq_dec hole_idx i).
            {
              subst.
              rewrite rmb1 in rmb; inversion rmb.
            }
            {
              erewrite !get_set_neq; try lia.
              erewrite <- H6.
              erewrite H4; eauto.
            }
          }
        }
        {
          intros.
          assert (hole_idx <? alength x2 = true).
          rewrite H8.
          eapply Nat.ltb_lt.
          lia.
          rewrite H20.
          intros.
          assert (hole_idx =? x8 = false).
          eapply Nat.eqb_neq. 
          lia.
          rewrite H21.
          eauto.
        }
        (* TODO a tactic for length and defaults! *)
        rewrite H8, H, H1; simpl; try lia.
        rewrite H9, H2; simpl; try lia; reflexivity.
      }
      {
        epose proof (exist_list (aset x2 hole_idx (aget x0 hole_idx)) x2) as key_lemma.
        simpl in key_lemma.
        erewrite get_set_eq in key_lemma.
        assert (aget x1 hole_idx = aget x2 hole_idx).
        { eauto.  }
        rewrite H13 in H10.
        rewrite H13 in H11.

        specialize (key_lemma) with (6:= H10).
        specialize (key_lemma) with (6:= H11).
        assert (existSR ms (aget x0 hole_idx) (aget x0 hole_idx)) by econstructor.
        specialize (key_lemma) with (5:= H14).
        erewrite H8 in key_lemma.

        repeat auto_specialize' key_lemma.
        assert ((forall instance : nat, instance <> hole_idx -> aget x2 instance = aget (aset x2 hole_idx (aget x0 hole_idx)) instance)).
        {
          intros.
          erewrite get_set_neq; eauto.
        }
        repeat auto_specialize' key_lemma.
        2:{ rewrite H8; lia.  }
        cleanup.
        clear H15 H12.
        do 2 eexists.
        split.
        2:{
          split.
          2:{
            split.
            2:{
              eapply H18.
            }
            repeat split; eauto.
          }
          eauto.
        }
        do 5 eexists.
        repeat split; eauto.
        eapply wpa_I_to_S.
        eauto.
        eauto.
        all: simpl. 
        intros.
        {
          specialize (H6 i).
          rewrite H1 in H12; rewrite H in H6.
          simpl in *.
          specialize (H6 H12).
          destruct (x4 i) eqn:rmb.
          {
            destruct p.
            destruct (Nat.eq_dec hole_idx i).
            {
              subst.
              erewrite get_set_eq; try lia.
              rewrite rmb1 in rmb; inversion rmb.
            }
            {
              unfold ModuleTableS.
              erewrite !get_set_neq; try lia.
              erewrite <- H4; eauto.
            }
          }
          {
            destruct (Nat.eq_dec hole_idx i).
            {
              subst.
              erewrite !get_set_eq; try lia.
              reflexivity.
            }
            {
              erewrite !get_set_neq; try lia.
              erewrite <- H6.
              erewrite H4; eauto.
            }
          }
        }
        {
          intros.
          assert (hole_idx <? alength x2 = true).
          rewrite H8.
          eapply Nat.ltb_lt.
          lia.
          rewrite H13.
          intros.
          assert (hole_idx =? x6 = false).
          eapply Nat.eqb_neq. 
          lia.
          rewrite H15.
          eauto.
        }
        (* TODO a tactic for length and defaults! *)
        rewrite H8, H, H1; simpl; try lia.
        rewrite H9, H2; simpl; try lia; reflexivity.
      }
    }
    split.
    {
      intros.
      pose proof H3 as rmbRule.
      unfold imodule in H3 |- *.
      unfold smodule in H3 |- *.
      cbn in H3.
      unfold apply_alog in *.
      destruct (r <? length local_rules) eqn:?;
      autorewrite with fwd_rewrites in *.
      2:{
        erewrite nth_overflow in H3.
        contradiction H3.
        cbn.
        rewrite map_length; eauto. 
      }
      subst.
      rpn relation_big bigr.
      pose proof bigr as bigr'.
      unfold relation_big in bigr'.

      cleanup.
      unfold refines in i_refines_s.
      repeat auto_specialize' i_refines_s.
      destruct i_refines_s.
      clear i_refines_s.
      clear H8.
      erewrite nth_map with (d' := Skip) in H3; eauto.
      cleanup.
      subst.
      inverseAll.
      subst.
      unshelve epose proof (H10 hole_idx _).
      { lia. }
      destruct (x4 hole_idx) eqn:rmb1.
      {
        destruct p.
        repeat auto_specialize' H7. 
        cleanup.
        (* epose proof (exist_list x0) as key_lemma. *)
        epose proof (exist_list  (aset _ hole_idx x) x2) as key_lemma.
        simpl in key_lemma.
        erewrite get_set_eq in key_lemma.
        specialize (key_lemma) with (5:= H8).
        specialize (key_lemma) with (5:= H14).
        specialize (key_lemma) with (5:= H15).
        assert ((forall instance : nat, instance <> hole_idx -> aget x2 instance = aget (aset x2 hole_idx x) instance)).
        {
          intros.
          erewrite get_set_neq; eauto.
        }
        rewrite !H12 in key_lemma.
        2:{ rewrite H12; lia.  }
        repeat auto_specialize' key_lemma.
        clear H16.
        cleanup.
        unfold relation_big in H17.
        eexists.
        split.
        2:{
          split.
          2:{
            eapply H18.
          }
          do 2 eexists.
          split; eauto.
        }
        eapply existSR_step with (r:=r).
        2:{ eauto. }
        unfold ModuleTableS.
        simpl.
        erewrite nth_map with (d' := Skip); eauto.
        do 5 eexists.
        split; eauto.
        split; eauto.
        split; eauto.
        eapply wpa_I_to_S.
        eauto.
        eauto.
        unfold apply_alog.
        split.
        {
          intros.
          specialize (H10 i).
          rewrite H1 in H19; rewrite H in H10.
          simpl in *.
          specialize (H10 H19).
          destruct (x4 i) eqn:rmb.
          {
            destruct p.
            destruct (Nat.eq_dec hole_idx i).
            {
              subst.
              erewrite get_set_eq; try lia.
              rewrite rmb1 in rmb; inversion rmb.
              subst.
              unfold ModuleTableS.
              erewrite get_set_eq; try lia.
              eauto.
            }
            {
              unfold ModuleTableS.
              erewrite !get_set_neq; try lia.
              erewrite <- H4; eauto.
            }
          }
          {
            destruct (Nat.eq_dec hole_idx i).
            {
              subst.
              rewrite rmb1 in rmb; inversion rmb.
            }
            {
              erewrite !get_set_neq; try lia.
              erewrite <- H4; eauto.
            }
          }
        }
        {
          split.
          simpl.
          intros.
          assert (hole_idx <? alength x2 = true).
          rewrite H12.
          eapply Nat.ltb_lt.
          lia.
          rewrite H20.
          intros.
          assert (hole_idx =? x8 = false).
          eapply Nat.eqb_neq. 
          lia.
          rewrite H21.
          eauto.
          simpl.
          rewrite H12, H13.
          split; eauto.
          rewrite H, H1.
          simpl; eauto.
        }
      }
      {
        epose proof (exist_list (aset x2 hole_idx (aget x0 hole_idx)) x2) as key_lemma.
        simpl in key_lemma.
        erewrite get_set_eq in key_lemma.
        assert (aget x1 hole_idx = aget x2 hole_idx).
        { eauto.  }
        rewrite H8 in H5.
        rewrite H8 in H6.

        specialize (key_lemma) with (6:= H5).
        specialize (key_lemma) with (6:= H6).
        assert (existSR ms (aget x0 hole_idx) (aget x0 hole_idx)) by econstructor.
        specialize (key_lemma) with (5:= H14).
        erewrite H12 in key_lemma.

        repeat auto_specialize' key_lemma.
        assert ((forall instance : nat, instance <> hole_idx -> aget x2 instance = aget (aset x2 hole_idx (aget x0 hole_idx)) instance)).
        {
          intros.
          erewrite get_set_neq; eauto.
        }
        repeat auto_specialize' key_lemma.
        2:{ rewrite H12; lia.  }
        cleanup.
        clear H15.
        eexists.
        split.
        2:{
          split.
          2:{
            eapply H18.
          }
          do 2 eexists.
          split; eauto.
        }
        eapply existSR_step with (r:=r).
        2:{ eauto. }
        unfold ModuleTableS.
        simpl.
        erewrite nth_map with (d' := Skip); eauto.
        do 5 eexists.
        split; eauto.
        split; eauto.
        split; eauto.
        eapply wpa_I_to_S.
        eauto.
        eauto.
        unfold apply_alog.
        split.
   
        intros.
        {
          specialize (H10 i).
          rewrite H1 in H8; rewrite H in H10.
          simpl in *.
          specialize (H10 H8).
          destruct (x4 i) eqn:rmb.
          {
            destruct p.
            destruct (Nat.eq_dec hole_idx i).
            {
              subst.
              erewrite get_set_eq; try lia.
              rewrite rmb1 in rmb; inversion rmb.
            }
            {
              unfold ModuleTableS.
              erewrite !get_set_neq; try lia.
              erewrite <- H4; eauto.
            }
          }
          {
            destruct (Nat.eq_dec hole_idx i).
            {
              subst.
              erewrite !get_set_eq; try lia.
              reflexivity.
            }
            {
              erewrite !get_set_neq; try lia.
              erewrite <- H4; eauto.
            }
          }
        }
        {
          simpl.
          split.
          intros.
          assert (hole_idx <? alength x2 = true).
          rewrite H12.
          eapply Nat.ltb_lt.
          lia.
          rewrite H15.
          intros.
          assert (hole_idx =? x6 = false).
          eapply Nat.eqb_neq. 
          lia.
          rewrite H19.
          eauto.
          try rewrite H12, H13.
          split; eauto; rewrite H, H1; simpl; eauto.
        }
      }
    }
    {
      subst.
      cleanup.
      intros.
      (* Two cases:
        - the step takes place in the hole: 
            1. It is a step of the hole itself, we use the simulation relation for rules to give us a existSR for the submodule.
            2. It is a substep of the hole, we use the simulation relation for subrules to give us a existSR for the submodule.
        - the step takes place in an other submodule: just replay the exact same substep in the spec *)
      destruct (PeanoNat.Nat.eq_dec sm hole_idx).
      {
        (* - the step takes place in the hole:  *)
        subst.
        unfold lift_to in H.
        cleanup.
        inverseAll.
        subst.
        pose proof H3 as remember_rl_relation.
        unfold imodule in H3.
        cbn in H3.
        erewrite nth_map in H3; try rewrite seq_length; eauto.
        rewrite seq_nth in H3;eauto.
        cbn in H3.
        remember ((rule_spec _)) in H3.
        assert (r < length l \/ r >= length l) as case by lia.
        destruct case; eauto.
        {
            (* 1. It is a step of the hole itself, we use the simulation relation for rules to give us a existSR for the submodule. *)
          rewrite app_nth1 in H3;eauto .
          subst l.
          unfold refines in i_refines_s.
          rpn relation_big rpr.
          pose proof rpr as H2.
          unfold relation_big in H2.
          cleanup.
          repeat auto_specialize.
          destruct i_refines_s.
          clear i_refines_s.
          cleanup.
          clear H8.
          unfold mi in H10.
          pose proof H3 as rememberspec.
          specialize H9 with (1:= rememberspec).
          cleanup. 
          pose proof exist_list as el; eauto.
          specialize (el x0 (aset x1 hole_idx x2)).
          erewrite get_set_eq in el; try lia.
          specialize (el) with (6:=H9).
          specialize (el) with (5:=H8).
          specialize (el) with (5:=H11).
          assert (forall instance : nat,
      instance <> hole_idx ->
      aget (aset x1 hole_idx x2) instance = aget x0 instance).
          {
            intros.
            erewrite <- H5; eauto.
            cleanup.
            symmetry.
            erewrite get_set_neq; eauto.
          }
          specialize (el) with (4:=H12).
          simpl in el.
          rewrite H4, H2, H1 in el.
          simpl in el.
          repeat auto_specialize' el.
          cleanup.
          eexists.
          split; eauto.
          split; eauto.
        }
        {
            (* 2. It is a substep of the hole, we use the simulation relation for subrules to give us a existSR for the submodule. *)
          erewrite app_nth2 in H3; eauto.
          subst l.
          eapply simplify_concat in H3.
          cleanup.
          unfold refines in i_refines_s.
          rpn relation_big rpr.
          pose proof rpr as H2.
          unfold relation_big in H2.
          cleanup.
          repeat auto_specialize.
          destruct i_refines_s.
          clear i_refines_s.
          cleanup.
          clear H8 H9.
          rpn lift_to ref_hyp.
          unfold mi in ref_hyp.
          pose proof H1 as rememberspec.
          specialize ref_hyp with (1:= rememberspec).
          cleanup. 
          pose proof exist_list as el; eauto.
         specialize (el x0 (aset x1 hole_idx x2)).
          erewrite get_set_eq in el; try lia.
          specialize (el) with (6:=H9).
          specialize (el) with (5:=H8).
          specialize (el) with (5:=H10).
          assert (forall instance : nat, instance <> hole_idx -> aget (aset x1 hole_idx x2) instance = aget x0 instance) .
          {
            intros.
            erewrite <- H5; eauto.
            cleanup.
            symmetry.
            erewrite get_set_neq; eauto.
          }
          specialize (el) with (4:=H11).
          clear H11.
          simpl in el.
          rewrite H2, H3, H4 in el.
          simpl in el.
          repeat auto_specialize' el.
          cleanup.
          eexists.
          split; eauto.
          split; eauto.
        }
      }
      {
        unfold lift_to in H.
        (* - the step takes place in another submodule: just replay the exact same substep in the spec *)
        assert (sm < length (subrules_spec imodule) \/ sm >= length(subrules_spec imodule)) as case by lia.
        cleanup.
        destruct case.
        2:{
          rewrite nth_overflow with (l:= subrules_spec imodule) in H3; eauto.
          cleanup.
          destruct r; 
          cbv in H3;
          contradiction H3.
        }
        assert (length (subrules_spec imodule) = length (subrules_spec smodule)).
        {
          unfold imodule,smodule.
          cbn.
          rewrite !map_length; eauto.
        }
        rename H1 into length_sm.  
        assert (length (subrules_spec imodule) = alength ModuleTableI).
        {
          unfold imodule.
          cbn.
          rewrite map_length.
          rewrite seq_length; eauto.
        }
        assert (nth sm (subrules_spec imodule) [] = nth sm (subrules_spec smodule) []) as samenth.
        {
          unfold imodule,smodule.
          simpl.
          erewrite nth_map.
          erewrite nth_map.
          unfold ModuleTableS.
          rewrite !nth_seq.
          rewrite !get_set_neq.
          all: eauto.
          all: try rewrite seq_length; lia.
        }
        subst.
        inverseAll.
        subst.
        pose proof H3 as jj.
        pose proof existSR_substep.
        specialize H with (instance_i := sm) (r:= r); eauto.
        remember (nth sm (subrules_spec smodule) []).
        pose proof (@nth_error_nth' _ (subrules_spec smodule) sm []) as fstnth.
        assert (sm < length (subrules_spec smodule)) .
        {
          unfold smodule, imodule in H4|-*.
          simpl in H4|-*.
          rewrite map_length, seq_length in H4|-*.
          eauto.
        }
        auto_specialize' fstnth.
        auto_specialize' H.
        pose proof (@nth_error_nth' _ l r unexisting_rule) as sndnth.
        assert (r < length l \/ r >= length l) as case by lia.
        destruct case.
        2:{ rewrite nth_overflow in jj;eauto.  contradiction jj.
        rewrite samenth. eauto.  }
        auto_specialize' sndth.
        rewrite samenth in *.
        subst l.
        auto_specialize' H.
        unfold lift_to in *.
        unfold relation_big in H2.
        cleanup.
        specialize (H {| T := state_t; state := x0 |} ).
        epose proof (H {| T:= state_t; state := aset x0 sm x2|} {| T:= state_t; state := aset x0 sm x2|}).
        assert   (exists small : state_t,
         {| T := state_t; state := x0 |} = {| T := state_t; state := small |} /\
         (exists change_submod_small : SModule,
            {| T := state_t; state := aset x0 sm x2 |} =
            {| T := state_t; state := aset small sm change_submod_small |} /\
            nth r (nth sm (subrules_spec smodule) []) unexisting_rule 
              (aget small sm) change_submod_small)) .
        { eexists.  split; eauto. 
          eexists.
          split; eauto.
          erewrite <- H10; eauto.  } 
        auto_specialize' H13.
        clear H14.
        specialize (H13 (existSR_done _ _)).
        eexists.
        split; eauto. 
        assert ( relation_big (aset x1 sm x2) (aset x0 sm x2)).
        {
          unfold relation_big; simpl.
        rewrite H2, H8, H9.
        simpl.
        split; eauto.
        split; eauto.
        split; eauto.
        erewrite !get_set_neq; eauto.
        split; eauto.
        intros.
        destruct (Nat.eq_dec instance sm).
        {
          subst.
          rewrite !get_set_eq; try lia; eauto.
          rewrite H8;simpl; eauto.
          simpl in H4. rewrite map_length, seq_length in H4.
          eauto.
        }
        {
          erewrite !get_set_neq; eauto.
        }
        }
        split.
        do 2 eexists.
        split; eauto.
        eapply indistinguishable_preserved; eauto.
        {
          simpl in H4. rewrite map_length, seq_length in H4.
          eauto.
        }
        rewrite H8, H2; simpl; eauto.
      }
    }
    Unshelve.
    exact 0.
    exact 0.
    exact 0.
    Qed.
    
    (* Qed.  *)
End RefinementTheorem. 

Section TransitivityRefinement.
  Context {i1 s1 s2 : spec_module_t}.
  Context {related1 related2 : SModule -> SModule -> Prop}.
 
  Theorem tran_indistinguishable :
    forall x_i1 x_s1 x_s2, 
    indistinguishable i1 s1 x_i1 x_s1 ->
    indistinguishable s1 s2 x_s1 x_s2 ->
    indistinguishable i1 s2 x_i1 x_s2.
    intros.
    unfold indistinguishable in *.
    cleanup.
    split; intros; repeat auto_specialize; eauto.
    cleanup.
    intros; repeat auto_specialize; eauto.
  Qed.

  Lemma tr_existSR : forall s x1 x2 x3, existSR s x1 x2 -> existSR s x2 x3 -> existSR s x1 x3.
  intros.
  generalize dependent x3.
  induction H.
  {
    intros; eauto.
  }
  {
    intros.
    eapply existSR_substep.
    eauto.
    eauto.
    eauto.
    eapply IHexistSR.
    eauto.
  }
  {
    intros.
    eapply existSR_step.
    eauto.
    eapply IHexistSR.
    eauto.
  }
  Qed.

  Lemma multisteps : forall x0,
      (* refines i1 s1 related1 -> *)
      refines s1 s2 related2 ->
      forall x0',
      related2 x0 x0' ->
      indistinguishable s1 s2 x0 x0' ->
      forall mid_s1,
      existSR s1 x0 mid_s1 ->
      exists mid_s2,
      existSR s2 x0' mid_s2  /\
      related2 mid_s1 mid_s2 /\ indistinguishable s1 s2 mid_s1 mid_s2.
      intros.
      generalize dependent x0'.
      induction H2; subst.
      {
        intros.
        econstructor.
        split.
        econstructor.
        split; eauto.
      }
      {
        intros.
        repeat auto_specialize.
        cleanup.
        repeat auto_specialize.
        pose proof H0 as subrules_spec.
        erewrite nth_error_nth' with (d:= []) in H0.
        2:{
          eapply nth_error_Some.
          erewrite H0; easy.
        }
        inversion H0.
        erewrite nth_error_nth' with (d:= unexisting_rule) in H1.
        2:{
          eapply nth_error_Some.
          erewrite H1; easy.
        }
        inversion H1; clear H0 H1.
        subst.
       
        unfold refines in H.
        repeat auto_specialize' H.
        cleanup.
        clear H0 H.
        specialize (H1 instance_i r ).
        repeat auto_specialize' H1.
        unfold lift_to in *.
        cleanup.
        specialize (IHexistSR x1 H6 H7).
        cleanup.
        subst.
        eexists.
        split.
        2:{
        split; eauto.
        }
        eapply tr_existSR.
        eauto.
        eauto.
      }
      {
        intros.
        unfold refines in *.
        repeat auto_specialize.
        cleanup.
        clear H5 H.
        repeat auto_specialize.
        cleanup.
        repeat auto_specialize.
        cleanup.

        eexists.
        split.
        2:{ split; eauto.  } 
        eapply tr_existSR.
        eauto.
        eauto.
      }
      Qed.

  Theorem trans_refinement : 
    refines i1 s1 related1 -> refines s1 s2 related2 ->
    refines i1 s2 (fun i s => exists int, related1 i int /\ indistinguishable i1 s1 i int /\
                             indistinguishable s1 s2 int s /\ related2 int s).
    intros.
    repeat split.
    {
      intros.
      cleanup.
      pose proof H0 as rf12.
      unfold refines in H0, H.
      repeat auto_specialize.
      cleanup.
      clear H9 H10 H7 H8.
      specialize H with (1:=H3).
      cleanup.
      specialize H0 with (1:= H).
      cleanup.
      repeat auto_specialize.
      pose proof multisteps as ms; eauto.
      specialize (ms) with (2:=H11).
      specialize (ms) with (2:=H12).
      specialize (ms) with (2:=H7).
      auto_specialize.
      cleanup.
      eexists.
      eexists.
      split; eauto.
      assert (existSR s2 x2 x4).
      {
        eapply tr_existSR.
        eauto.
        eauto.
      }
      split; eauto.
      split.
      eexists.
      split; eauto.
      eapply tran_indistinguishable; eauto.
    }
    {
      intros.
      pose proof multisteps.
      repeat auto_specialize.
      unfold refines in *.
      cleanup.
      repeat auto_specialize.
      cleanup.
      repeat auto_specialize.
      cleanup.
      repeat auto_specialize.
      cleanup.
      eexists.
      split; eauto.
      split;eauto.
      eapply tran_indistinguishable; eauto.
    }
    {
      intros.
      pose proof multisteps.
      repeat auto_specialize.
      unfold refines in *.
      cleanup.
      repeat auto_specialize.
      cleanup.
      repeat auto_specialize.
      cleanup.
      repeat auto_specialize.
      cleanup.
      eexists.
      split; eauto.
      split;eauto.
      eapply tran_indistinguishable; eauto.
    }
    Qed.

End TransitivityRefinement.


Arguments Pos.to_nat !x.
Definition hideId {T : Type} (x : T) := x.

(* Notation "'OpaqueAxiom'" := (@hideId _ _) (only printing).
Notation " '{' s '}' 'WITH_ARGS' args 'WITH_VARS' binders 'STEPS_TO' P  " :=
    (wp _ args _ binders _ s P)
    (at level 200, only printing).

Notation "'{' s '}' 'WITH_ARGS' args 'WITH_BINDERS' binders 'STEPS_TO' P":=
    (wpa _ args _ binders _ _ s P)
    (at level 200, only printing). *)



(* The following is a hack to display small arrays, at some point, figure out a way to do it for arbitrary size arrays. *)
Declare Custom Entry printer_arrays.
Notation "m1 ';' m2  ';' m3 ';' '...' " := 
    (fun x:nat => match x with 
      | 0%nat => m1
      | S m => match m with 
            | 0%nat => m2
            | S m =>
            match m with 
            | 0%nat => m3
            | S m => match m with 
            | 0%nat => _
            | S m => match m with 
                  | 0%nat => _ 
                  | S m => _
            end end end end end) (in custom printer_arrays at level 51,
             m1 constr at level 0,
             m2 constr at level 0,
             m3 constr at level 0,
               only printing).
Notation "m1 ';' m2  ';' m3 ';' '...' " := 
    (fun x:nat => match x with 
      | 0%nat => m1
      | S m => match m with 
            | 0%nat => m2
            | S m =>
            match m with 
            | 0%nat => m3
            | S m => match m with 
            | 0%nat => _
            | S m => match m with 
                  | 0%nat => _ 
                  | _ => _
            end end end end end) (in custom printer_arrays at level 51,
             m1 constr at level 0,
             m2 constr at level 0,
             m3 constr at level 0,
               only printing).
Notation "m1 ';' m2  ';' m3" := 
    (fun x:nat => match x with 
      | 0%nat => m1
      | S m => match m with 
            | 0%nat => m2
            | S m =>
            match m with 
            | 0%nat => m3
            | S m => match m with 
            | 0%nat => _
            | _ => _
            end end end end) (in custom printer_arrays at level 51,
             m1 constr at level 0,
             m2 constr at level 0,
             m3 constr at level 0,
               only printing).
Notation "m1 ';' m2 " := 
    (fun x:nat => match x with 
      | 0%nat => m1
      | S m => match m with 
            | 0%nat => m2
            | S m0 => match m0 with 
            | 0%nat => _
            | _ => _
      end
      end
      end) (in custom printer_arrays at level 50, m1 constr at level 0, m2 constr at level 0, only printing).
Notation "m1" := 
    (fun x:nat => match x with 
      | 0%nat => m1
      | S m => match m with 
            | 0%nat => _
            | _ => _
      end
      end) (in custom printer_arrays at level 49, m1 constr at level 0, only printing).

(* Notation "'<|' fn '|>'" := ({|  alength := _; default := _ ; values :=  fn |}) 
      (fn custom printer_arrays at level 52, only printing). *)
(* Declare Scope fjfjarrays_scope. *)
(* Notation "'<|' fn '|>'" := ({|  alength := _; default := _ ; values :=  fn%fjfjarrays|})  *)
      (* (only printing). *)
Open Scope N.

Notation "x '!=' y" := (N.b2n (x =? y)%N mod 2 = 0) (at level 10).
Notation "x '==' y" := (N.b2n (x =? y)%N mod 2 = 1) (at level 10).


Lemma lift_inequality : forall (n m: N), n <> m -> N.to_nat n <> N.to_nat m.
    intros.
    unfold not.
    intros.
    eapply (f_equal N.of_nat) in H0.
    rewrite !N2Nat.id in H0.
    eauto.
  Qed.

(* Coercion to help writing the code *)

(* Module InstanceNotations.
Notation "'{[' ']}'" := (nil: list spec_module_t) (format "{[ ]}"). 
Notation "'{[' x ']}'" := (cons (x:spec_module_t) nil).
Notation "'{[' x ; y ; .. ; z ']}'" := (cons (x:spec_module_t) (cons (y:spec_module_t) .. (cons (z:spec_module_t) nil) ..)).
End InstanceNotations. *)


Section RefinesRefl.
  Theorem indistinguishable_refl : forall m s, indistinguishable m m s s.
    intros;split; intros; eauto.
  Qed.
  Context (m : spec_module_t).
  Theorem refines_refl : refines m m (fun x y => x = y).
    intros.
    split.
    {
      intros.
      subst.
      do 2 eexists.
      split; eauto.
      split; eauto.
      econstructor.
      split; eauto.
      eapply indistinguishable_refl.
    }
    split.
    {
      intros.
      subst.
      eexists.
      split.
      eapply existSR_step; eauto.
      econstructor.
      split; eauto; eapply indistinguishable_refl.
    }
    {
      intros.
      eexists.
      split.
      eapply existSR_substep; eauto.
      erewrite nth_error_nth' .
      reflexivity.
      assert ( sm < length (subrules_spec m) \/ sm >= length (subrules_spec m))%nat by lia.
      destruct H2; eauto.
      {
        rewrite nth_overflow with (l:= subrules_spec m) in H1; eauto.
        destruct r; cbv in H1;
        cleanup; contradiction H4.
      }
      erewrite nth_error_nth' .
      reflexivity.
      assert ( r < length (nth sm (subrules_spec m) []) \/ r >= length (nth sm (subrules_spec m) []))%nat by lia.
      destruct H2; eauto.
      {
        rewrite nth_overflow in H1; eauto.
        destruct r; cbv in H1;
        cleanup; contradiction H4.
      }
      subst.
      eapply H1.
      econstructor.
      split; eauto ; eapply indistinguishable_refl.
  }
  Qed.
End RefinesRefl.


Notation "'dlet' '{' x y '}' ':=' exp 'in' t" :=
  (let x := split1 exp in
  let y := split2 exp in
  t) (at level 10, 
        x constr at level 0,
        y constr at level 0,
        t constr at level 200).

Notation "'dlet' '{' x y z '}' ':=' exp 'in' t" :=
  (let x := split1 exp in
  let y := split1 (split2 exp) in
  let z := split2 (split2 exp) in
  t) (at level 10, 
        x constr at level 0,
        y constr at level 0,
        z constr at level 0,
        t constr at level 200).

Notation "'dlet' '{' x y z u '}' ':=' exp 'in' t" :=
  (let x := split1 exp in
  let y := split1 (split2 exp) in
  let z := split1 (split2 (split2 exp)) in
  let u := split2 (split2 (split2 exp)) in
  t) (at level 10, 
        x constr at level 0,
        y constr at level 0,
        z constr at level 0,
        u constr at level 0,
        t constr at level 200).

Notation "'dlet' '{' x y z u v '}' ':=' exp 'in' t" :=
  (let x := split1 exp in
  let y := split1 (split2 exp) in
  let z := split1 (split2 (split2 exp)) in
  let u := split1 (split2 (split2 (split2 exp))) in
  let v := split2 (split2 (split2 (split2 exp))) in
  t) (at level 10, 
        x constr at level 0,
        y constr at level 0,
        z constr at level 0,
        u constr at level 0,
        v constr at level 0,
        t constr at level 200).

Close Scope N.

(* Notation "'<<' s '>>'" := (generic_embed s) (only parsing). *)

(* Notation "s1 '.=.' s2" := ({| T := _; state := s1 |} = {| T := _; state := s2 |}) (only printing, at level 10, right associativity).
Notation "a '=.' s2" := (a = {| T := _; state := s2 |}) (only printing, at level 3, right associativity).
Notation "s1 '.=' a" := ( {| T := _; state := s1 |} = a) (only printing, at level 3, right associativity). *)

Notation "'*(' a ')*'" := ( {| T := _; state := a |}) ( at level 2, right associativity).
Declare Custom Entry fjfj_mergeargs.

Notation "a b" :=  (merge a b) (in custom fjfj_mergeargs at level 100,
                                 a custom fjfj_mergeargs,
                                 b custom fjfj_mergeargs,
                                 right associativity).
Notation "a" := (a)
     (in custom fjfj_mergeargs at level 0,
      a constr at level 0).

Notation "'{#' a '}' " :=
  (a) (a custom fjfj_mergeargs at level 100).

(* Useful tactics: *)
Inductive FjfjKind :=
 | value_method_simulates (s : String.string)
 | action_method_simulates (s : String.string).
Inductive FjfjCase : FjfjKind -> Prop :=
  | fjfj_case : forall a , FjfjCase a.

Ltac change_fjfj_state a :=
  match goal with 
  | [H : FjfjCase _ |- _ ]=> clear H;
  let s := fresh "CurrentProof" in
  assert (FjfjCase a) as s by econstructor
  | [ |- _ ]=>
  let s := fresh "CurrentProof" in
  assert (FjfjCase a) as s by econstructor
  end.

(* Ltac fast_subst := 
    (* subst. *)
    try match goal with 
    | [ H: ?a = ?b |- _] => 
      is_var a; 
      subst a
    | [ H: ?a = ?b |- _] => 
      is_var b; 
      subst b
    end. *)
Ltac fast_subst :=
    try
    match goal with
    | H:?a = ?b |- _ => is_var a; subst a
    | H:?a = ?b |- _ => is_var b; subst b
    | H:?a ?x = ?b |- _ => is_var a; is_var x; rewrite H in *
    end.
(* 
(* Initial version, remove to use projections *)
Ltac destruct_ex n H := 
    lazymatch type of H with 
    | ?A /\ ?B => 
    let a := fresh "A" in
    let b := fresh "B" in
    let ha := fresh "HA" in
    let hb := fresh "HB" in
    set A as a in H;
    set B as b in H;
    destruct H as [ha hb]; subst a b; simpl in ha, hb
    | ?A <-> ?B => 
    let a := fresh "A" in
    let b := fresh "B" in
    let ha := fresh "HA" in
    let hb := fresh "HB" in
    set A as a in H;
    set B as b in H;
    destruct H as [ha hb]; subst a b; simpl in ha, hb
    | ex ?P => 
    let p := fresh "P" in
    set P as p in H;
    destruct H as [n H]; subst p; simpl in H
  end. *)
Ltac destruct_ex n H := 
    lazymatch type of H with 
    | ?A /\ ?B => 
    let ha := fresh "HA" in
    let hb := fresh "HB" in
    pose proof (proj1 H) as ha;
    pose proof (proj2 H) as hb;
    clear H;
    simpl in ha, hb
    (* let a := fresh "A" in
    let b := fresh "B" in
    let ha := fresh "HA" in
    let hb := fresh "HB" in
    set A as a in H;
    set B as b in H;
    destruct H as [ha hb]; subst a b;  
    simpl in ha, hb
    *)
    | ?A <-> ?B => 
    let ha := fresh "HA" in
    let hb := fresh "HB" in
    pose proof (proj1 H) as ha;
    pose proof (proj2 H) as hb;
    clear H;
    simpl in ha, hb
    (* let a := fresh "A" in
    let b := fresh "B" in
    let ha := fresh "HA" in
    let hb := fresh "HB" in
    set A as a in H;
    set B as b in H;
    destruct H as [ha hb]; subst a b; simpl in ha, hb *)
    | ex ?P => 
      let p := fresh "P" in
      set (p := P) in H; destruct H as [n H]; subst p; simpl in H
  end.
Ltac user_cleanup := intros;
  repeat match goal with
  | H: _ /\ _ |- _ => let n := fresh "dummy" in destruct_ex n H
  | H: _ <-> _ |- _ => let n := fresh "dummy" in destruct_ex n H
  | H: exists i, _  |- _ => let n := fresh i in destruct_ex n H
  | H: True  |- _ => clear H
  | H : ?a = ?b, H' : ?a = ?b |- _ => clear H'
  | H : N.of_nat ?a = N.of_nat ?b |- _ =>
    apply Nat2N.inj in H
  end.
Section ErrorMessages.
  Import String.
  Open Scope string.
  Definition fishy := ("ERROR: Analyzing a method that does not seem to have a name. Fishy.").
  Definition not_focused := "Not Focused Yet".
  Close Scope string.
End ErrorMessages.
Class instances := { code : array spec_module_t; idx : list String.string }.
Class module (sm : spec_module_t):= {
    value_methods : list String.string;
    action_methods : list String.string;
    rule_names: list String.string;
    mod_spec := sm
  }.

Definition spec_of {sm : spec_module_t} (s : module sm) := sm.
Inductive Current_Impl_Spec_Modules : forall (sm1 sm2: spec_module_t), module sm1 -> module sm2 -> Prop :=
  | _fjfj_module : forall {a b} m1 m2 , Current_Impl_Spec_Modules a b m1 m2.
Notation "'IMPL:' m1 'SPEC' m2" := (Current_Impl_Spec_Modules _ _ m1 m2) (at level 200, only printing). 

Ltac identify_modules :=
  try match goal with 
  | |- (indistinguishable (spec_of ?a) (spec_of ?b) _ _) => 
  let s := fresh "ProvingStateSimulation" in
  assert (Current_Impl_Spec_Modules _ _ a b) as s by econstructor
  | |- (refines (spec_of ?a) (spec_of ?b) ?phi ) => 
  let s := fresh "ProvingRefinement" in
  assert (Current_Impl_Spec_Modules _ _ a b) as s by econstructor
  end.
   
Ltac destruct_met' method_id step_implem current_n :=
  (* idtac "Enter destruct" method_id; *)
  simpl in step_implem; try contradiction  step_implem; 
  destruct method_id;
  simpl in step_implem; 
  try (idtac;[
    lazymatch goal with 
    | [ H : (Current_Impl_Spec_Modules _ _ ?a _), H' : FjfjCase (value_method_simulates _) |- _] =>
      let l := eval cbv in 
        (nth current_n (value_methods (sm:= a)) fishy) 
      in
      change_fjfj_state (value_method_simulates l )
     | [ H : (Current_Impl_Spec_Modules _ _ ?a _) , H' : FjfjCase (action_method_simulates _)|- _] =>
      let l := eval cbv in 
        (nth current_n (action_methods (sm:= a)) fishy) 
      in
      change_fjfj_state (action_method_simulates l)
    | _ => 
    idtac
     (* "ERROR: unexpected missing marker to identify which module is implementation and which one is spec"  *)
    end
  | ..]);
  try contradiction step_implem;
   try (idtac;[..|try destruct_met' method_id step_implem (S current_n)]).

(* 
old destruct_met'
Ltac destruct_met' method_id step_implem current_n :=
  (* idtac "Enter destruct" method_id; *)
  simpl in step_implem; try contradiction  step_implem; 
  destruct method_id;
  simpl in step_implem; 
  try (idtac;[match type of step_implem with 
  | exists st (nB : Binders) (nV: Vlog),_ => 
    match goal with 
    | [ H : (Current_Impl_Spec_Modules ?a _) |- _] =>
      let l := eval cbv in 
        (nth current_n (value_methods (sm:= a)) fishy) 
      in
      change_fjfj_state (value_method_simulates l )
    | _ => 
    idtac
     (* "ERROR: unexpected missing marker to identify which module is implementation and which one is spec"  *)
    end
  | exists (st : state_t) (nxt_st : array SModule) (nB : Binders) 
     (nA : Alog) (nV : Vlog), _ => 
      match goal with 
    | [ H : (Current_Impl_Spec_Modules ?a _) |- _] =>
      let l := eval cbv in 
        (nth current_n (action_methods (sm:= a)) fishy) 
      in
      change_fjfj_state (action_method_simulates l)
    | _ => 
    idtac
     (* "ERROR: unexpected missing marker to identify which module is implementation and which one is spec"  *)
    end
  | _ => idtac
  end | ..]);
  try contradiction step_implem;
   try (idtac;[..|try destruct_met' method_id step_implem (S current_n)]). *)

Ltac destruct_met method_id step_implem :=
  destruct_met' method_id step_implem 0%nat.

(* Ltac destruct_met method_id step_implem :=
    simpl in step_implem; try contradiction step_implem; destruct method_id; simpl in step_implem; try contradiction step_implem; try destruct_met method_id step_implem. *)

Ltac amethods_cases := intros method_id arg_method mid_i init2mid_i; 
  (* let c := fresh "current_case" in 
  pose proof init2mid_i as c;
  let y0 := fresh "tmp_met" in 
  set (aget _ _) as y0 in c; cbv [aget Nat.ltb Nat.leb alength action_spec] in y0; simpl in y0; subst y0; *)
  destruct_met method_id init2mid_i; 
  let y := fresh "tmp_met" in 
  set (aget _ _) as y; simpl in y; subst y.

Ltac rules_cases:= intros r mid_i init2mid_i; 
  (* let c := fresh "current_case" in  *)
  (* pose proof init2mid_i as c; *)
  (* let y0 := fresh "tmp_met" in 
  set (nth _ _) as y0 in c; cbv [aget Nat.ltb Nat.leb alength rule_spec] in y0; simpl in y0; subst y0; *)
  destruct_met r init2mid_i 
  (*let y := fresh "tmp_met" in 
  set (nth _ _) as y; cbn in y; subst y *)
  .
Ltac contradiction_submodule init2mid_i :=
    let x := fresh "x" in
    let y := fresh "y"  in
    let eq_x := fresh "eqx" in
    let eq_y := fresh "eqy" in
    let trans := fresh "step_eq" in 
    solve [destruct init2mid_i as [x [eq_x [y [eq_y trans]]]]; contradiction trans].

Ltac destruct_sr r step_implem := 
    simpl in step_implem; try contradiction_submodule step_implem; destruct r; simpl in step_implem; try contradiction_submodule step_implem .
   (* try destruct_sr r step_implem. *)

Ltac destruct_sm sm r step_implem :=
    simpl in step_implem; try contradiction_submodule step_implem; destruct sm;[
    repeat (destruct_sr r step_implem)| ]; let t := type of step_implem in 
    match t with 
    | context[match _ with _ => _ end] => destruct_sm sm r step_implem 
    | _ => repeat(destruct_sr r step_implem)
    end
    .

Ltac subrules_cases := intros sm r mid_i init2mid_i; 
  repeat (destruct_sm sm r init2mid_i).

Ltac prove_refinement :=
  unfold refines;
  intros init_i init_s related_i_s indistinguishable_i_s;
  split;[ amethods_cases
  |split ;[rules_cases| subrules_cases]].
     
Ltac value_method_indis := intros arg vmethod_id ret_value impl_vm_call;
   (* let c := fresh "current_case" in 
   pose proof impl_vm_call as c;
   let y0 := fresh "tmp_met" in 
      set (aget _ _) as y0 in c; cbv [aget Nat.ltb Nat.leb alength value_spec] in y0; simpl in y0; subst y0; *)
  destruct_met vmethod_id impl_vm_call 
      (* let y := fresh "tmp_met" in 
      set (aget _ _) as y; cbn in y; subst y *)
      .

Ltac action_method_guard_ready := intros arg amethod_id new_st_value impl_am_call;
   (* let c := fresh "current_case" in 
   pose proof impl_am_call as c;
   let y0 := fresh "tmp_met" in 
      set (aget _ _) as y0 in c; cbv [aget Nat.ltb Nat.leb alength action_spec] in y0; simpl in y0; subst y0; *)
  destruct_met amethod_id impl_am_call
  (* ;  *)
      (* let y := fresh "tmp_met" in 
      set (aget _ _) as y; cbn in y; subst y *)
      .

(* Ltac prove_indistinguishable := split;[value_method_indis| action_method_guard_ready]. *)



Ltac prove_indistinguishable :=
  split; [ change_fjfj_state (value_method_simulates not_focused); value_method_indis | change_fjfj_state (action_method_simulates not_focused); action_method_guard_ready ].


Ltac clean_propagate := repeat (user_cleanup; try inverseAll; subst; repeat auto_specialize).
Ltac crush := repeat split; clean_propagate; repeat eexists; intuition congruence.

(* Finally some arithmetic stuff: *)
Open Scope N.
Lemma rm_mod_b2n : forall x, N.b2n x mod 2 = N.b2n x.
  intros x; destruct x; reflexivity.
Qed.
Lemma rm_b2n_true : forall x, N.b2n x = 1 <-> x = true.
  intro x; destruct x; easy.
Qed.
Lemma rm_b2n_false : (forall x, N.b2n x = 0 <-> x = false) .
  intro x; destruct x; easy.
Qed.
Ltac rm_b2n_chenil :=
  repeat first [ rewrite rm_mod_b2n| rewrite rm_b2n_true| rewrite rm_b2n_false].
Ltac rm_b2n_chenilIn H :=
  repeat first [ rewrite rm_mod_b2n in H| rewrite rm_b2n_true in H| rewrite rm_b2n_false in H].
Ltac goto_n H :=
       rm_b2n_chenilIn H;
       repeat erewrite N.eqb_eq in H;
       repeat erewrite N.eqb_neq in H.
Ltac clean_arith := 
  match goal with 
  | [ H : context[N.eqb _ _] |- _] => progress (goto_n H)
  | H:context [ _ <? _ ] |- _ => progress goto_n H
  | H:context [ N.leb _ _] |- _ => progress goto_n H
  | [ |- context[N.eqb _ _]] => rm_b2n_chenil
  end.
Close Scope N.

Ltac light_clean_propagate := repeat (user_cleanup; try inverseAll; fast_subst ).
Ltac straight_line_step := 
  match goal with 
        | [H : step _ _ _ _ _ (ValMethod _ _ _) _ _ _ |-_] => 
        eapply inv_DCall in H; simpl in H; light_clean_propagate
        | [H : step _ _ _ _ _ (BOp _ _ _) _ _ _ |-_] => 
        eapply inv_DBinop' in H; simpl in H; light_clean_propagate
        | [H : step _ _ _ _ _ (UOp _ _) _ _ _ |-_] => 
        eapply inv_DUnop' in H; simpl in H; light_clean_propagate
        | [H : step _ _ _ _ _ (SetVar _ _) _ _ _ |-_] => 
        eapply inv_DSetVar in H; simpl in H; light_clean_propagate
        | [H : step _ _ _ _ _ (ZOp (Cst _)) _ _ _ |-_] => 
        eapply inv_DCst in H; simpl in H; light_clean_propagate
        | [H : step _ _ _ _ _ (Arg) _ _ _ |-_] => 
        eapply inv_DArg in H; simpl in H; light_clean_propagate
        | [H : step _ _ _ _ _ (Abort) _ _ _ |-_] => 
        eapply inv_DAbort in H; simpl in H; light_clean_propagate
        | [H : step _ _ _ _ _ (Var _) _ _ _ |-_] => 
        eapply inv_DVar in H; simpl in H; light_clean_propagate
        | [H : step _ _ _ _ _ (Ternary _ _ (Abort)) _ _ _ |-_] => 
        eapply inv_DWhenExpr in H; simpl in H; light_clean_propagate
        | [H : step _ _ _ _ _ (Ternary _ _ _) _ _ _ |-_] => 
        eapply inv_DTernary in H; simpl in H; light_clean_propagate
        end.

Ltac straight_line_wpa :=
  match goal with 
  | [ H :  wpa _ _ _ _ _ _ (Expr _) _ _ _  |- _] =>
        eapply inv_DExpr' in H; simpl in H; light_clean_propagate
  | [ H :  wpa _ _ _ _ _ _ (Seq _ _) _ _ _  |- _] =>
        eapply inv_DSeq' in H; simpl in H; light_clean_propagate
  | [ H :  wpa _ _ _ _ _ _ (Skip ) _ _ _  |- _] =>
        eapply inv_DSkip in H; simpl in H; light_clean_propagate
  | [ H :  wpa _ _ _ _ _ _ (ActionMethod _ _ _) _ _ _  |- _] =>
        eapply inv_DACall in H; simpl in H; light_clean_propagate
  | [ H :  wpa _ _ _ _ _ _ (If _ _ (Expr Abort)) _ _ _  |- _] =>
        eapply inv_DWhen in H; simpl in H; light_clean_propagate
  | [ H :  wpa _ _ _ _ _ _ (If _ _ _) _ _ _  |- _] =>
        eapply inv_DIf in H; simpl in H; light_clean_propagate
  end.

Ltac straight_line := repeat (first [straight_line_step | straight_line_wpa]; simpl in *); simpl in *.

Tactic Notation "unique" "pose" "proof" constr(defn) :=
  let T := type of defn in
  match goal with
  | [ H : T |- _ ] => fail 1
  | _ => pose proof defn
  end.

Definition impl (A : Prop) (B : Prop) := A -> B.

Definition BlackHole (x : Prop) := True.
Definition BlackHoleT {T} (x : T) : Prop := True.

Lemma eq_True_prove :forall (P: Prop), P = True ->P.
Proof.
  intros.
  rewrite H. eauto.
Qed.
Require Import Coq.Logic.PropExtensionality.



Ltac propintu := intros; apply propositional_extensionality; intuition idtac.
Module PropLemmas.
  Lemma eq_True: forall (P: Prop), P -> P = True. Proof. propintu. Qed.
  Lemma and_True_l: forall (P: Prop), (True /\ P) = P. Proof. propintu. Qed.
  Lemma and_True_r: forall (P: Prop), (P /\ True) = P. Proof. propintu. Qed.

  Lemma and_inv : (forall (A: Prop), (A /\ A) = A). propintu. Qed.
  Lemma reify_fundamental : forall t (x y:t), x = y ->  True = (x = y).  propintu. Qed. 

  Lemma anti_reify_eq : forall t (x y:t), (x = y) = True -> x = y.  intros.  rewrite H. trivial.  Qed. 
  Lemma smodule_inj_eq_sym : (forall (T : Type) (a b : T),   ( *( a )* = *( b )* ) = (a = b) ). propintu.  apply smodule_inj; eauto. rewrite H; eauto. Qed.
  Lemma some_inj_eq : (forall (T : Type) (a b : T), ( Some a = Some b ) = (a = b)). propintu. eapply some_inj; eauto. rewrite H; eauto. Qed.

  Lemma forall_ext_prop : forall (A : Type) (B C : A -> Prop),
       (forall x : A, B x = C x) -> (forall x : A, B x) = (forall x : A, C x).
       {
        intros.
        eapply propositional_extensionality.
        split.
        intros.
        erewrite <- H.
        eapply H0.
        intros.
        erewrite H.
        eapply H0.
       }
       Qed.
Lemma forall_ext_prop2 : forall (A1 A2 : Type) (B C : A1 -> A2 -> Prop),
       (forall (x : A1) (y : A2)  , B x y = C x y) -> (forall (x : A1) (y : A2), B x y) = (forall (x : A1) (y : A2), C x y).
       {
        intros.
        eapply propositional_extensionality.
        split.
        intros.
        erewrite <- H.
        eapply H0.
        intros.
        erewrite H.
        eapply H0.
       }
       Qed.

  Lemma BlackHoleT_True : forall (T : Type) x , @BlackHoleT T x = True.
  eauto.
  Qed.

  Lemma and_True_BlockHole : forall (P: Prop) (Q:Prop), P = True -> Q = True -> P /\ Q. Proof. intros. rewrite H, H0. eauto. Qed.
  Lemma and_l: forall (P: Prop) (Q:Prop), P /\ Q -> (P /\ Q) = P. Proof. intros.  propintu. Qed.
  Lemma and_r: forall (P: Prop) (Q:Prop), P /\ Q ->  (P /\ Q)  = Q. Proof. propintu.  Qed.

  Ltac pose_prop_lemmas :=
    pose proof PropLemmas.and_True_l as and_True_l;
    pose proof PropLemmas.and_True_r as and_True_r;
    (* pose proof PropLemmas.and_l as and_l;
    pose proof PropLemmas.and_r as and_r;
    pose proof PropLemmas.and_inv as and_inv; *)
    pose proof PropLemmas.and_True_BlockHole as and_True_BlockHole;
    pose proof PropLemmas.reify_fundamental as reify_fundamental
    (* ; *)
    (* pose proof PropLemmas.anti_reify_eq as antireify_eq *)
    .

  Ltac pose_smodule_lemmas := 
              pose proof @smodule_inj;
              pose proof @smodule_inj_eq_sym;
              pose proof @some_inj_eq
              . 

  Ltac pose_lemmas_nobh := pose_prop_lemmas; pose_smodule_lemmas.
  Ltac pose_lemmas:= pose_prop_lemmas; pose_smodule_lemmas ;
    pose proof PropLemmas.BlackHoleT_True as blackholet_trueT
    .
End PropLemmas.

Lemma eq_refl_True : forall {t} (x:t), (x = x) = True.
intros.
  eapply PropLemmas.eq_True.
reflexivity.
Qed.

Ltac repeat_tac t i :=
  match i with 
  | O => idtac 
  | S ?n => t n; repeat_tac t n
  end.


Ltac obs H i := let tmp := fresh "array_ext" in unshelve epose proof (H i _) as tmp; try simpl in tmp; try lia.
 Ltac simpl_applylogH H := 
        unfold apply_alog in H; simpl in H; user_cleanup;
         match goal with
         | [H':forall i : nat, (i < alength ?l)%nat -> _, H : alength ?l = ?n
           |- _] => let t' := obs H' in
                   repeat_tac t' n; clear H'
         | H':forall i : nat, (i < ?n)%nat -> _
           |- _ => let t' := obs H' in
                   repeat_tac t' n; clear H'
         end; light_clean_propagate.

Ltac simpl_applylog :=
  match goal with
  | [H:apply_alog _ _ _ _  
	|- _] =>
  simpl_applylogH H
  end.
(* Ltac simpl_applylog :=
  match goal with 
  | [ H: apply_alog _ _ _ _ |- _] =>
    unfold apply_alog in H; simpl in H; user_cleanup;
    match goal with
    | H':forall i : nat, (i < ?n)%nat -> _ |- _ => 
      let t' := obs H' in
      repeat_tac t' n; clear H'
    end;
    light_clean_propagate 
  end. *)

Ltac transform_exist_forall e l g := match e with 
| exists oldt, @?body oldt => 
    let t:= fresh oldt in
    constr:(forall t, 
        ltac:( let bdy := eval cbv beta in (body t) in 
               let sub_lift := transform_exist_forall bdy ( *( t )* :: l ) g in 
               exact sub_lift )
        )
| ?leaf => 
constr:(impl leaf (and g (BlackHoleT l)))
end.

Ltac transform_exist_forall_simpl e l g := 
  lazymatch e with 
| exists oldt, @?body oldt => 
    let t:= fresh oldt in
              (* let __ := match O with | _ => idtac "Call transformexist" e  end in *)
    open_constr:(forall t, 
        ltac:( let bdy := eval cbv beta in (body t) in 
               (* let __ := match O with | _ => idtac "Call recursive" bdy  end in *)
               let sub_lift := transform_exist_forall_simpl bdy ( *( t )* :: l ) g in 
               (* let __ := match O with | _ => idtac "End Call recursive returned" sub_lift  end in *)
               exact sub_lift)
        )
| ?leaf => 
              (* let __ := match O with | _ => idtac "Leaf transformexist" leaf  end in *)
open_constr:(impl leaf (and g (BlackHoleT l)) = ?[simp_th])
end.

Ltac existential_egg :=
   match goal with 
    | [|- ?g ] => match g with 
    | exists t, @?body t => 
      let gn := fresh "ToProve" in 
      let Hgn := fresh "Eqgoal" in 
      let exi := fresh "ExGoal" in 
      let exis := fresh "ExGoalSimpl" in 
      remember g as gn eqn:Hgn;
      let lifted  := transform_exist_forall g ([] : list SModule) gn in
      assert lifted as exi; 
        [intros; rewrite Hgn ;eexists;eauto; unfold BlackHoleT; trivial|];
      let lifteds  := transform_exist_forall_simpl g ([] : list SModule) gn in
      assert lifteds as exis;
      [ clear exi;
         intros;
         let ev := fresh "tmp" in 
         match goal with 
          | [|- ?b = ?a] => remember a as ev; 
          (* idtac  b a; *)
                   PropLemmas.pose_lemmas_nobh;
                    (* do 4 (try (time "Egg" (egg_simpl_goal 5); try reflexivity;  *)
                    do 4 (try ((egg_simpl_goal 5); try reflexivity; 
                    try lazymatch goal with 
                     | [H :?a |- _] => solve [ instantiate (simp_th:= False); inversion H ]
                    end))
         end; simpl; subst ev; try reflexivity
          | 
         ];
    try (eapply PropLemmas.forall_ext_prop2 in exis;
    simpl in exis;
    rewrite exis in exi;
    clear exis; unfold impl in exi);
    try (eapply PropLemmas.forall_ext_prop in exis;
    simpl in exis;
    rewrite exis in exi;
    clear exis; unfold impl in exi);
    (* eapply eq_True_prove; *)
    clear Hgn
    end
    end.

Ltac egg_repeat := 
  (* repeat (time "Egg" (egg_simpl_goal 5) ;  *)
  repeat ((egg_simpl_goal 5) ; 
          try reflexivity;
          try lazymatch goal with 
                | [H :?a |- _] => solve [ inversion H ] end).

Tactic Notation "egg_repeat_n" int(k) := 
  (* repeat (time "Egg" (egg_simpl_goal k) ;  *)
  repeat ((egg_simpl_goal k) ; 
          try reflexivity;
          try lazymatch goal with 
                | [H :?a |- _] => solve [ inversion H ] end).
Tactic Notation "egg_simpl" int(k) constr(x):= 
(* x needs to be a const, a bit sad *)
  (* time "Egg Elim" (egg_elim k x). *)
  (egg_elim k x).

Tactic Notation "egg_eexists" int(k) := 
  (* time "Egg Search Evar" (egg_search_evars k). *)
  (egg_search_evars k).

(* TODO: Should get deprecated, Coquetier should work without that now *)
Ltac add_eq_refl_True :=
  try match goal with 
  | [ H' : context[?H] |- _] => 
    let t := type of H in
    lazymatch t with 
    | Prop => fail 
    | forall x, _ => fail
    | _ => 
      let tt := type of t in
      lazymatch tt with 
      | Set => 
      unique pose proof (eq_refl_True H)
      | Type => 
      unique pose proof (eq_refl_True H )
      end
    end
  end.




Notation "'*[|' x  '|]*'" := 
  *(list_to_array (generic_embed 0)
   [ (generic_embed x)] )*.
Notation "'*[|' x ; y ; .. ; z '|]*'" := 
  *(list_to_array (generic_embed 0)
    (cons (generic_embed x) (cons (generic_embed y) .. (cons (generic_embed z) nil) ..)) )*.
Notation "'[|' x  '|]'" := 
  (list_to_array (generic_embed 0)
    [(generic_embed x)] ).
Notation "'[|' x ; y ; .. ; z '|]'" := 
  (list_to_array (generic_embed 0)
    (cons (generic_embed x) (cons (generic_embed y) .. (cons (generic_embed z) nil) ..)) ).

Require Import String.


Fixpoint index_of (e: string) (l : list string) acc:= 
     match l with 
     | cons t q => if eqb e t then Some acc else index_of e q (S acc)
     | nil => None 
     end.

Declare Custom Entry instances.
Require Import IdentParsing.


(* Definition id_module : forall {sm1 : spec_module_t} Id sm1, sm1 := sm. *)
(* Add a coercion to not have to add "spec_of" everywhere. *)
(* Identity Coercion Anat_of_A : Anat >-> spec_module_t. *)
Coercion spec_of :  module >-> spec_module_t.
Notation "tx x" := (spec_of tx, (ident_to_string! x)) (in custom instances at level 0, tx constr at level 0, x constr at level 0, only parsing).

Notation "'#|' txx ; tyy ; .. ; tzz '|#'" := 
  (let l := cons txx 
              (cons tyy .. (cons tzz nil) ..) in
  let spec := map fst l  in
  let names := map snd l in
{| code := list_to_array unexisting_spec_module spec;
   idx := names 
|}) (at level 200, txx custom instances, tyy custom instances, tzz custom instances).

Notation "'#|' txx  '|#'" := 
  (let l := cons txx  nil in
  let spec := map fst l in
  let names := map snd l in
{| code := list_to_array unexisting_spec_module spec;
   idx := names 
|}) (at level 200, txx custom instances).

Ltac list_ident_string l :=
  match l with 
  | nil => constr:(@nil string)
  | ?t :: ?q => 
              let nt :=  IdentToStringImpl.varconstr_to_string t in 
              (* let __ := match O with | _ => idtac "converting " t  end in *)
              let nq := list_ident_string q in 
              constr:(nt::nq) 
  end.
  

Arguments setb b !x y !idx /.
Arguments setalog nA !inst !met varg !i /.
Arguments setvlog nV !inst !met varg !i !m /.
Ltac refinement_t hole refinement:=
   eapply @trans_refinement;
   [ eapply refinenement_theorem with (hole_idx := hole) 
   | ];
   [ | | | eapply refinement| ]; simpl; try lia.

(* Declare a global set of uninterpreted functions to avoid problems *)

Axiom (fns : Uninterpreted_Functions).
Global Instance nouninterp : Uninterpreted_Functions := fns.
Notation "st '-(' s ')->'  P  " :=
    (step st _ _  _ _ s _ _ P)
    (at level 200, only printing).

Notation "st '-{' s '}->' P":=
    (wpa st 0%N _ _ _ _ s _  P _ )
    (at level 200, only printing).

Notation "st '-{' s '(' arg ')' '}->' P":=
    (wpa st arg _ _ _ _ s _  P _ )
    (at level 200, only printing).
Theorem wpa_to_cps : (forall w st a b c d e f g h i, (@wpa w st a b c d e f g h i ) <-> 
      @interp_wpa_cps w st a b c d e f (fun g' h' i' => h = h' /\ i = i')).
      Admitted.