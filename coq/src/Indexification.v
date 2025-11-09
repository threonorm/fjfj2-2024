Require Import LangFjfj2.
Require Import Arith.
Require List.
Import List.ListNotations.
Require Import Strings.String.

Section Indexification.
  Definition mapping_t := (nat * (String.string -> nat))%type.
  (* 0 is special, it means not mapped yet *)
  Fixpoint indexify_expr'  (t : @expr String.string) (mapping : mapping_t) :
  (* The first components holds the first unused integer, the second one maps
  string to integer representation or max_int if the string is not
  represented *)
  (mapping_t * (@expr varname ))%type :=
  match t with
  | Var v =>  (mapping, Var {| idxvar := (snd mapping) v; stringvar := v|})
  | Arg => (mapping, Arg)
  | ZOp prim =>
    (mapping, ZOp prim )
  | UOp prim arg =>
    let '(mapping, arg) := indexify_expr' arg mapping in
    (mapping, UOp prim arg)
  | BOp prim arg1 arg2 =>
    let '(mapping, arg1) := indexify_expr' arg1 mapping in
    let '(mapping, arg2) := indexify_expr' arg2 mapping in
    (mapping, BOp prim arg1 arg2)
  | SetVar v e =>
    let '(mapping, e) := indexify_expr' e mapping in
    let idx := (snd mapping) v in
    let newmapping := ( (fst mapping) + 1, fun e =>
      if String.eqb e v then (fst mapping) else (snd mapping) e) in
    if PeanoNat.Nat.eqb idx 0 then
    (newmapping,
     SetVar {| idxvar := (snd newmapping) v ; stringvar := v |} e)
    else
    (mapping,
     SetVar {| idxvar := (snd mapping) v ; stringvar := v |} e)
  | Ternary c t f =>
    let '(mapping, c) := indexify_expr' c mapping in
    let '(mapping, t) := indexify_expr' t mapping in
    let '(mapping, f) := indexify_expr' f mapping in
    (mapping, Ternary c t f)
  | Abort =>
    (mapping, Abort)
  | ValMethod instance met arg =>
    let '(mapping, arg) := indexify_expr' arg mapping in
    (mapping, ValMethod instance met arg)
  end.
  Arguments indexify_expr' t mapping /.

  Fixpoint indexify_action' (t : @action String.string ) (mapping : mapping_t ):=
  match t with
  | If c t f =>
    let '(mapping, c) := indexify_expr' c mapping in
    let '(mapping, t) := indexify_action' t mapping in
    let '(mapping, f) := indexify_action' f mapping in
    (mapping, If c t f)
  | Skip => (mapping, Skip)
  | Expr e =>
    let '(mapping, e) := indexify_expr' e mapping in
    (mapping, Expr e)
  | Seq a1 a2 =>
    let '(mapping, a1) := indexify_action' a1 mapping in
    let '(mapping, a2) := indexify_action' a2 mapping in
    (mapping, Seq a1 a2)
  | ActionMethod  instance met arg =>
    let '(mapping, arg) := indexify_expr' arg mapping in
    (mapping, ActionMethod instance met arg)
  end.
  Arguments indexify_action' t mapping /.

  Section HideScoping.
    Import Coq.Strings.String.
    Open Scope string_scope.
    Definition fresh_mapping : mapping_t := (1, fun x =>
                                              (* if eqb x "res" then 1 *)
                                              (* else if eqb x "guard" then 2 *)
                                              (* else *)
                                               0).
    Close Scope string_scope.
  End HideScoping.

  Definition indexify_action (t : @action String.string) := snd (indexify_action' t fresh_mapping).
  Definition indexify_expr (t : @expr String.string) := snd (indexify_expr' t fresh_mapping).
End Indexification.

Arguments indexify_action !t /.
Arguments indexify_expr !t /.
Section Unindexification.
  Fixpoint unindexify_expr (t : @expr varname) : @expr String.string :=
  match t with
  | Var v => Var (stringvar v)
  | Abort => Abort
  | Arg => Arg 
  | ZOp prim =>
    ZOp prim 
  | UOp prim arg =>
    let arg := unindexify_expr arg in
    UOp prim arg
  | BOp prim arg1 arg2 =>
    let arg1 := unindexify_expr arg1 in
    let arg2 := unindexify_expr arg2 in
    BOp prim arg1 arg2
  | SetVar v e =>
    let e := unindexify_expr e in
     SetVar (stringvar v) e
  | Ternary c t f =>
    let c := unindexify_expr c in
    let t := unindexify_expr t in
    let f := unindexify_expr f in
    Ternary c t f
  | ValMethod instance met arg =>
    let arg := unindexify_expr arg in
    ValMethod instance met arg
  end.

  Fixpoint unindexify_action  (t : @action varname) : @action String.string :=
  match t with
  | Skip => Skip
  | If c t f =>
    let c := unindexify_expr c in
    let t := unindexify_action t in
    let f := unindexify_action f in
    If c t f
  | Expr e =>
    let e := unindexify_expr e in
    Expr e
  | Seq a1 a2 =>
    let a1 := unindexify_action a1 in
    let a2 := unindexify_action a2 in
    Seq a1 a2
  | ActionMethod  instance met arg =>
    let arg := unindexify_expr arg in
    ActionMethod instance met arg
  end
  .
End Unindexification.