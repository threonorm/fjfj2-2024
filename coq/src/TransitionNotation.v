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

Open Scope N.


Notation "a '--{' r '}-->' b" :=
    (r (a : SModule) (b : SModule)) (at level 201, only parsing).

Require Import IdentParsing.
Notation "'{' m name arg '}'" := (match index_of (ident_to_string! name) (action_methods (sm:= m)) O with  
      | Some x => aget (action_spec m) x arg
      | None => unexisting_rule
      end)  
  ( m constr at level 0, name constr at level 0,  only parsing).
Notation "'{' m name '}'" := (match index_of (ident_to_string! name) (rule_names (sm:= m)) O with 
  | Some x => nth x (rule_spec m) unexisting_rule
  | None => 
      match index_of (ident_to_string! name) (action_methods (sm:= m)) O with  
      | Some x => aget (action_spec m) x 0%N
      | None => unexisting_rule
      end
  end)
  (m constr at level 0, name constr at level 0,  only parsing).

Record Viewable_transition:= {
object_viewed :> (SModule -> SModule -> Prop);
spec_corresponding : spec_module_t;
view : ((module spec_corresponding) * N * string)%type
}.

Notation "'{{' v m '}}'" := (Build_Viewable_transition _ _ (m, 0 , v)) 
( only printing, v custom pr_string , m constr, right associativity).
Notation "'{{' v m arg '}}'" := (Build_Viewable_transition _ _ (m, arg, v)) 
( only printing, v custom pr_string , m constr, right associativity).

Ltac print_transitions :=
simpl (index_of _ _ _); cbv beta iota;
match goal with 
| [ H: context[ aget (action_spec (spec_of ?m)) ?i ?arg] |- _] =>
        let y:= constr:(@action_methods _ m)in 
        let name := eval cbv in (nth i (@action_methods _ m) "NOTFOUND"%string) in 
        change (aget (action_spec m) i arg) with
                (object_viewed {| object_viewed := (aget (action_spec m) i arg);
                   view := (m, arg,name) |}) in H
| [ H: context[nth ?i (rule_spec (spec_of ?m)) unexisting_rule] |- _] =>
        let name := eval cbv in (nth i (@rule_names _ m) "NOTFOUND"%string) in 
        change (nth i (rule_spec m) unexisting_rule) with
                (object_viewed {| object_viewed := (nth i (rule_spec m) unexisting_rule);
                   view := (m, 0%N,name) |}) in H
| [ |- context[ aget (action_spec (spec_of ?m)) ?i ?arg] ] =>
        let y:= constr:(@action_methods _ m) in 
        let name := eval cbv in (nth i (@action_methods _ m) "NOTFOUND"%string) in 
        change (aget (action_spec m) i arg) with
                (object_viewed {| object_viewed := (aget (action_spec m) i arg);
                   view := (m, arg, name) |}) 
| [ |- context[nth ?i (rule_spec (spec_of ?m)) unexisting_rule]] =>
        let name := eval cbv in (nth i (@rule_names _ m) "NOTFOUND"%string) in 
        change (nth i (rule_spec m) unexisting_rule) with
                (object_viewed {| object_viewed := (nth i (rule_spec m) unexisting_rule);
                   view := (m, 0%N,name) |})
end.

Notation "a '--' r '-->' b" :=
    ((object_viewed r) a b) (at level 201, only printing, format "a '--' r '-->' b").
