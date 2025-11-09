Require Import
        LangFjfj2
        IdentParsing
        Indexification. 

Require Import Ltac2.Ltac2.
Require Import NArith.

Require Coq.Strings.String.
Section Utils.
     Import Coq.Strings.String.
     Local Open Scope string_scope.
     Definition underscore := "_".
     Definition test_str := "yoyo".
End Utils.

Declare Custom Entry fjfj_expr.
Declare Custom Entry fjfj_exprlist.
Declare Custom Entry fjfj_args.
Declare Custom Entry fjfj_binders.
Declare Custom Entry fjfj_action.
Declare Custom Entry fjfj_actionlist.
Declare Custom Entry pr_char.

Require Import Coq.Strings.Ascii.

(* String printing *)
Notation "'a'" := "a"%char (in custom pr_char).
Notation "'b'" := "b"%char (in custom pr_char).
Notation "'c'" := "c"%char (in custom pr_char).
Notation "'d'" := "d"%char (in custom pr_char).
Notation "'e'" := "e"%char (in custom pr_char).
Notation "'f'" := "f"%char (in custom pr_char).
Notation "'g'" := "g"%char (in custom pr_char).
Notation "'h'" := "h"%char (in custom pr_char).
Notation "'i'" := "i"%char (in custom pr_char).
Notation "'j'" := "j"%char (in custom pr_char).
Notation "'k'" := "k"%char (in custom pr_char).
Notation "'l'" := "l"%char (in custom pr_char).
Notation "'m'" := "m"%char (in custom pr_char).
Notation "'n'" := "n"%char (in custom pr_char).
Notation "'o'" := "o"%char (in custom pr_char).
Notation "'p'" := "p"%char (in custom pr_char).
Notation "'q'" := "q"%char (in custom pr_char).
Notation "'r'" := "r"%char (in custom pr_char).
Notation "'s'" := "s"%char (in custom pr_char).
Notation "'t'" := "t"%char (in custom pr_char).
Notation "'u'" := "u"%char (in custom pr_char).
Notation "'v'" := "v"%char (in custom pr_char).
Notation "'w'" := "w"%char (in custom pr_char).
Notation "'x'" := "x"%char (in custom pr_char).
Notation "'y'" := "y"%char (in custom pr_char).
Notation "'z'" := "z"%char (in custom pr_char).
Notation "'A'" := "A"%char (in custom pr_char).
Notation "'B'" := "B"%char (in custom pr_char).
Notation "'C'" := "C"%char (in custom pr_char).
Notation "'D'" := "D"%char (in custom pr_char).
Notation "'E'" := "E"%char (in custom pr_char).
Notation "'F'" := "F"%char (in custom pr_char).
Notation "'G'" := "G"%char (in custom pr_char).
Notation "'H'" := "H"%char (in custom pr_char).
Notation "'I'" := "I"%char (in custom pr_char).
Notation "'J'" := "J"%char (in custom pr_char).
Notation "'k'" := "k"%char (in custom pr_char).
Notation "'L'" := "L"%char (in custom pr_char).
Notation "'M'" := "M"%char (in custom pr_char).
Notation "'N'" := "N"%char (in custom pr_char).
Notation "'O'" := "O"%char (in custom pr_char).
Notation "'P'" := "P"%char (in custom pr_char).
Notation "'Q'" := "Q"%char (in custom pr_char).
Notation "'R'" := "R"%char (in custom pr_char).
Notation "'S'" := "S"%char (in custom pr_char).
Notation "'T'" := "T"%char (in custom pr_char).
Notation "'U'" := "U"%char (in custom pr_char).
Notation "'V'" := "V"%char (in custom pr_char).
Notation "'W'" := "W"%char (in custom pr_char).
Notation "'X'" := "X"%char (in custom pr_char).
Notation "'Y'" := "Y"%char (in custom pr_char).
Notation "'Z'" := "Z"%char (in custom pr_char).
Notation "'0'" := "0"%char (in custom pr_char).
Notation "'1'" := "1"%char (in custom pr_char).
Notation "'2'" := "2"%char (in custom pr_char).
Notation "'3'" := "3"%char (in custom pr_char).
Notation "'4'" := "4"%char (in custom pr_char).
Notation "'5'" := "5"%char (in custom pr_char).
Notation "'6'" := "6"%char (in custom pr_char).
Notation "'7'" := "7"%char (in custom pr_char).
Notation "'8'" := "8"%char (in custom pr_char).
Notation "'9'" := "9"%char (in custom pr_char).
Notation "'_'" := "_"%char (in custom pr_char).

Declare Custom Entry pr_string.
Notation "h" := (h)
 (in custom pr_string at level 0, h constr, format "h", only printing).
Notation "" := String.EmptyString (in custom pr_string at level 1, only printing).
Notation "h t" := (String.String h t)
 (in custom pr_string at level 1, h custom pr_char, t custom pr_string,
  right associativity, format "h t", only printing).

(* Notation "x" := (Var x) (at level 2, x custom pr_string, only printing, right associativity).
Eval cbv in Var 3.
Eval cbv in Var test_str. *)

(* fjfj_exprlist parsing *)

Notation "a b" :=  (BOp ESeq a b) (in custom fjfj_exprlist at level 100,
                                 a custom fjfj_exprlist,
                                 b custom fjfj_exprlist,
                                 right associativity,
                                 only parsing).
Notation "a" := (a)
     (in custom fjfj_exprlist at level 0,
      a custom fjfj_expr,
      only parsing).

Notation "a b" :=  (BOp Merge a b) (in custom fjfj_args at level 100,
                                 a custom fjfj_args,
                                 b custom fjfj_args,
                                 right associativity,
                                 only parsing).
Notation "a" := (a)
     (in custom fjfj_args at level 0,
      a custom fjfj_expr,
      only parsing).


(* fjfj_actionlist parsing *)
Notation "a b" := (Seq a b)
     (in custom fjfj_actionlist at level 100,
      a custom fjfj_actionlist,
      b custom fjfj_actionlist,
      right associativity,
      only parsing).
Notation "a" := (a)
     (in custom fjfj_actionlist at level 0,
      a custom fjfj_action, 
      only parsing).

(* Leaf parsing, why did I do that? I think it was to support both literals and variable for the leafs, without any extra keys *)
Inductive __fjfj_Mark : N -> Type := __fjfj_mark : forall n, __fjfj_Mark n  .
Class __fjfj_TCMark (n : N) : Type := {__fjfj_tcmark : __fjfj_Mark n}.
Global Instance __fjfj_connect_mark (n : N) : __fjfj_TCMark n := {| __fjfj_tcmark := __fjfj_mark n|}.
Notation "a" := 
  (match (_ : (__fjfj_TCMark ?[top] )), true return expr with
    | @Build___fjfj_TCMark _ (@__fjfj_mark a), true => 
      ltac2:(let t := Constr.pretype a in
             match Constr.Unsafe.kind t with
             | Constr.Unsafe.Var v =>
               (* let coq_string := coq_string_of_ident v in *)
               let coq_string := IdentToStringImpl.ident_to_coq v in
               ltac1:(instantiate (top:= 0%N));
               let newterm := constr:(@Var _ $coq_string) in
               exact ($newterm)
             | _ => 
               refine open_constr:(let constraint := ?[x] : __fjfj_Mark $t in _) > [
               Control.enter (fun () => exact (__fjfj_mark $t) )| ];
               try (let tc_top := constr:(eq_refl : ?top = $t) in ltac1:(idtac));
               let newterm := constr:(ZOp (var:= String.string) (Cst $t)) in
               exact ($newterm)
             end)
    | _, _ => Var (String.EmptyString)
    end)    
    (in custom fjfj_expr at level 0,
     a constr at level 0,
     only parsing).
Fixpoint seq_var (v : list String.string) (e : expr (var := String.string)):=
     match v with 
     | nil => 
          (UOp PassCst (ZOp (Cst 0)))
     | cons s nil =>
          BOp ESeq (SetVar s e) (UOp PassCst (ZOp (Cst 0))) 
     | cons s l =>
          BOp ESeq (SetVar s (UOp Split1 e)) (seq_var l (UOp Split2 e))
     end.

(* fjfj_expr parsing *)
Notation "'(' 'fjfj_expr' e ')'" := 
     (ltac:(let r := eval cbn zeta iota beta delta [__fjfj_connect_mark] in
           (indexify_expr (e : expr (var:= String.string))) in exact r))
     (e custom fjfj_expr at level 200, only parsing).
Notation "'(' 'value_method' '(' varlist ')' e ')'" := 
     (ltac:(let r := eval cbn zeta iota beta delta [__fjfj_connect_mark] in
           (indexify_expr (
               BOp ESeq
               (seq_var varlist 
                    Arg)
               (e : expr (var:= String.string)))) in exact r))
     (e custom fjfj_expr at level 200,
      varlist custom fjfj_binders,
     only parsing).
Notation "'(' 'value_method' '('')' e ')'" := 
     (ltac:(let r := eval cbn zeta iota beta delta [__fjfj_connect_mark] in
           (indexify_expr (e : expr (var:= String.string))) in exact r))
     (e custom fjfj_expr at level 200, only parsing).
Notation "'(' 'value_method' '()' e ')'" := 
     (ltac:(let r := eval cbn zeta iota beta delta [__fjfj_connect_mark] in
           (indexify_expr (e : expr (var:= String.string))) in exact r))
     (e custom fjfj_expr at level 200, only parsing).
Notation "'(' 'fjfj_expr_wm' e m ')'" := 
     (indexify_expr' e m)
     (e custom fjfj_expr at level 200,
     m constr,
      format "'(' 'fjfj_expr_wm' '[v' '/' e '/' ']' m ')'").
Notation "'(' 'begin' l ')'" :=
     (l)
     (in custom fjfj_expr at level 200,
      l custom fjfj_exprlist,
      only parsing).
Notation "'abort'":=
     (Abort)
     (in custom fjfj_expr at level 200,
      only parsing).
Notation "'(' '+' f g ')'" :=
     (BOp Plus f g) 
     (in custom fjfj_expr at level 200,
      f custom fjfj_expr,
      g custom fjfj_expr,
      only parsing).
Notation "'(' '&' f g ')'" :=
     (BOp BwAnd f g) 
     (in custom fjfj_expr at level 200,
      f custom fjfj_expr,
      g custom fjfj_expr,
      only parsing).
Notation "'(' '|' f g ')'" :=
     (BOp BwOr f g)
     (in custom fjfj_expr at level 200,
      f custom fjfj_expr,
      g custom fjfj_expr,
      only parsing).
Notation "'(' '!' g ')'" :=
     (UOp (BwNot 1) g) 
     (in custom fjfj_expr at level 200, 
      g custom fjfj_expr at level 200,
      only parsing).
Notation "'(' '~' sz g ')'" :=
     (UOp (BwNot sz) g) 
     (in custom fjfj_expr at level 200, 
      sz constr at level 0,
      g custom fjfj_expr at level 200,
      only parsing).
Notation "'(' ':' sz g ')'" :=
     (UOp (BwSize sz) g) 
     (in custom fjfj_expr at level 200, 
      sz constr at level 0,
      g custom fjfj_expr at level 200,
      only parsing).
Notation "'(' '='  f g ')'" :=
     (BOp Eq f g)
     (in custom fjfj_expr at level 200,
      f custom fjfj_expr,
      g custom fjfj_expr,
      only parsing).
Notation "'(' '<'  f g ')'" :=
     (BOp Lt f g)
     (in custom fjfj_expr at level 200,
      f custom fjfj_expr,
      g custom fjfj_expr,
      only parsing).
Notation "'(' '>'  f g ')'" :=
     (BOp Gt f g)
     (in custom fjfj_expr at level 200,
      f custom fjfj_expr,
      g custom fjfj_expr,
      only parsing).
Notation "'(' '<='  f g ')'" :=
     (BOp Leq f g)
     (in custom fjfj_expr at level 200,
      f custom fjfj_expr,
      g custom fjfj_expr,
      only parsing).
Notation "'(' '>='  f g ')'" :=
     (BOp Geq f g)
     (in custom fjfj_expr at level 200,
      f custom fjfj_expr,
      g custom fjfj_expr,
      only parsing).
Notation "'(' 'set' var e ')'" :=
     (SetVar (ident_to_string! var) e)
     (in custom fjfj_expr at level 200,
      var constr at level 0,
      e custom fjfj_expr,
      only parsing).

Notation "a b" :=  (app a b) (in custom fjfj_binders at level 100,
                                 a custom fjfj_binders,
                                 b custom fjfj_binders,
                                 right associativity,
                                 only parsing).
Notation "a" := (cons (ident_to_string! a) nil : list String.string)
     (in custom fjfj_binders at level 0,
      a constr at level 0,
      only parsing).

Notation "'pass'" :=
     (UOp PassCst (ZOp (Cst 0)))
     (in custom fjfj_expr at level 210,
      only parsing).
Notation "'(' 'set' '(' varlist ')' e ')'" :=
     (* TODO potentially fix to add a new binder 
     and then seq
     (BOp ESeq a b)
     *)
(BOp ESeq (SetVar ltac:( let r := eval cbv in (String.concat underscore varlist ) in exact r ) e) 
     (seq_var varlist ltac:( let r := eval cbv in (String.concat underscore  varlist ) in 
          exact (Var (var:= String.string) r))))
     (* (seq_var varlist e) *)
     (in custom fjfj_expr at level 200,
      varlist custom fjfj_binders,
      e custom fjfj_expr,
      only parsing).
Notation "'met_arg'" :=
     (Arg (var:=String.string))
     (in custom fjfj_expr at level 200,
      only parsing).
Notation "'(' '#' e ')'" :=
     (e)
     (in custom fjfj_expr at level 200,
     e custom fjfj_args,
      only parsing).

Definition __Ltac2_MarkedInstance (A: Type) := A.
Definition __Ltac2_MarkedMet (A: Type) := A.

Ltac serialize_instance_in_context :=
    ltac2:(match! goal with
           | [ h: __Ltac2_MarkedInstance _ |- _ ] =>
             let coq_string := IdentToStringImpl.ident_to_coq h in
             exact ($coq_string)
           | [  |- _ ] => Control.throw_invalid_argument "No instance in the context"
           end).
Ltac serialize_met_in_context :=
    ltac2:(match! goal with
           | [ h: __Ltac2_MarkedMet _ |- _ ] =>
             let coq_string := IdentToStringImpl.ident_to_coq h in
             exact ($coq_string)
           | [  |- _ ] => Control.throw_invalid_argument "No instance in the context"
           end).
Notation "'{' met  instance '}'" :=
          match (true : __Ltac2_MarkedInstance _), (true : __Ltac2_MarkedMet _) with
          | instance, met => ltac:(
                    let s_inst := constr:(ltac:(serialize_instance_in_context)) in
                    (* idtac s_inst; *)
                    let ninstance_idx := eval cbv in (index_of s_inst idx O) in 
                    (* idtac "nsintance" ninstance_idx; *)
                    match ninstance_idx with 
                    | Some ?instance_idx => 
                         let s_met := constr:(ltac:(serialize_met_in_context)) in
                         (* idtac "intance" instance_idx; *)
                         let mmet_idx := eval cbv in (index_of s_met (value_methods (sm:= (aget code instance_idx))) O) in 
                         match mmet_idx with 
                         | Some ?met_idx =>  
                              (* idtac "Resolved" instance_idx met_idx; *)
                              exact (ValMethod (var:= String.string) 
                                             {| idxvar := instance_idx; stringvar := s_inst |} 
                                             {| idxvar := met_idx; stringvar := s_met |}
                                             (ZOp (Cst 0)) : expr)
                         | _ => idtac "no method found"
                         end
                    | _ => idtac "no instance found" 
                    end )
          end
     (in custom fjfj_expr at level 200, 
      instance ident,
      met ident,
      only parsing).
Notation "'(' '(' instance met ')' ')'" :=
          match (true : __Ltac2_MarkedInstance _), (true : __Ltac2_MarkedMet _) with
          | instance, met => ltac:(
                    let s_inst := constr:(ltac:(serialize_instance_in_context)) in
                    (* idtac s_inst; *)
                    let ninstance_idx := eval cbv in (index_of s_inst idx O) in 
                    (* idtac "nsintance" ninstance_idx; *)
                    match ninstance_idx with 
                    | Some ?instance_idx => 
                         let s_met := constr:(ltac:(serialize_met_in_context)) in
                         (* idtac "intance" instance_idx; *)
                         let mmet_idx := eval cbv in (index_of s_met (value_methods (sm:= (aget code instance_idx))) O) in 
                         match mmet_idx with 
                         | Some ?met_idx =>  
                              (* idtac "Resolved" instance_idx met_idx; *)
                              exact (ValMethod (var:= String.string) 
                                             {| idxvar := instance_idx; stringvar := s_inst |} 
                                             {| idxvar := met_idx; stringvar  := s_met |}
                                                  (ZOp (Cst 0)) : expr)
                         | _ => idtac "no method found"
                         end
                    | _ => idtac "no instance found" 
                    end )
          end
     (in custom fjfj_expr at level 200, 
      instance ident,
      met ident,
      only parsing).
Notation "'(' '(' instance met ')' e ')'" :=
          match (true : __Ltac2_MarkedInstance _), (true : __Ltac2_MarkedMet _) with
          | instance, met => ltac:(
                    let s_inst := constr:(ltac:(serialize_instance_in_context)) in
                    (* idtac s_inst; *)
                    (* let s_inst := constr:("valid") in *)
                    let ninstance_idx := eval cbv in (index_of s_inst idx O) in 
                    (* idtac "nsintance" ninstance_idx; *)
                    match ninstance_idx with 
                    | Some ?instance_idx => 
                         (* let s_met := constr:("read") in *)
                         let s_met := constr:(ltac:(serialize_met_in_context)) in
                         (* idtac "intance" instance_idx; *)
                         let mmet_idx := eval cbv in (index_of s_met (value_methods (sm:= (aget code instance_idx))) O) in 
                         match mmet_idx with 
                         | Some ?met_idx =>  
                              (* idtac "Resolved" instance_idx met_idx; *)
                              exact (ValMethod (var:= String.string) 
                                             {| idxvar := instance_idx; stringvar := s_inst |} 
                                             {| idxvar := met_idx; stringvar  := s_met |}
                              e : expr)
                              (* exact (instance_idx, met_idx) *)
                         | _ => idtac "no method found"
                         end
                    | _ => idtac "no instance found" 
                    end )
          end
(in custom fjfj_expr at level 200, 
      instance ident,
      met ident,
      e custom fjfj_expr,
      only parsing)
     .
Notation "'{' met   instance  e '}'" :=
          match (true : __Ltac2_MarkedInstance _), (true : __Ltac2_MarkedMet _) with
          | instance, met => ltac:(
                    let s_inst := constr:(ltac:(serialize_instance_in_context)) in
                    (* idtac s_inst; *)
                    (* let s_inst := constr:("valid") in *)
                    let ninstance_idx := eval cbv in (index_of s_inst idx O) in 
                    (* idtac "nsintance" ninstance_idx; *)
                    match ninstance_idx with 
                    | Some ?instance_idx => 
                         (* let s_met := constr:("read") in *)
                         let s_met := constr:(ltac:(serialize_met_in_context)) in
                         (* idtac "intance" instance_idx; *)
                         let mmet_idx := eval cbv in (index_of s_met (value_methods (sm:= (aget code instance_idx))) O) in 
                         match mmet_idx with 
                         | Some ?met_idx =>  
                              (* idtac "Resolved" instance_idx met_idx; *)
                              exact (ValMethod (var:= String.string)
                                             {| idxvar := instance_idx; stringvar := s_inst |} 
                                             {| idxvar := met_idx; stringvar  := s_met |}
                                             e : expr)
                              (* exact (instance_idx, met_idx) *)
                         | _ => idtac "no method found"
                         end
                    | _ => idtac "no instance found" 
                    end )
          end
(in custom fjfj_expr at level 200, 
      instance ident,
      met ident,
      e custom fjfj_expr,
      only parsing)
     .

Notation "'(' a  l ')'" :=
     (UOp (Fn (ident_to_string! a)) l)
     (in custom fjfj_expr at level 200,
      a constr at level 0,
      l custom fjfj_expr,
      only parsing).
Notation "'(' 'if' c t f ')'" :=
     (Ternary c t f)
     (in custom fjfj_expr at level 200,
      c custom fjfj_expr,
      t custom fjfj_expr,
      f custom fjfj_expr,
      only parsing).
Notation "'`(' e ')'" := (e)
     (in custom fjfj_expr at level 200,
      e constr,
      only parsing).
Notation "'`{' e '}'" := (ZOp (var:= String.string) (Cst e))
     (in custom fjfj_expr at level 200,
      e constr,
      only parsing).



(* fjfj_action  *)
Notation "'(' 'fjfj_action' e ')'" :=
     (ltac:(let r := eval cbn zeta iota beta delta [__fjfj_connect_mark] in (indexify_action (e : action (var:= String.string))) in exact r))
     (e custom fjfj_action at level 200, only parsing).

Notation "'(' 'rule' e ')'" :=
     (ltac:(let r := eval cbn zeta iota beta delta [__fjfj_connect_mark] in (indexify_action (e : action (var:= String.string))) in 
     let r:= eval cbv in r in exact r))
     (e custom fjfj_action at level 200, only parsing).
Notation "'(' 'action_method' '(' varlist ')' e ')'" :=
     (ltac:(let r := eval cbn zeta iota beta delta [__fjfj_connect_mark] in (indexify_action 
     (Seq (Expr (seq_var varlist Arg))
     (e : action (var:= String.string)))) in 
     let r:= eval cbv in r in
     exact r))
     (e custom fjfj_action at level 200,
      varlist custom fjfj_binders,
     only parsing).

     (* Empty case requires two rules to handle whitespace *)
Notation "'(' 'action_method' '()' e ')'" :=
     (ltac:(let r := eval cbn zeta iota beta delta [__fjfj_connect_mark] in (indexify_action 
     (e : action (var:= String.string))) in 
     let r:= eval cbv in r in
     exact r))
     (e custom fjfj_action at level 200,
     only parsing).
Notation "'(' 'action_method' '('')' e ')'" :=
     (ltac:(let r := eval cbn zeta iota beta delta [__fjfj_connect_mark] in (indexify_action 
     (e : action (var:= String.string))) in
     let r:= eval cbv in r in
     exact r))
     (e custom fjfj_action at level 200,
     only parsing).
Notation "'(' 'fjfj_action_wm' e m ')'" :=
     (indexify_action' e m)
     (e custom fjfj_action at level 200,
     m constr,
      format "'(' 'fjfj_action_wm' '[v' '/' e ']' m ')'").
Notation "'(' 'begin' l ')'" :=
     (l)
     (in custom fjfj_action at level 200,
      l custom fjfj_actionlist,
      only parsing).

Notation "'{' met  instance e '}'" :=
      match (true : __Ltac2_MarkedInstance _), (true : __Ltac2_MarkedMet _) with
          | instance, met => ltac:(
                    let s_inst := constr:(ltac:(serialize_instance_in_context)) in
                    (* idtac s_inst; *)
                    (* let s_inst := constr:("valid") in *)
                    let ninstance_idx := eval cbv in (index_of s_inst idx O) in 
                    (* idtac "nsintance" ninstance_idx; *)
                    match ninstance_idx with 
                    | Some ?instance_idx => 
                         (* let s_met := constr:("read") in *)
                         let s_met := constr:(ltac:(serialize_met_in_context)) in
                         (* idtac "intance" instance_idx; *)
                         let mmet_idx := eval cbv in (index_of s_met (action_methods (sm:= (aget code instance_idx))) O) in 
                         match mmet_idx with 
                         | Some ?met_idx =>  
                              (* idtac "Resolved" instance_idx met_idx; *)
                              exact (ActionMethod (var:= String.string) 
                                             {| idxvar := instance_idx; stringvar := s_inst |} 
                                             {| idxvar := met_idx; stringvar  := s_met |}
                                             e )
                              (* exact (instance_idx, met_idx) *)
                         | _ => idtac "no method found"
                         end
                    | _ => idtac "no instance found" 
                    end )
          end
     (in custom fjfj_action at level 199, 
      instance ident,
      met ident,
      e custom fjfj_expr,
      only parsing).
Notation "'{' met instance  '}'" :=
          match (true : __Ltac2_MarkedInstance _), (true : __Ltac2_MarkedMet _) with
          | instance, met => ltac:(
                    let s_inst := constr:(ltac:(serialize_instance_in_context)) in
                    (* idtac s_inst; *)
                    let ninstance_idx := eval cbv in (index_of s_inst idx O) in 
                    (* idtac "nsintance" ninstance_idx; *)
                    match ninstance_idx with 
                    | Some ?instance_idx => 
                         let s_met := constr:(ltac:(serialize_met_in_context)) in
                         (* idtac "intance" instance_idx; *)
                         let mmet_idx := eval cbv in (index_of s_met (action_methods (sm:= (aget code instance_idx))) O) in 
                         match mmet_idx with 
                         | Some ?met_idx =>  
                              (* idtac "Resolved" instance_idx met_idx; *)
                              exact (ActionMethod (var:= String.string)
                                             {| idxvar := instance_idx; stringvar := s_inst |} 
                                             {| idxvar := met_idx; stringvar  := s_met |}
                                             (ZOp (Cst 0)) )
                         | _ => idtac "no method found"
                         end
                    | _ => idtac "no instance found" 
                    end )
          end
     (* (ActionMethod instance met (ZOp (Cst 0) (var:=String.string))) *)
     (in custom fjfj_action at level 199, 
      instance ident,
      met ident,
      only parsing).
Notation "'(' '(' instance met ')' e ')'" :=
      match (true : __Ltac2_MarkedInstance _), (true : __Ltac2_MarkedMet _) with
          | instance, met => ltac:(
                    let s_inst := constr:(ltac:(serialize_instance_in_context)) in
                    (* idtac s_inst; *)
                    (* let s_inst := constr:("valid") in *)
                    let ninstance_idx := eval cbv in (index_of s_inst idx O) in 
                    (* idtac "nsintance" ninstance_idx; *)
                    match ninstance_idx with 
                    | Some ?instance_idx => 
                         (* let s_met := constr:("read") in *)
                         let s_met := constr:(ltac:(serialize_met_in_context)) in
                         (* idtac "intance" instance_idx; *)
                         let mmet_idx := eval cbv in (index_of s_met (action_methods (sm:= (aget code instance_idx))) O) in 
                         match mmet_idx with 
                         | Some ?met_idx =>  
                              (* idtac "Resolved" instance_idx met_idx; *)
                              exact (ActionMethod (var:= String.string) 
                                             {| idxvar := instance_idx; stringvar := s_inst |} 
                                             {| idxvar := met_idx; stringvar  := s_met |}
                                             e )
                              (* exact (instance_idx, met_idx) *)
                         | _ => idtac "no method found"
                         end
                    | _ => idtac "no instance found" 
                    end )
          end
     (in custom fjfj_action at level 200, 
      instance ident,
      met ident,
      e custom fjfj_expr,
      only parsing).
Notation "'(' '(' instance met ')' ')'" :=
          match (true : __Ltac2_MarkedInstance _), (true : __Ltac2_MarkedMet _) with
          | instance, met => ltac:(
                    let s_inst := constr:(ltac:(serialize_instance_in_context)) in
                    (* idtac s_inst; *)
                    let ninstance_idx := eval cbv in (index_of s_inst idx O) in 
                    (* idtac "nsintance" ninstance_idx; *)
                    match ninstance_idx with 
                    | Some ?instance_idx => 
                         let s_met := constr:(ltac:(serialize_met_in_context)) in
                         (* idtac "intance" instance_idx; *)
                         let mmet_idx := eval cbv in (index_of s_met (action_methods (sm:= (aget code instance_idx))) O) in 
                         match mmet_idx with 
                         | Some ?met_idx =>  
                              (* idtac "Resolved" instance_idx met_idx; *)
                              exact (ActionMethod (var:= String.string)
                                                  {| idxvar := instance_idx; stringvar := s_inst|} 
                                                  {| idxvar := met_idx; stringvar  := s_met |}
                                                   (ZOp (Cst 0)) )
                         | _ => idtac "no method found"
                         end
                    | _ => idtac "no instance found" 
                    end )
          end
     (* (ActionMethod instance met (ZOp (Cst 0) (var:=String.string))) *)
     (in custom fjfj_action at level 200, 
      instance ident,
      met ident,
      only parsing).

Notation "'(' 'if' c t f ')'" :=
     (If c t f)
     (in custom fjfj_action at level 200,
      c custom fjfj_expr,
      t custom fjfj_action,
      f custom fjfj_action,
      only parsing).
Notation "'pass'" :=
     (Skip  (var:= String.string))
     (in custom fjfj_action at level 200,
      only parsing).
Notation "'(' 'set' var e ')'" :=
     (Expr (SetVar (ident_to_string! var) e))
     (in custom fjfj_action at level 200,
      var constr at level 0,
      e custom fjfj_expr,
      only parsing).
(* Notation "'#' a " :=
     (Expr a)
     (in custom fjfj_action at level 200,
      a custom fjfj_expr). *)
Notation "'abort'" :=
     (Expr Abort)
     (in custom fjfj_action at level 200).

Notation "'(' 'set' '(' varlist ')' e ')'" :=
     (* TODO Think about creating a new binder? *)
     (
          Seq (Expr (SetVar ltac:( let r := eval cbv in (String.concat underscore varlist ) in exact r ) e)) 
          (Expr (seq_var varlist 
                    ltac:(let r := eval cbv in (String.concat underscore  varlist ) in
                          exact (Var (var:= String.string) r) ))))
     (in custom fjfj_action at level 200,
      varlist custom fjfj_binders,
      e custom fjfj_expr,
      only parsing).
Notation "'`(' e ')'" :=
     (e)
     (in custom fjfj_action,
      e constr,
      only parsing).


(* -------------------------------- *)
(* Notations for printing           *)
(* -------------------------------- *)
(* Open Scope string. *)


Notation "i" := (ZOp (Cst i)) (only printing, i custom pr_string , at level 2, right associativity).
Notation "a" :=
     (Expr a)
     (only printing,  a custom pr_string, at level 2, right associativity). 
Notation "a" :=
     (BOp ESeq a (UOp PassCst (ZOp (Cst 0))))
     (only printing, at level 2, a custom pr_string, right associativity).
     
Notation "name" := (Var ({|idxvar := _; stringvar:= name|})) (only printing, name custom pr_string, at level 2, right associativity).
Notation "name" := (Var name) (only printing, name custom pr_string, at level 2, right associativity).


Notation "'(' '#' a b c d ')'" :=
     (BOp Merge a (BOp Merge b (BOp Merge c d)))
     (only printing).
Notation "'(' '#' a b c ')'" :=
     (BOp Merge a (BOp Merge b c))
     (only printing).
Notation "'(' '#' a b ')'" :=
     (BOp Merge a b)
     (only printing).


Notation "'(' '=' f g ')'" :=
     (BOp Eq f g)
     (only printing,
      format "'(' '='  f  g ')'").
Notation "'(' '<' f g ')'" :=
     (BOp Lt f g)
     (only printing,
      format "'(' '<'  f  g ')'").
Notation "'(' '<=' f g ')'" :=
     (BOp Leq f g)
     (only printing,
      format "'(' '<='  f  g ')'").
Notation "'(' '>' f g ')'" :=
     (BOp Gt f g)
     (only printing,
      format "'(' '>'  f  g ')'").
Notation "'(' '>=' f g ')'" :=
     (BOp Geq f g)
     (only printing,
      format "'(' '>='  f  g ')'").
Notation "'(' 'set' '(' var1 var2 var3 var4 ')' e ')'" :=
     (BOp ESeq 
          (SetVar {|idxvar:= _; stringvar:= var1|}  (UOp Split1 e))
          (BOp ESeq
               (SetVar {|idxvar:= _; stringvar:= var2|} (UOp Split1 (UOp Split2 e)))
               (BOp ESeq 
                    (SetVar {|idxvar:= _; stringvar:= var3|} (UOp Split1 (UOp Split2 (UOp Split2 e))))
                    (BOp ESeq 
                         (SetVar {|idxvar:= _; stringvar:= var4|} (UOp Split2 (UOp Split2 (UOp Split2 e))))
                         (UOp (var := varname) PassCst (ZOp (Cst 0)))
                         ))))
     (only printing, 
     var1 custom pr_string,
     var2 custom pr_string,
     var3 custom pr_string,
     var4 custom pr_string,
     at level 200).
Notation "'(' 'set' '(' var1 var2 var3 ')' e ')'" :=
     (BOp ESeq 
          (SetVar {|idxvar:= _; stringvar:= var1|} (UOp Split1 e))
          (BOp ESeq
               (SetVar {|idxvar:= _; stringvar:= var2|} (UOp Split1 (UOp Split2 e)))
               (BOp ESeq 
                    (SetVar {|idxvar:= _; stringvar:= var3|} (UOp Split2 (UOp Split2 e)))
                    (UOp (var := varname) PassCst (ZOp (Cst 0))))))
     (only printing,
     var1 custom pr_string,
     var2 custom pr_string,
     var3 custom pr_string,
      at level 200).
Notation "'(' 'set' '(' var1 var2 ')' e ')'" :=
     (BOp ESeq 
          (SetVar {|idxvar:= _; stringvar:= var1|} (UOp Split1 e))
          (BOp ESeq (SetVar {|idxvar:= _; stringvar:= var2|} (UOp Split2 e))
               (UOp (var := varname)PassCst (ZOp (Cst 0)))))
     (only printing,
     var1 custom pr_string,
     var2 custom pr_string,
      at level 200).

Notation "'(' 'set' '(' var1 var2 var3 var4 ')' e ')'" :=
     (BOp ESeq 
          (SetVar var1  (UOp Split1 e))
          (BOp ESeq
               (SetVar var2 (UOp Split1 (UOp Split2 e)))
               (BOp ESeq 
                    (SetVar var3 (UOp Split1 (UOp Split2 (UOp Split2 e))))
                    (BOp ESeq 
                         (SetVar var4 (UOp Split2 (UOp Split2 (UOp Split2 e))))
                          (UOp (var := String.string) PassCst (ZOp (Cst 0)))))))
     (only printing, 
     var1 custom pr_string,
     var2 custom pr_string,
     var3 custom pr_string,
     var4 custom pr_string,
     at level 200).
Notation "'(' 'set' '(' var1 var2 var3 ')' e ')'" :=
     (BOp ESeq 
          (SetVar var1 (UOp Split1 e))
          (BOp ESeq
               (SetVar var2 (UOp Split1 (UOp Split2 e)))
               (BOp ESeq 
                    (SetVar var3 (UOp Split2 (UOp Split2 e)))
                    (UOp (var := String.string) PassCst (ZOp (Cst 0))))))
     (only printing, 
     var1 custom pr_string,
     var2 custom pr_string,
     var3 custom pr_string,
     at level 200).

Notation "'(' 'set' '(' var1 var2 ')' e ')'" :=
     (BOp ESeq 
          (SetVar  var1 (UOp Split1 e))
          (BOp ESeq (SetVar var2 (UOp Split2 e))
                   (UOp (var := String.string)PassCst (ZOp PassCst))))
     (only printing,
      var1 custom pr_string,
      var2 custom pr_string,
      at level 200).
Notation "'(' 'set' var e ')'" :=
     (SetVar {|idxvar:= _; stringvar:= var|} e)
     (only printing, 
     var custom pr_string,
     format "'(' 'set'  var  e ')'").
Notation "'(' 'set' var e ')'" :=
     (SetVar var e)
     (only printing,
     var custom pr_string
     ).

Notation "'(' 'begin' a b .. d e ')'" :=
     (BOp ESeq a (BOp ESeq b .. (BOp ESeq d e) ..))
     (* (Seq a (Seq b .. (Seq d e) ..)) *)
     (only printing,
      format "'(' 'begin' '[v  ' '/' a '/' b '/' .. '/' d '/' e ')' ']'", at level 190).
Notation "'(' 'begin' a b .. d ')'" :=
     (BOp ESeq a (BOp ESeq b .. (BOp ESeq d (UOp PassCst (ZOp (Cst 0)))) ..))
     (* (Seq a (Seq b .. (Seq d e) ..)) *)
     (only printing,
      format "'(' 'begin' '[v  ' '/' a '/' b '/' .. '/' d ')' ']'", at level 190).
Notation "'(' 'begin' a b ')'" :=
     (BOp ESeq a b)
     (only printing,
     format "'(' 'begin' '[v  ' '/' a '/' b ')' ']'",at level 190).
Notation "'(' 'begin' a b ')'" :=
     (Seq a b)
     (only printing,
     format "'(' 'begin' '[v  ' '/' a '/' b ')' ']'",at level 190).

Notation "'(' 'begin' a b .. d e ')'" :=
     (Seq a (Seq b .. (Seq d e) ..))
     (only printing,
      format "'(' 'begin' '[v  ' '/' a '/' b '/' .. '/' d '/' e ')' ']'",at level 190).


(* Notation "'(' 'begin' a b c d ')'" :=
     (BOp ESeq a (BOp ESeq b (BOp ESeq c d)))
     (only printing,
     format "'(' 'begin' '[v' '/' a '/' b '/' c '/' d ')' ']'").
Notation "'(' 'begin' a b c ')'" :=
     (BOp ESeq a (BOp ESeq b c))
     (only printing,
     format "'(' 'begin' '[v' '/' a '/' b '/' c ')' ']'").
Notation "'(' 'begin' a b ')'" :=
     (BOp ESeq a b)
     (only printing,
     format "'(' 'begin' '[v' '/' a '/' b ')' ']'"). *)
Notation "'anonymous_met_arg'" :=
     (Arg)
     (only printing).
Notation "'{' met instance '}'" :=
     (ValMethod  {|idxvar := _; stringvar := instance |} {|idxvar := _; stringvar := met |} (ZOp (Cst N0)))
     (only printing,
     met custom pr_string ,
     instance custom pr_string ,
     format "'{' met  instance '}'").
Notation "'{' met instance e '}'" :=
     (ValMethod {|idxvar := _; stringvar := instance |} {|idxvar := _; stringvar := met |} e)
     (only printing,
     met custom pr_string ,
     instance custom pr_string ,
     format "'{' met  instance  e '}'").
Notation "'(' 'if' c t f ')'" :=
     (Ternary c t f)
     (only printing, format "'(' 'if' '[hv  '  c  t  f ')' ']' ").
Notation "'(' a l ')'" :=
     (UOp (Fn a) l)
     (only printing,
      a custom pr_string,
      format "'(' a  l ')'").
Notation "'pass'" :=
     (Skip)
     (only printing).
Notation "'pass'" :=
     (UOp PassCst (ZOp (Cst 0)))
     (only printing).
Notation "'{' met instance '}'" :=
     (ActionMethod {|idxvar := _; stringvar := instance |} {|idxvar := _; stringvar := met |} (ZOp (Cst 0)))
     (only printing,
     met custom pr_string ,
     instance custom pr_string ,
     format "'{' met  instance '}'").
Notation "'{' met instance e '}'" :=
     (ActionMethod {|idxvar := _; stringvar := instance |} {|idxvar := _; stringvar := met |} e)
     (only printing,
     met custom pr_string ,
     instance custom pr_string ,
     format "'{' met  instance  e '}'").

Notation "'(' 'if' c t f ')'" :=
     (If c t f)
     (only printing, format "'(' 'if' '[hv  '  c  t  f ')' ']' "). 



(* Notation "'(' 'begin' a ')'" :=
     (a)
     (only printing,
     format "'(' 'begin' '[v' '/' a ')' ']'"). *)

Notation "'(' '+' f g ')'" := 
     (BOp Plus f g )
     (only printing,
      format "'(' '+'  f  g ')'").
Notation "'(' '&' f g ')'" :=
     (BOp BwAnd f  g )
     (only printing,
      format "'(' '&'  f  g ')'").
Notation "'(' '|' f g ')'" :=
     (BOp BwOr f g )
     (only printing,
      format "'(' '|'  f  g ')'").
Notation "'(' '!'  g ')'" :=
     (UOp (BwNot 1) g )
     (only printing,
      format "'(' '!'  g ')'").
Notation "'(' '~' sz g ')'" :=
     (UOp (BwNot sz) g )
     (only printing,
      format "'(' '~' sz  g ')'").
Notation "'(' ':' sz g ')'" :=
     (UOp (BwSize sz)  g)
     (only printing,
      format "'(' ':' sz  g ')'").

(* The following notation is dead if we don't materialize the antiquote explicitly *)
(* Notation "'`(' e ')'" := (e) (only printing, format "'`(' '[v' '/' e '/' ']' ')'"). *)

Require reg.
Section Tests.
     Local Definition validtest : nat:=  0.
     Local Definition datatest : nat := 0.
     Local Instance processor_submodules : instances := #| reg.mkReg valid ; reg.mkReg data |#.
     Open Scope N.

     (* Parsing tests: *)
     Goal unit.
     let a := eval cbn in (fjfj_expr (fn 2)) in
     let a := eval cbn in (fjfj_expr 2) in 
     let a := eval cbn in (fjfj_expr (begin 2)) in 
     let a := eval cbn in (fjfj_expr (begin 2 3)) in 
     let a := eval cbn in (value_method () yo) in 
     let a := eval cbn in (value_method (foo bar) (f foo)) in 
     let a := eval cbn in (fjfj_expr (# yo ba foo)) in
     let a := eval cbn in (fjfj_expr (# yo ba foo)) in
     let a := eval cbn in (fjfj_expr 
                    (set (newyo newba ) a)) in 
     let a := eval cbn in (fjfj_expr 
                    (set (newyo newba newfoo) (# yo ba foo))) in 
     let a := eval cbn in (fjfj_expr (begin (+ vo yo))) in 
     let a := eval cbn in (fjfj_expr (begin (+ vo yo) 3 (& 3 2) ew)) in 
     (* let a := eval cbn in (ValMethod (var:= String.string) 0 0 (ZOp (Cst 0))) in    *)
     let a := eval cbn in (fjfj_expr
               ((valid read))
               ) in 
     let a := eval cbn in (fjfj_expr
               (begin 
               (if yo 2 3)
               ((valid read) 43)
               ((valid read))
               (begin bar (+ 32 fsd))
               (begin fd fdi `(id (Var test_str))))) in 
     let a := eval cbn in (fjfj_expr
               (begin 
               (if yo 2 3)
               ((valid read))
               { read valid }
               (begin bar (+ 32 fsd))
               (begin fd fdi `(id (Var test_str))))) in 
     let a := eval cbn in (fjfj_expr (begin (+ vo yo) 3 (& 3 2) ew)) in 
     let a := eval cbn in (fjfj_expr (fn 2)) in 
     let a := eval cbn in (fjfj_expr (begin yoyo)) in 
     let a := eval cbn in (fjfj_expr (begin 1 2 0x100)) in 
     let a := eval cbn in (fjfj_expr (begin 1 2 3 4 5 6)) in 
     let a := eval cbn in (fjfj_expr (begin 1 (:2 (+ 3 2)) 3 4 5 6)) in 
     let a := eval cbn in (fjfj_expr (f 0)) in 
     let a := eval cbn in (fjfj_expr (begin 1 (+ 3 2) (~ 2 (f 0)) 4 5 6)) in 
     let a := eval cbn in (fjfj_expr (begin 1 (+ 3 2) (set flk (begin 1 2)) 4 5 6)) in 
     let a := eval cbn in (fjfj_expr (begin 1 (+ 3 2) (set to (begin 1 2)) 4 5 6)) in 
     let a := eval cbn in (fjfj_expr (begin (if 1 2 pass) (+ 3 2) (set ewi (begin 1 2)) 4 5 6)) in 
     let a := eval cbn in (fjfj_expr (begin (if 1 2 3) ((valid read) 3) 6)) in 
     let a := eval cbn in (fjfj_expr (begin (if 1 `(id (Var test_str)) 3) ((valid read) ) 6)) in 
     let a := eval cbn in (action_method () ((valid write))) in
     let a := eval cbn in (rule ((valid write))) in
     let a := eval cbn in (fjfj_action (begin ((valid write) 3))) in
     let a := eval cbn in (fjfj_action 
                  (begin
                    {write valid 3}
                   (set autobus 1)
                   { write valid 2})) in
     let a := eval cbn in (fjfj_action 
                         (begin 
                         (set (a b) ((valid read))))) in
     let a := eval cbn in (fjfj_action 
                  (if 0 
                   ((valid write)) 
                   ((valid write)))) in
     let a := eval cbn in (fjfj_action 
                  (begin
                   ((valid write) (f 3))
                   (set foo 1)
                   (set bat (if ( | (+ 1 2) 2) 1 3))
                   (if (= foo 1)
                    (set foo 2)
                    pass)
                   ((valid write)))) in
     exact ltac:(idtac "Parsing tests succeeded"; exact tt).

     Qed.
End Tests.
Notation "'primitive_module#(' 'vmet'  v  'amet'  a  ')'" :=
              ( 
      {|
       value_methods := ltac:(let s := list_ident_string v in exact s);
       action_methods := ltac:(let s := list_ident_string a in exact s);
       rule_names := nil
      |} : module (
      {| value_spec := list_to_array unexisting_vmethod v ;
        action_spec :=  list_to_array unexisting_amethod a;
        rule_spec := nil; 
        subrules_spec := nil; |}
     )) (only parsing).

Notation "'primitive_module#(' 'amet'  a  ')'" :=
          ( 
  {|
   value_methods := nil;
   action_methods := ltac:(let s := list_ident_string a in exact s);
   rule_names := nil
  |} : module (
  {| value_spec := list_to_array unexisting_vmethod nil ;
    action_spec :=  list_to_array unexisting_amethod a;
    rule_spec := nil; 
    subrules_spec := nil; |}
 )) (only parsing).

Notation "'primitive_module#(' 'rules' r 'vmet'  v  'amet'  a  ')'" :=
              ( 
      {|
       value_methods := ltac:(let s := list_ident_string v in exact s);
       action_methods := ltac:(let s := list_ident_string a in exact s);
       rule_names := ltac:(let s := list_ident_string r in exact s)
      |} : module (
      {| value_spec := list_to_array unexisting_vmethod v ;
        action_spec :=  list_to_array unexisting_amethod a;
        rule_spec := r;
        subrules_spec := nil ; |}
     )) (only parsing).
Notation "'module#(' 'rules'  r  'vmet'  v  'amet'  a  ')'" :=
              ( 
      {|
       value_methods := ltac:(let s := list_ident_string v in exact s);
       action_methods := ltac:(let s := list_ident_string a in exact s);
       rule_names := ltac:(let s := list_ident_string r in exact s)
      |} : module (build_module 
      code
      (r : list (action (var:=varname)))
      (list_to_array Skip (a : list (action (var:=varname))))
      (list_to_array Abort (v : list (expr (var:=varname)))))) (only parsing).
Notation "'module#('  'vmet'  v  'amet'  a  ')'" :=
              ( 
      {|
       value_methods := ltac:(let s := list_ident_string v in exact s);
       action_methods := ltac:(let s := list_ident_string a in exact s);
       rule_names := nil
      |} : module (build_module 
      code
      (@nil (action (var:=varname))) 
      (list_to_array Skip (a : list (action (var:=varname))))
      (list_to_array Abort (v : list (expr (var:=varname)))))) (only parsing).

Notation "'?' f" := (sem_uninterp f) 
     (f custom pr_string at level 2,           
     only printing, at level 2).
Notation "'?' f" := (sem_uninterp f) (only parsing, at level 2).

Notation "'Focus' 'Value' 'Method:' a" := (FjfjCase (value_method_simulates a)) (at level 2, a custom pr_string, only printing, right associativity).
Notation "'Focus' 'Action' 'Method:' a" := (FjfjCase (action_method_simulates a)) (at level 2, a custom pr_string, only printing, right associativity).