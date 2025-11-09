Require Import Lia.
Require Import String.
Require Import NArith.

Require ZArith.

Require Import LangFjfj2.
Require Import Indexification.
Require Import FjfjParsing.
Require Import Ltac2.Ltac2.
Require Import List.

Local Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Set Default Proof Mode "Classic".

Ltac dest i k := try (destruct i; simpl).
Ltac split_i_upto i n :=
  let t := dest i in
  repeat_tac t n.

Ltac array_case_indexes i n :=
  (* here for backward compatibility *)
  split_i_upto i n.
Ltac eexists_list n t :=
          match n with 
          | O => open_constr:(@nil t)
          | S ?n => open_constr:(_:ltac:(let r := eexists_list n t in exact r))
          end.
Ltac eexists_smodule_list n :=
  match n with 
  | O => open_constr:(@nil SModule)
  | S ?n => open_constr:((generic_embed _)::ltac:(let r := eexists_smodule_list n  in exact r) )
  end.

Ltac eexists_st_array n :=
  let r := eexists_smodule_list n in 
  open_constr:(list_to_array (generic_embed 0%nat) r).

(*** Tactic to invert all the steps corresponding to rules or action method in
the context, unless such a step is a conditional ****) 
Ltac min_straight_line :=
  repeat ((first [ straight_line_step | straight_line_wpa ])).

(*** The eggserver is unhappy with strings, it creates lots of vertices in the
graph that significantly slow down the search. This tactic abstract over concrete strings.
***)
Ltac remove_ascii := 
repeat match goal with 
| [ H: context [(? ?a)] |- _ ] =>
  let fn := fresh "fn" in
  remember (? a) as fn eqn:Heqt; clear Heqt
end.

(*** Tactics to handle when one has inverted a step in the implementation in the context, and one
wants to do a _corresponding_ a step in the specification.
_repeat econstructor_ is not enough because of branches. In case of branches,
this tactic pick the side of the branch that is immediately provable because the
value of the condition is already in context.
***)
Ltac reconstruct_step :=
            repeat (lazymatch goal with
            | [ |- step _ _ _ _ _ (BOp ESeq _ _) _ _ _ ] => eapply DBinop' with (binop := ESeq)
            | [ |- @step ?uninterp ?st ?called_args ?ModuleTable ?B ?V (Ternary ?c _ _) _ _ _ ] => 
                let cond := fresh "cond" in
                eassert (@step uninterp st called_args ModuleTable B V c _ _ _) as cond;
                [reconstruct_step|..]; 
                [.. | 
                match type of cond with 
                | step _ _ _ _ _ _ _ _ ?res => 
                  let res := eval simpl in res in 
                  (* idtac "reconstructing conditional:" res; *)
                  let myeq:= constr:( (N.modulo res 2%N) ) in
                  (* idtac  myeq; *)
                  match goal with 
                  | [ H : myeq = 1%N |- _ ] =>
                    (* idtac "case true" ; *)
                    eapply DTernaryT;simpl
                  | [ H : myeq  <> 1%N |- _ ] =>
                    (* idtac "case false" ; *)
                    eapply DTernaryF;simpl
                  end
                end
                (*  *)
                ] 
            | |- step ?st ?called_args ?ModuleTable ?B ?V _  _ _ _  => not_evar st; econstructor
            end; simpl).

Ltac reconstruct := 
      repeat (lazymatch goal with 
      | |- @wpa ?uninterp ?st ?called_args ?ModuleTable ?B _ ?V (If ?c _ (Expr Abort)) _ _ _  =>
              eapply DIft
      | |- @wpa ?uninterp ?st ?called_args ?ModuleTable ?B _ ?V (If ?c _ _) _ _ _  =>
          let cond := fresh "cond" in
          eassert (@step uninterp st called_args ModuleTable B V c _ _ _) as cond;
          [reconstruct_step|..]; 
          [.. | 
          match type of cond with 
          | step _ _ _ _ _ _ _ _ ?res => 
            let res := eval simpl in res in 
            (* idtac "reconstructing conditional:" res; *)
            let myeq:= constr:( (N.modulo res 2%N) ) in
            (* idtac  myeq; *)
            match goal with 
            | [ H : myeq = 1%N |- _ ] =>
              (* idtac "case true" ; *)
              eapply DIft;simpl
            | [ H : myeq  <> 1%N |- _ ] =>
              (* idtac "case false" ; *)
              eapply DIff;simpl
            end
          end
          (*  *)
          ] 
          (* If cond *)
   | |- wpa ?st ?called_args ?ModuleTable ?B _ ?V _ _ _ _ => econstructor; simpl
   | |- step ?st ?called_args ?ModuleTable ?B _ ?V _ _ _ => reconstruct_step 
      end).

Ltac reconstruct_wpa := 
      repeat (lazymatch goal with 
      | |- @wpa ?uninterp ?st ?called_args ?ModuleTable ?B _ ?V (If ?c _ _) _ _ _  =>
          let cond := fresh "cond" in
          eassert (@step uninterp st called_args ModuleTable B V c _ _ _) as cond;
          [reconstruct_step|..]; 
          [.. | 
          match type of cond with 
          | step _ _ _ _ _ _ _ _ ?res => 
            let res := eval simpl in res in 
            (* idtac "reconstructing conditional:" res; *)
            let myeq:= constr:( (N.modulo res 2%N) ) in
            (* idtac  myeq; *)
            match goal with 
            | [ H : myeq = 1%N |- _ ] =>
              (* idtac "case true" ; *)
              eapply DIft;simpl
            | [ H : myeq  <> 1%N |- _ ] =>
              (* idtac "case false" ; *)
              eapply DIff;simpl
            | [ H : myeq  = 0%N |- _ ] =>
              (* idtac "case false" ; *)
              eapply DIff;simpl
            end
          end
          (*  *)
          ] 
          (* If cond *)
      | |- wpa ?st ?called_args ?ModuleTable ?B _ ?V  _ _ _ _  => not_evar st; econstructor; simpl
      end).

(*** Tactic to simplify the mangling between multiple arguments
methods/functions visible to users, and single argument to functions and methods
in the semantics***) 
Ltac merge_simpl := 
      repeat (try rewrite !merge_split1 in *;
      try rewrite !merge_split2 in *;
      try rewrite !merge_of_split in *).

(*** Extensional characterization of arrays: ***)

Ltac assert_kth_el eq opaque transparent k := 
    let reduced := eval simpl in (aget transparent k) in 
    assert (aget opaque k = reduced ) by (rewrite eq; try reflexivity).

Ltac array_case_charact eq opaque transparent n :=
  let t := assert_kth_el eq opaque transparent in
  repeat_tac t n.

(* Toplevel tactics to characterize all the arrays in the context in term of a
collection of properties describing the elements one by one*) 
Ltac characterize_arrays := 
        cbv [rm_view] in *;
        repeat match goal with 
        | [H : context[Build_array ?l ?d ?v] |- _] => 
          let eq := fresh "eq_array" in
          let el:= fresh "array_modules" in
          remember (Build_array l d v) as el eqn:eq in H;
          assert (alength el = l) by (rewrite eq; reflexivity);
          assert (default el = d) by (rewrite eq; reflexivity) ;
          array_case_charact eq el (Build_array l d v) l;
          (* Repeat tactics for i =0%nat to l: get *)
          clear eq
        end.

Require Import egg.Loader.

(*** Some tactics that together can discharge simple equality goals about arrays:

    alength a = 2
    aget a 0 = 12 
    aget a 1 = 42 
    ========= 
    a = [| 12; 42 |]
*)
Ltac custom_eq_array n :=
    (* auxiliary tactic to do the bulk work 
    *)
  eapply ext_array; simpl; eauto;
  unfold aget in *;
  (* Handle last *)
  assert (n >= n)%nat by lia; 
  match goal with 
  | [ |- forall x, _] => 
    let rn := fresh x in
    try (rename x into rn);
    let newn := eval simpl in (1+n)%nat in 
    split_i_upto x newn; try lia; eauto; 
    egg_repeat_n 4;
    (* Handle out of bound*)
    try (assert ( newn + x>= n)%nat by lia;
      egg_repeat_n 3);
    try (simpl in *;
    let n := fresh "tmp" in 
    match goal with
    | [ |- _ = ?a ] => set a as n
    end;
    (* (time "Egg Elim" (egg_elim 4 values)); subst n; cbv beta); *)
    ((egg_elim 4 values)); subst n; cbv beta);
    eauto;
    (* prepare handling submodule :*)
    try lia 
    end.


Ltac prove_outside st := 
  (* tactic to discharge the out-of-bound side-conditions *)
      match goal with 
      | [ H : forall x, (x >= _)%nat -> values st _ = default st |- _] => 
        erewrite H; try lia
      end.

(* Ltac arrays_equal n := 
  (* Top level tactic to prove arrays equality *)
        custom_eq_array n; 
        [ .. | match goal with 
                | |-  values ?nxt_st _ = match ?x with _ => _ end  => 
                prove_outside nxt_st;
                destruct x; eauto
                end ]. *)

Ltac wrapped_arrays_equal n := 
  (* Tactic to prove equality between wrapped arrays *)
        apply f_equal; unfold aget in *;
        custom_eq_array n.


Ltac assert_related pf :=
  (* Small helper when we want to prove A /\ B and that we have a proof pf : A -> B. 
  Thet tactic simply assert A and then use pf *)
    match goal with 
    | [ |- ?a /\ ?b ] => 
      assert a; [.. | split; eauto; apply pf; eauto ] 
    end.

(* When performing simulation proof, one at some point needs to prove a goal:
....
======
apply_log ... <| ?a ; ... ; ?b |>

That kind of goal states that we can update the modules of the specification, and constraint the new state submodule by submodule, 
the new values should be free evars in the goal, organized in nested arrays shaped like the hierarchy of the design

This tactics was designed to be run after everything has been flattened in the context (hypothesis have been inverted completely, etc...)
*)
Ltac apply_log_fn n := 
    split;[
    match goal with 
    | |- forall i, _ => array_case_indexes i n%nat; eauto
    end | 
    simpl; 
    (* This simpl is important to avoid eager unification because of length/default equations *)
    split; eauto; 
    match goal with 
    | |- forall x, _ => let nn := eval simpl in (2+n)%nat in 
                         array_case_indexes  x nn; try lia; eauto
    end ].


Notation "'subst!' yy 'for' xx 'in' f" := (match yy with xx => f end) (at level 10).

Ltac app_beta f x :=
  match f with
  | (fun yyy => ?F) => constr:(subst! x for yyy in F)
  end.

Ltac prettify_arrays x := 
  (* let _ := match O with _ => idtac "Start call" x end in *)
  let ot := type of x in
  let A := fresh "ctx" in
  (* let _ := match O with _ => idtac "tc" ot end in *)
  let res := 
    lazymatch x with 
    | context A [ Build_array ?a *( 0%nat )* ?v ] =>
        let ds := constr:(Build_array a *( 0%nat )* v) in
        let foo := context A [rm_view (add_view _ (Build_array a *( 0%nat )* v))] in
        (* let _ := match O with _ => idtac "Found no binder ctx" A "array" ds "ctxapplied" foo end in *)
        foo
    | context[ Build_array _ *( 0%nat )* _ ] =>
        (* Try to find it!  *)
        lazymatch x with 
        | Build_array_with_view ?V ?l ?d ?v ?view => 
            (* let _ := match O with _ => idtac "array_view" end in *)
            let vview := prettify_arrays view in
            constr:(Build_array_with_view V l d v vview)
        | forall (b : ?t), @?f x => 
          constr:(forall (b :t), ltac:(
            let t := app_beta f b in
            idtac t;
            let vb := prettify_arrays t in exact vb))
        | (fun (b : ?t) => @?f b) => 
          (* let y := fresh "foo" in *)
          constr:(fun (b : t) => 
                  ltac:(
                    (* idtac "GoDown"; *)
                      let t' := app_beta f b in
                      (* idtac "Progress" t'; *)
                      let vb := prettify_arrays t' in 
                      (* idtac "Success" vb; *)
                      exact vb))
        | ?a ?b => 
            let va := prettify_arrays a in
            let vb := prettify_arrays b in
            constr:(va vb)
        | ?a => 
          (* We tried our best *)
          constr:(ltac:(
            (* idtac "Neither app nor foraall" a;  *)
          exact a))
        end
    | ?a => constr:(a)
    end in
  let nt := type of res in 
  (* let __ := match O with _ => tryif constr_eq nt ot then idtac "Ok" else  fail 1000 nt ot end in *)
  res.


Ltac print_arrays := 
    repeat multimatch goal with 
    | [H : context A [Build_array ?a ?d ?v ] |- _ ] =>
         let eq := fresh "eq_array" in
          let el:= fresh "array_modules" in
          let t :=  context A [Build_array a d v] in 
          let new := prettify_arrays t in
          change t with new in H;
          cbv [add_view] in H; simpl in H 
    end;
    repeat match goal with 
    | |- ?g  =>
         let eq := fresh "eq_array" in
          let el:= fresh "array_modules" in
          let t := g in 
          (* idtac t; *)
          let new := prettify_arrays t in
          (* idtac "new" new; *)
          change t with new;
          cbv [add_view] ; simpl 
    end.



Ltac prove_indistinguishable' := 
  (* Wrapper around our standard prove_indistinguishable tactic, but abstract over all the strings in the context,
  which helps the Coquetier by reducing significantly the size of the egraph. *)
   remove_ascii;
   prove_indistinguishable; print_arrays.


Ltac rm_existentials := 
  repeat match goal with 
    | [ |- exists t, _] => eexists 
  end.

Ltac symb_ex_met :=
              light_clean_propagate;
              repeat min_straight_line; light_clean_propagate; repeat clean_arith.

Ltac case_step_if H :=
  eapply inv_DTernary in H; simpl in H; light_clean_propagate.

Ltac prove_state_simulation :=
  intros;identify_modules; prove_indistinguishable'; simpl in *; light_clean_propagate; print_arrays.
Ltac symb_ex_split := 
  repeat (match goal with 
  | [ H :  wpa _ _ _ _ _ _ _ _ _ _  |- _ ] =>
    progress symb_ex_met
  | [H : step _ _ _ _ _ _ _ _ _ |-_ ] => 
    progress symb_ex_met
  | [H : if (?x =? ?y)%N then wpa _ _ _ _ _ _ _ _ _ _ else wpa _ _ _ _ _ _ _ _ _ _ |- _] =>
    destruct (x =? y)%N eqn:?
  | [H : if (?x =? ?y)%N then step _ _ _ _ _ _ _ _ _ else step _ _ _ _ _ _ _ _ _|- _] =>
    destruct (x =? y)%N eqn:?
  | _ => progress (light_clean_propagate; simpl in *|-; repeat clean_arith; try blast_arith)
  end); simpl; repeat simpl_applylog; print_arrays.

Ltac has_var v := match v with 
| context[?a] => is_var a
end.

Ltac arithmetic_hammer := 
    autorewrite with fwd_rewrites in *; eauto; blast_arith.

    
Ltac replay_method_with_no_rules ϕ_implies_state_simul := 
  simpl;
  do 2 eexists;
  split; eauto 6;
  split; [ eapply existSR_done |.. ];
  assert_related ϕ_implies_state_simul;
  merge_simpl; print_arrays.

Notation "'update' st 'with' log 'gives'  nxt_st":= (apply_alog _ st log nxt_st) (only printing, at level 200).

(* simpl in H with a easy-to-check proof term. *)
Ltac simpl_in H :=
    let type_of_H := type of H in
    let type_of_H' := eval simpl in type_of_H in
    lazymatch goal with
    | |- ?Goal =>
        revert H;
        refine ((_ : type_of_H' -> Goal) : type_of_H -> Goal);
        intros H
    end. 
  Ltac prove_post :=
        match goal with 
        | [ H : ?a |- (?a /\ ?b) \/ (?c /\ ?d)] =>
          left; split; [exact H|..]
        | [ H : ?c |- (?a /\ ?b) \/ (?c /\ ?d)] =>
          right; split; [exact H | ..]
        | [ |- ?a /\ ?b ] => split
        | _ => solve [repeat eexists]
        | [ |- exists x , ?a /\ ?b] => 
          eexists; split 
        | [ |- exists x , ?a] => 
          eexists
        | [ |- apply_alog _ ?st ?log ?nxt_st] =>
          let n := eval cbv in (alength st) in 
          apply_log_fn n
        end.




  (* Tactics to use Egg to do evar inference. The top-level tactic that should be used is [add_subterms_goal] *)
  Ltac add_term t :=
      (* idtac t; *)
      let tt := type of t in
      match tt with 
      | forall x, ?a => 
          match t with 
          | ?f ?x => add_term f; add_term x
          | ?a => idtac
          end
      | Type => 
          idtac
      | Set => 
          idtac
      | _ => 
          pose proof (eq_refl t) 
      end.

  Ltac keepterms t := 
      (* Useful tactic to remember *)
      match t with
  | ?a ?b =>
      tryif (assert_fails (has_evar a)) then 
      (tryif (assert_fails (has_evar b)) then add_term (a b)else (add_term ( a); keepterms b))
          else 
      (keepterms a; keepterms b)
  | ?a => tryif (assert_fails (has_evar a)) then (add_term ( a)) else idtac
  end.

  Ltac add_subterms_goal := match goal with 
      | |- ?g => keepterms g 
      end.

  Ltac solve_easy_evars := 
    PropLemmas.pose_lemmas; rm_existentials; add_subterms_goal; egg_eexists 4; egg_repeat.

  Ltac solve_egg := PropLemmas.pose_lemmas; egg_repeat.



  (* Tactic of a doubtful use, destroyH == 1%nat => destroyt the equality between functions *)
  Ltac extract_equality H n destroyH:= 
    match n with 
    | 0%nat => 
        match type of H with 
        | (?f : nat -> _) = ?g  =>
          let name := fresh "fnEq" H "_" in 
          pose proof (FunctionalExtensionality.equal_f H n) as name; 
          simpl in name;
          match destroyH with 
          | 1%nat => clear H
          | _ => idtac
          end
        end
    | S ?p => 
      match type of H with 
      | (?f : nat -> ?x) = ?g  =>
        let name := fresh "fnEq" H "_" in 
        pose proof (FunctionalExtensionality.equal_f H n) as name;
        simpl in name;
        extract_equality H p destroyH
      end
    end.
