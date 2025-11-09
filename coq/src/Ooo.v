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
Require Nondet.
Require Import egg.Loader.
Require Import Tactics.
Require Import Coq.Sets.Ensembles.
From extructures Require Import ord fmap.

Open Scope N.



(* Developement that gives two generalization of a client (req/resp): 

  Pipelined generalization
  Out-of-order generalization
  
  We prove that the out-of-order generalization, once controlled by a Completion Buffer, is a refinement of the pipelined generalization.
*)
Require Import String.
Definition generic_client (sm : spec_module_t) : module sm := 
  {| value_methods := ["get_result"%string]; 
    action_methods := ["enq"%string;"deq"%string];
    rule_names := []|}.

Module Type GenericReqResp_t. 
  Parameter (T: Type).
  Parameter (req : T -> N -> T).
  Parameter (deq: T -> T).
  Parameter (get_resp : T -> N).

  Inductive buffered_input := 
    | None 
    | Done.
  Record st := 
    { 
      module_state : T;
      inp : buffered_input 
      }.
End GenericReqResp_t.

Module GenericReqResp (p : GenericReqResp_t).
  Import p.
  (* Experimentation with using locally *)
  Definition c : st -> SModule := fun x => *( x )*.
  Coercion c : st >-> SModule.
  Arguments c/.

  Definition enq (arg : N) (st : SModule) (st' : SModule) :=
    exists sm, st = {| module_state := sm; inp := None |} /\
    st'= {| module_state := p.req sm arg ; inp := Done |}.
  Arguments enq /.

  Definition deq (tag : N) (st : SModule) (st' : SModule) := 
     exists sm ,
     st = {| module_state := sm; inp := Done |} /\
     st' = {| module_state := p.deq sm; inp := None |} .
  Arguments deq /.
 
  Definition get_result (_arg : N) (st : SModule) (res : N) := 
     exists sm res ,
     st = {| module_state := sm; inp := Done |} /\
     res = p.get_resp sm.
  Arguments get_result/.

  Definition empty_mod (s : p.T) := 
    {| module_state := s; inp := None |}.

  Global Instance mkGenericReqResp : module _ := 
    primitive_module#(vmet [ get_result ] amet [ enq; deq ]).

End GenericReqResp.

(* Transformer for OOO *)
Module Ooo (gen_m : GenericReqResp_t).
  Module m := GenericReqResp gen_m.
  Import m.
  Definition m := mkGenericReqResp .
  Notation bag_t := {fmap N -> N}.

  Inductive buffered_input := 
    | NoneB 
    | InFlight (tag : N) (input : N).

  Record reordering_machine := 
    { bag : bag_t;
      module_state : SModule;
      inp : buffered_input 
      }.

  (* Experimentation with using locally *)
  Definition c : reordering_machine -> SModule := fun x => *( x )*.
  Coercion c : reordering_machine >-> SModule.
  Arguments c/.

  Definition enq (arg : N) (st : SModule) (st' : SModule) :=
    dlet {tag i} := arg in
    exists b sm sm', st = {| bag := b; module_state := sm; inp := NoneB |} /\
    ((b tag) = None) /\ (* The tag is currently not in use! *) 
    (aget (action_spec m) 0 (* enq method is 0 *) 
           i sm  sm') /\
    st'= {| bag := b; module_state := sm'; inp := InFlight tag i |}.
  Arguments enq /.

  Definition pull_from_module (st : SModule) (st' : SModule) := 
     exists b sm sm' tag i  res, st = {| bag := b; module_state := sm; inp := InFlight tag i |} /\ 
     (b tag = None) /\
     st' = {| bag := setm b tag res; module_state := sm'; inp := NoneB |} /\
     (aget (action_spec m) 1 (* deq method is 1 *) 
           i sm sm') /\
     (aget (value_spec m) 0 (* response method is 0 *) 
           i sm res).
  Arguments pull_from_module/.

  Definition deq (tag : N) (st : SModule) (st' : SModule) := 
     exists b sm res outstanding,
     st = {| bag := b; module_state := sm; inp := outstanding |} /\
     b tag = Some res /\  
     st' = {| bag := remm b tag; module_state := sm; inp := outstanding |} .
  Arguments deq/.
 
  Definition get_result (_arg : N) (st : SModule) (ret : N) := 
     exists b sm tag res outstanding,
     st = {| bag := b ; module_state := sm; inp := outstanding |} /\
     b tag = Some res /\
     ret = {# tag res}.
  Arguments get_result/.

  Definition empty_ooo (s : SModule) := 
    {| bag := emptym;
      module_state := s;
      inp := NoneB |}.

  Global Instance mkOooProcessing : module _ := 
    primitive_module#(rules [pull_from_module] vmet [ get_result ] amet [ enq; deq ]).
End Ooo.

Module CompletionBuffer.

  Inductive rob_entry := 
    | InFlight : forall (tag : N),  rob_entry
    | Completed : forall (tag : N) (output : N), rob_entry.


  (* an ROB typically must record the order in which things were enqueued.
  Each tag is unique *)
  (* Proposition for all tag: si on peut decomposer alors il y a unicité.
    Chaque tag apparait une et une seule fois. *)
  (* Definition single_el := 
    forall l l' tag r r,   *)

  Definition cb_valid tags : Prop:= 
    (* Painful, maybe map + NoDup NoDup *)
    NoDup (List.map (fun tag => match tag with 
                        | InFlight t  => t
                        | Completed t _ => t
                       end) tags).
  Arguments cb_valid tags /.

  Definition tokens_t := { l & cb_valid l}. 

  (* Experimentation with using locally *)
  Definition c : tokens_t -> SModule := fun x => *( x )*.
  Coercion c : tokens_t>-> SModule.
  Arguments c/.

 Fixpoint cb_all_completed tags := 
    match tags with 
    | [] => True 
    | (InFlight t ) :: tail => False
    | (Completed t _ ) :: tail =>  cb_all_completed tail 
    end.
 
  Lemma all_completed_app : forall l r, cb_all_completed (l ++ r) = (cb_all_completed l /\ cb_all_completed r).
    induction l; simpl.
    - intros. 
      rewrite PropLemmas.and_True_l.
      eauto.
    -
      intros.
      destruct a;
       apply PropExtensionality.propositional_extensionality;
        try rewrite IHl;
        tauto.
  Qed.

  Definition available_tag (_arg : N) (st : SModule) (res : N) :=
    exists tag (old_tags: tokens_t), st = old_tags /\
    (* well_formed_tokens old_tags /\ *)
    tag_not_in_tags tag (projT1 old_tags) /\
    res = tag.
  Arguments available_tag /.

  Definition reserve (tag : N) (st : SModule) (st' : SModule) :=
    exists (old_tags: tokens_t) (new_tags: tokens_t),
    st = old_tags /\
    
    tag_not_in_tags tag (projT1 old_tags) /\
    st' = *( newtags )*.
  Arguments reserve/.

  Definition complete (arg : N) (st : SModule) (st' : SModule) :=
    dlet {tag o} := arg in
    exists (tl tr: tokens_t), st = *( tl ++ [InFlight tag ] ++ tr )* /\
    well_formed_tokens ( tl ++ [InFlight tag ] ++ tr ) /\
    st'=  *( tl ++ [Completed tag o] ++ tr )* /\
    well_formed_tokens ( tl ++ [Completed tag o] ++ tr ).
  Arguments complete /.

  Definition drain (_arg : N) (st : SModule) (st' : SModule) := 
     exists (tl: tokens_t) tag o , st = *(  [Completed tag o] ++ tl)* /\
     well_formed_tokens ( [Completed tag o] ++ tl) /\
     st' = tl .
  Arguments drain /.
 
  Definition get_result (_arg : N) (st : SModule) (res : N) := 
     exists (tl: tokens_t) tag o, st = *( [Completed tag o ] ++ tl)* /\
     well_formed_tokens ( [Completed tag o] ++ tl) /\
     res = o.
  Arguments get_result /.

  Global Instance mkCompletionBuffer : module _ := 
    primitive_module#(vmet [get_result; available_tag] amet [reserve; complete; drain]).

(* Invariant: at most one entry per tag *)
End CompletionBuffer.


Module CbAndOoo  (gen_m : GenericReqResp_t) (cb : CompletionBuffer_inT).
    Module CB := CompletionBuffer cb.
    Module Ooo := Ooo gen_m.
    Import CB.
    Import Ooo.

    Local Instance sub_modules : instances :=
      #| 
        mkCompletionBuffer cb;
    (* primitive_module#(vmet [get_result; available_tag] amet [reserve; complete; drain]). *)
        mkOooProcessing ooo_process
    (* primitive_module#(rules [push_to_module; pull_from_module] vmet [ get_result ] amet [ enq; deq ]). *)
      |#.

    Open Scope N.
    Definition enq :=
      (action_method (el)
        (begin 
          (set tag {available_tag cb})
          {reserve cb tag}
          {enq ooo_process (# tag el)})).
    Arguments enq /.
 
    Definition completion_ooo :=
      (rule
        (begin 
          (set (tag output) {get_result ooo_process})
          {deq ooo_process tag}
          {complete cb (# tag output)})).
    Arguments completion_ooo /.
 
  Definition deq := 
    (action_method ()
      (begin 
        {drain cb}
        )).
  Arguments deq /.

  Definition get_result := 
    (value_method ()
      (begin 
        {get_result cb})).
  Arguments get_result /.

  Global Instance mkOooReordered : module _ := 
    module#(rules [completion_ooo] vmet [get_result] amet [enq; deq]).
End CbAndOoo.

Module Pipelined (gen_m : GenericReqResp_t).
    Module m := GenericReqResp gen_m.
    Import m.
    Definition submodule := mkGenericReqResp .
    Arguments submodule /.

    Import FifoSpec.FifoSpec.

    Local Instance sub_modules : instances := 
      #| 
         submodule m;
         mkFifoSpec out
      |#.

    Open Scope N.
 
    Definition completion :=
      (rule
        (begin 
          {deq m}
          {enq out {get_result m}}
          )).
    Arguments completion /.
 
    Definition enq :=
      (action_method (el)
        (begin 
          {enq m el})).
    Arguments enq /.
 
    Definition deq :=
      (rule
        (begin
          {deq out} 
          )).
    Arguments deq /.
 
  Definition get_result := 
    (value_method ()
      (begin 
        {first out})).
  Arguments get_result/.


  Global Instance mkPipelined : module _ := 
    module#(rules [completion] vmet [get_result] amet [enq; deq]).
End Pipelined.

Module Correctness (cb : CompletionBuffer_inT) (gen_m : GenericReqResp_t).
    Module pip := Pipelined gen_m.
    Import pip.
    Module ooo := CbAndOoo gen_m cb .
    Import ooo.

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
    (* Definition yo (x : SModule -> SModule -> Prop) := .
    Arguments yo / x.
    Canonical Structure viewable_ast (x:@action varname) : Viewable_ast  := yo x. 
    Arguments viewable_ast / x.  *)

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

    Inductive related : forall (ist : SModule) (sst : SModule), Prop := 
    | Flushed : forall cb s ist sst, ooo.CB.cb_valid cb ->
        ooo.CB.cb_all_completed cb -> 
        let spec_completed := List.flat_map (fun x => 
        match x with 
        | ooo.CB.Completed tag output =>  [ output ]
        | ooo.CB.InFlight tag => []
        end) cb in
     ist = *[| cb; ooo.Ooo.empty_ooo s |]* -> sst = *[| (state s) ; spec_completed |]*  
      -> related ist sst
    | Completion_ooo : 
      forall (ist_cb : ooo.CB.tokens_t) (ist_ooo : Ooo.reordering_machine) ist
            (sst_s: gen_m.st) (sst_q : list N) sst ist' ,
     ist = *[| ist_cb; ist_ooo |]* ->
     sst = *[| sst_s; sst_q|]* ->
     related ist' sst ->
     (ist --{{ ooo.mkOooReordered completion_ooo }}--> ist') ->
     (* (nth 0 (rule_spec ooo.mkOooReordered) (unexisting_rule) (* completion *)
           ist ist') -> *)
     related ist sst
    | Pull_from_module :
     forall (ist_cb : ooo.CB.tokens_t) (ist_ooo : Ooo.reordering_machine) ist
            (sst_s: gen_m.st) (sst_q : list N) sst ist' ,
     ist = *[| ist_cb; ist_ooo |]* ->
     sst = *[| sst_s; sst_q|]* ->
     related ist' sst ->
     lift_to 1 (nth 0 (nth 1 (subrules_spec ooo.mkOooReordered) []) unexisting_rule)  (* pull to module *)
            ist ist' ->
     related ist sst. 
     Print related_ind.

    Ltac prove_indistinguishable' := 
      remove_ascii;
      prove_indistinguishable.

    Ltac local_cleanup :=
       match goal with 
      | [ H: ?a ++ [?b] = ?c ++ [?d] |- _] =>
        eapply app_inj_tail_iff in H
      end.

    Ltac rw_eq :=
              repeat match goal with 
              | [ H : aget ?a ?b = ?c, H' : aget ?a ?b = ?d |- _] =>
                rewrite H in H'; light_clean_propagate 
              end.
    Ltac propagate_length_default_cst :=
                repeat match goal with 
                | [ H : alength ?A = S ?v, H' : alength ?b = alength ?A |- _] =>
                  rewrite H in H' 
                | [ H : default ?A = *( 0%nat )*, H' : default ?b = default ?A |- _] =>
                  rewrite H in H' 
                end.

    (* Notation "a '-' met '(' x ')' '->' b" :=
          (met (x : N) (a: SModule) (b : SModule)) (at level 200).
    Notation "a '-' met '(' ')' '->' b" :=
          (met 0 (a:SModule) (b:SModule)) (at level 200). *)
    
    (* Machinery to display/input (aget (action_spec m) i 
    as "m.name") *) 

    (* Record Viewable (V T: Type) (f : T -> V) := {
      object_viewed : T;
      view : V
    }. *)


    (* Goal forall ist sst, (ist --{{ mkOooReordered enq {# 1 2 }}}--> sst) -> False.
      intros ist sst.
      print_transitions. *)

    Inductive steps ist ist' := 
    (* Maybe surprisingly, this is not a Prop, this is a Set/Type! *)
    | Completion_ooo' : 
      (ist --{{ mkOooReordered completion_ooo}}--> ist' ) ->
     steps ist ist'
    | Pull_from_module' :
     lift_to 1 (nth 0 (nth 1 (subrules_spec ooo.mkOooReordered) []) unexisting_rule)  (* pull to module *)
            ist ist' ->
     steps ist ist'
    | Deq' :
      forall x,
      (ist --{{mkOooReordered deq x}}--> ist' ) ->
      steps ist ist'
    | Enq' : 
      forall x,
      (ist --{{mkOooReordered enq x}}--> ist' ) ->
      steps ist ist'.

    Definition apply_simul {ist ist' : SModule} (s: steps ist ist') (sst sst' : SModule) : Prop :=
      match s with 
      | Completion_ooo' _ => sst = sst' 
      | Enq' x _ =>
        exists sst'', 
          (sst --{{mkPipelined enq x}}--> sst'') /\ (sst'' --{{mkPipelined completion}}--> sst')
      | Deq' x _ =>
          (sst --{{mkPipelined deq x}}--> sst')
      | Pull_from_module' _ => sst = sst'
      end.

    Lemma remm_setm : (forall {T S} b t k, remm (T:=T) (S:=S) (setm b t k) t = b).
    Admitted.
    Lemma simul_forward : 
      forall ist sst, 
        related ist sst -> 
        forall ist' (s: steps ist ist'),
        exists sst', apply_simul s sst sst' /\
        related ist' sst'.
        intros ist sst H.
        induction H.
        {
          subst.
          intros.
          subst spec_completed.
          destruct s0; simpl in *.
          +
          (* we are in a flushing state and we add a "completion" step
            it should be absurd as the cb should be empty*)
            light_clean_propagate.
            symb_ex_split.
            merge_simpl.
            rewrite ooo.CB.all_completed_app in H0.
            simpl in H0.
            tauto. 
          +
            light_clean_propagate.
            unfold lift_to in *.
            symb_ex_split.
          +
            light_clean_propagate.
            unfold lift_to in *.
            symb_ex_split.
            eexists. split.
            let y := (eexists_st_array 2%nat) in
            eexists y.
            let y := (eexists_st_array 2%nat) in
            eexists y;
            do 3 eexists.
            split; eauto; [wrapped_arrays_equal 2%nat|..]. 
            split; eauto.
            split.
            reconstruct_wpa.
            apply_log_fn 2%nat.
            econstructor.
            4:{  eauto.  }
            inversion H.
            eauto.
            eauto.
            wrapped_arrays_equal 2%nat.
          +
            light_clean_propagate.
            unfold lift_to in *.
            symb_ex_split.
            eexists. split.
            eexists. split.
            let y := (eexists_st_array 2%nat) in
            eexists y.
            let y := (eexists_st_array 2%nat) in
            eexists y;
            do 3 eexists.
            split; eauto; [wrapped_arrays_equal 2%nat|..]. 
            split; eauto.
            split.
            reconstruct_wpa.
            apply_log_fn 2%nat.
            merge_simpl.
            let y := (eexists_st_array 2%nat) in
            eexists y.
            let y := (eexists_st_array 2%nat) in
            eexists y;
            do 3 eexists.
            split. wrapped_arrays_equal 2%nat.
            split; eauto.
            split.
            reconstruct_wpa.
            apply_log_fn 2%nat.
            merge_simpl.
            instantiate (1:= gen_m.get_resp (gen_m.req sm1 x)).
            (* The flushed state is the following: *)
            assert (related 
                  *[| old_tags ++ [CB.Completed tag (gen_m.get_resp (gen_m.req sm1 x))];
                      {| Ooo.bag := emptym;
                      Ooo.module_state :=
                        *(
                        {| gen_m.module_state :=  gen_m.deq (gen_m.req sm1 x);
                         gen_m.inp := gen_m.None |}
                        )*;
                      Ooo.inp := Ooo.NoneB |} |]*
                  *[| {| gen_m.module_state := gen_m.deq (gen_m.req sm1 x);
                         gen_m.inp := gen_m.None |};
                      flat_map (fun x0 : CB.rob_entry =>
                         match x0 with
                         | CB.InFlight _ => []
                         | CB.Completed _ output => [output]
                         end) old_tags ++ [gen_m.get_resp (gen_m.req sm1 x)] |]*).
            pose  *(
            {|
              gen_m.module_state := gen_m.deq (gen_m.req sm1 x);
              gen_m.inp := gen_m.None
            |} )* as yo.
            econstructor.
            3:{
            wrapped_arrays_equal 2%nat.
            instantiate (1:= yo).
            eauto.
            }
            simpl.
            rewrite map_app.
            simpl.
            match goal with 
            | [ |- NoDup ?l1]=>
            rewrite <- rev_involutive with (l:=l1)
            end.
            eapply NoDup_rev.
            rewrite rev_app_distr.
            simpl.
            eapply NoDup_cons_iff.
            split;[ | eapply NoDup_rev; eauto].
            intro.
            eapply  in_rev in H1.
            eauto.
            rewrite ooo.CB.all_completed_app.
            simpl; tauto.
            wrapped_arrays_equal 2%nat.
            rewrite flat_map_app.
            simpl.
            eauto.

            eapply Completion_ooo; simpl.
            wrapped_arrays_equal 2%nat.
            eauto.
            2:{
              merge_simpl.
              let y := (eexists_st_array 2%nat) in
              eexists y.
              let y := (eexists_st_array 2%nat) in
              eexists y;
              do 3 eexists.
              split; eauto; [wrapped_arrays_equal 2%nat|..]. 
              split; eauto.
              split.
              reconstruct_wpa.

            2:{ 
              (* absurd *)
               }
            
            (* eauto. *)
            2:{ apply_log_fn 2%nat.
            (* Trivial but painful administrative stuff *)
            merge_simpl.
            intros.
            repeat eexists.
            merge_simpl.
            intros.
            repeat eexists.
            2:{ 
              simpl.
              instantiate (3:= emptym).
              rewrite remm_setm.
              eauto.
            }
            rewrite setmE.
            rewrite eqtype.eq_refl.
            eauto.
            }
            rewrite setmE.
            rewrite eqtype.eq_refl.
            eauto.
            simpl.
            }

        
            eapply Pull_from_module; simpl.
            eauto.
            eauto.
            2:{
              unfold lift_to.
              eexists. split. eauto.
              eexists *(_)*.
              split.
              wrapped_arrays_equal 2%nat.
              rewrite HA5.
              simpl.
              rewrite HB1.
              merge_simpl.
              eauto.
              rewrite HA5.
              simpl.
              eauto.
              rewrite HA5.
              simpl.
              egg_repeat.
              rewrite HA5.
              simpl.
              egg_repeat.
              rm_existentials.
              split.
              exact HB.
              split.
              eauto.
              split.
              eexists.
              split; eauto.
            }
            eapply Completion_ooo; simpl.
            eauto.
            wrapped_arrays_equal 2%nat.
            eapply H1.
            merge_simpl.
            let y := (eexists_st_array 2%nat) in
            eexists y.
            let y := (eexists_st_array 2%nat) in
            eexists y;
            do 3 eexists.
            split; eauto; [wrapped_arrays_equal 2%nat|..]. 
            split; eauto.
            split.
            reconstruct_wpa.

            2:{ 
              (* absurd *)
               }
            
            (* eauto. *)
            2:{ apply_log_fn 2%nat.
            (* Trivial but painful administrative stuff *)
            merge_simpl.
            intros.
            repeat eexists.
            merge_simpl.
            intros.
            repeat eexists.
            2:{ 
              simpl.
              instantiate (3:= emptym).
              rewrite remm_setm.
              eauto.
            }
            rewrite setmE.
            rewrite eqtype.eq_refl.
            eauto.
            }
            rewrite setmE.
            rewrite eqtype.eq_refl.
            eauto.
            simpl.
            
        }
        {
          simpl in *.
          light_clean_propagate.
          symb_ex_split.
          merge_simpl.
          destruct s; simpl in *.
          +
            light_clean_propagate.
            symb_ex_split.
            merge_simpl.

            assert (tag = tag0 \/ tag <> tag0) by lia.
            destruct H.
            {
            subst.


            }
            assert (exists ist'',  ( *(nxt_st)* --{{ mkOooReordered completion_ooo}}--> ist'' ) /\
                      ( *(nxt_st0)* --{{ mkOooReordered completion_ooo}}--> ist'' )) as diagram_commutes.
            (* There are 2 cases! Either it is the same, or 2 different tags being completed  *)
            (* b and b0 are equal except maybe at tag *)
            subst.
            eexists.
            split.
            2:{ 
              simpl.
              let y := (eexists_st_array 2%nat) in
              eexists y.
              let y := (eexists_st_array 2%nat) in
              eexists y;
              do 3 eexists.
              split; eauto; [wrapped_arrays_equal 2%nat|..]. 
              split; eauto.
              split.
              (* Very painful representation *)
              (* tag0 has been completed *)
              reconstruct_wpa.
            }
              rewrite H2 in H6.
              eauto.
            (* First we use IHrelated: *)
            pose proof (Completion_ooo' ).
            simpl in X.
            specialize (IHrelated _ (Completion_ooo'))
            eexists.
            split.
            2:{
              eapply Completion_ooo.
              3:{ eauto. }
             }


        }

     
          Admitted.
        (* }



        }
        3:{ }
        - light_clean_propagate. simpl in *.
          indistinguishable (spec_of mkOooReordered) (spec_of mkPipelined) ist sst.
          simpl; intros; intuition trivial.
          simpl_in H.
          induction H. *)
    Lemma simul_implies_indistinguishable : 
      forall ist sst, related ist sst -> 
          indistinguishable (spec_of mkOooReordered) (spec_of mkPipelined) ist sst.
          simpl; intros; intuition trivial.
          simpl_in H.
          induction H.
          -
            prove_indistinguishable'; clean_propagate; simpl; symb_ex_split.
            + 
              let y := (eexists_st_array 2%nat) in
              eexists y; do 2 eexists.
              split; eauto; [wrapped_arrays_equal 2%nat|..]. 
              clean_propagate.
              subst spec_completed.
              reconstruct_step.
            + 
              merge_simpl.
              eexists; let y := (eexists_st_array 2%nat) in
              eexists y;
              let y := (eexists_st_array 2%nat) in
              eexists y;
              do 3 eexists.
              split; eauto; [wrapped_arrays_equal 2%nat|..]. 
              split; eauto.
              subst spec_completed.
              split.
              reconstruct_wpa.
              apply_log_fn 2%nat.
            +
              merge_simpl.
              eexists; let y := (eexists_st_array 2%nat) in
              eexists y;
              let y := (eexists_st_array 2%nat) in
              eexists y;
              do 3 eexists.
              split; eauto; [wrapped_arrays_equal 2%nat|..]. 
              split; eauto.
              subst spec_completed.
              split.
              reconstruct_wpa.
              eauto.
              apply_log_fn 2%nat.
        -
           simpl in *|-.
           prove_indistinguishable'.
           + 
              light_clean_propagate.
              symb_ex_split.
              light_clean_propagate.
              merge_simpl.
              light_clean_propagate.
              unfold indistinguishable in IHrelated.
              destruct IHrelated.
              eapply H with (method_id := 0%nat).
              simpl.
              let y := (eexists_st_array 2%nat) in
              eexists y; do 2 eexists.
              split; eauto.
              wrapped_arrays_equal 2%nat; solve [prove_outside nxt_st; eauto].
              simpl.
              destruct tl1; simpl in *.
              inversion H5.
              inversion H5.
              subst.
              reconstruct_step.
           + 
               (* TODO: streamline the 3 sets:  *)
              light_clean_propagate.
              symb_ex_split.
              merge_simpl.
              propagate_length_default_cst.
              unfold indistinguishable in IHrelated.
              destruct IHrelated.
              eapply H3 with (new_st_i := *( _ )*) (method_id := 0%nat).
              simpl.
              eexists; let y := (eexists_st_array 2%nat) in
              eexists y;
              do 3 eexists.
              split.
              eauto.
              split.
              eauto.
              split; eauto.
              reconstruct_wpa.
              eauto.
              { (* TODO bring that in global tactic *)
                rewrite H4 in *.
                rewrite CB.tag_not_in_tags_app in *.
                instantiate (1:= tag0).
                simpl in *.
                tauto.
              }
              eauto.
              { rewrite H4 in *.
                rewrite CB.tag_not_in_tags_app in *.
                tauto.
              }
              eauto.
              merge_simpl.
              {
                intros.
                eapply HA8.
                instantiate (1:= x).
                rewrite H2.
                econstructor.
                eauto.
              }
              apply_log_fn 2%nat.
              intros.
              rewrite HB0.
              repeat eexists; eauto.
              { rewrite H4 in *.
                rewrite CB.tag_not_in_tags_app in *.
                tauto.
              }
              2:{ intros. lia. }
              intros.
              repeat eexists; eauto.
              merge_simpl.
              {
                intros.
                eapply HA8.
                instantiate (1:= x).
                rewrite H2.
                econstructor.
                eauto.
              }
           + 
               (* TODO: streamline the 3 sets:  *)
              light_clean_propagate.
              symb_ex_split.
              merge_simpl.
              propagate_length_default_cst.
              unfold indistinguishable in IHrelated.
              destruct IHrelated.
              rewrite H3 in H6.
              destruct tl2.
              { inversion H6. } 
              {
                simpl in H6.
                inversion H6.
                subst.
                eapply H5 with (new_st_i := *( _ )*) (method_id := 1%nat).
                simpl.
                eexists; let y := (eexists_st_array 2%nat) in
                eexists y;
                do 3 eexists.
                split.
                eauto.
                split.
                eauto.
                split; eauto.
                reconstruct_wpa.
                exact HB0.
                apply_log_fn 2%nat.
                { intros. lia. }
              }
      -
           identify_modules.
           simpl in *|-.
           prove_indistinguishable'.
           + 
              light_clean_propagate.
              symb_ex_split.
              unfold lift_to in *.
              light_clean_propagate.
              merge_simpl.
              destruct IHrelated.
              eapply H with (method_id := 0%nat).
              simpl.
              let y := (eexists_st_array 2%nat) in
              eexists y; do 2 eexists.
              split; eauto.
              wrapped_arrays_equal 2%nat; solve [prove_outside nxt_st; eauto].
              simpl.
              reconstruct_step.
           + 
               (* TODO: streamline the 3 sets:  *)
              light_clean_propagate.
              symb_ex_split.
              unfold lift_to in *.
              light_clean_propagate.
              merge_simpl.
              {
                simpl in *.
                inversion HA10.
                light_clean_propagate.
                apply (f_equal Ooo.inp) in H.
                simpl_in H.
                inversion H.
              }
           + 
              light_clean_propagate.
              unfold lift_to in *.
              symb_ex_split.
              merge_simpl.
              unfold indistinguishable in IHrelated.
              destruct IHrelated.
              eapply H0 with (new_st_i := *( _ )*) (method_id := 1%nat).
              simpl.
              eexists; let y := (eexists_st_array 2%nat) in
              eexists y;
              do 3 eexists.
              split.
              eauto.
              split.
              eauto.
              split; eauto.
              simpl.
              reconstruct_wpa.
              simpl.
              apply_log_fn 2%nat.
              {
                (* TODO idea: add a way to fail if one does not find the Focus Action Method *)
              (* do 4 eexists.
              {
                split; eauto.
              }
              }
              { *)
              intros.
              destruct i.
              eauto.
              destruct i; eauto.
              }
              {
              intros.
              destruct i.
              eauto.
              destruct i; eauto.
              }
    Time Qed.


Theorem correct' : refines (spec_of mkOooReordered) (spec_of mkPipelined)  related.
  prove_refinement.
  {



(* 
(* Archival of an experimentation that ended up being not so useful when in a parametric setup *)

  Notation "'{->' met instance '}'" :=
          match (true : __Ltac2_MarkedMet _) with
          | met => ltac:(
                        let s_met := constr:(ltac:(serialize_met_in_context)) in
                         let mmet_idx := eval cbv in (index_of s_met (value_methods (sm:= instance)) O) in 
                         lazymatch mmet_idx with 
                         | Some ?met_idx => idtac met_idx; exact (aget (value_spec instance) met_idx)
                         | _ => idtac "no method found"
                         end)
          end
     (met ident,
      instance global,
      only parsing).

  Notation "'{' met instance '}'" :=
          match (true : __Ltac2_MarkedMet _) with
          | met => ltac:(let s_met := constr:(ltac:(serialize_met_in_context)) in
                         let mmet_idx := eval cbv in (index_of s_met (action_methods (sm:= instance)) O) in 
                         lazymatch mmet_idx with 
                         | Some ?met_idx => idtac met_idx; exact (aget (action_spec instance) met_idx)
                         | _ => idtac "no method found"
                         end)
          end
     (met ident,
      instance global,
      only parsing).

*)

(* 
    Ltac post_rule_state n:= 
      rm_existentials; 
      split;[ wrapped_arrays_equal n| ].

  Ltac step_method_spec := 
      eexists;
      let y := (eexists_st_array 16%nat) in
      eexists y;
      do 3 eexists;
      split;[eauto | ];
      split;[ eauto | ];
      split;
      [repeat reconstruct; repeat reconstruct_wpa|
      apply_log_fn 16%nat].
 

Ltac pre_method related_i_s indistinguishable_i_s := 
      simpl in related_i_s;
      light_clean_propagate;
      clear indistinguishable_i_s;
      simpl in *|-;
      min_straight_line;
      repeat  simpl_applylog;
      min_straight_line;
      simpl in * |-;
      repeat clean_arith;
      light_clean_propagate;
      do 2 eexists;
      split;[ step_method_spec | split;[ eapply existSR_done| ]].



  Ltac method_indistinguishable :=
    light_clean_propagate; min_straight_line;
    repeat match goal with
          | H: if ?a then wpa _ _ _ _ _ _ _ _ _ _ 
              else wpa _ _ _ _ _ _ _ _ _ _ 
              |- _ => destruct a eqn:?
            end;
      min_straight_line;
    repeat match goal with
          | H:apply_alog _ _ _ _ |- _ => clear H
            end;
    repeat clean_arith;
    repeat
    lazymatch goal with
    | |- apply_alog _ _ _ _ =>
      let y := eexists_st_array 16%nat in
      instantiate ( 1 := y ); apply_log_fn 16%nat
    | |- wpa _ _ _ _ _ _ _ _ _ _  => 
      reconstruct; simpl; eauto
    | _ => 
    econstructor; simpl
    end;
    min_straight_line; simpl;
    try blast_arith;
    characterize_arrays; unfold state_t in *;
    simpl;
    eapply f_equal; PropLemmas.pose_lemmas;
    time "Indistiguishable searchvar" egg_eexists 4; egg_repeat. *)

(* 
  Ltac substep k:= 
        simpl; unfold lift_to;
   let y := eexists_st_array k in
	eexists y; split;
  [ apply f_equal; reflexivity | ]; simpl;
  eexists;
  split; [reflexivity | ]. *)
 