Require Import NArith.
Require Import Lia.

Require Import String.
Require Import NArith.

Require ZArith.

Require Import LangFjfj2.
Require Import Indexification.
Require Import FjfjParsing.
Require Import List.
Require Import ArithFacts.

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
  (* Definition c : st -> SModule := fun x => *( x )*.
  Coercion c : st >-> SModule.
  Arguments c/. *)

  Definition enq' sm arg :=
    {| module_state := p.req sm arg ; inp := Done |}.
  Arguments enq' /.

  Definition enq (arg : N) (st : SModule) (st' : SModule) :=
    exists sm, st = *({| module_state := sm; inp := None |})* /\
    st'= *(enq' sm arg)*.
  Arguments enq /.

  Definition deq (tag : N) (st : SModule) (st' : SModule) := 
     exists sm ,
     st = *({| module_state := sm; inp := Done |})* /\
     st' = *({| module_state := p.deq sm; inp := None |})* .
  Arguments deq /.
 
  Definition get_result (_arg : N) (st : SModule) (res : N) := 
     exists sm,
     st = *({| module_state := sm; inp := Done |})* /\
     res = p.get_resp sm.
  Arguments get_result/.

  Definition empty_mod (s : p.T) := 
    {| module_state := s; inp := None |}.
  
  Definition is_empty (st : p.st) :=
    inp st = p.None.

  Global Instance mkGenericReqResp : module _ := 
    primitive_module#(vmet [ get_result ] amet [ enq; deq ]).

End GenericReqResp.

Module Cb_impl.
  Local Instance cb_modules : instances :=
    #|
      reg.mkReg r0;
      reg.mkReg r0_valid;
      reg.mkReg r1;
      reg.mkReg r1_valid;
      reg.mkReg h;
      reg.mkReg t;
      reg.mkReg cnt
    |#.

  Definition reserve :=
    (action_method (tag)
      (begin
        (set vcnt {read cnt})
        (if (= vcnt 2)
          abort
          (begin
            {write cnt (+ vcnt 1)}
            (if (= {read t} 1)
              (if (= tag 1) 
                {write t 0}
                abort)
              (if (= tag 0) 
                {write t 1}
                abort)))))).
  Arguments reserve /.

  Definition deq :=
    (action_method ()
      (begin
        (set vcnt {read cnt})
        (set vh {read h})
        (if (! (= vcnt 0))
          pass
          abort)
        (if (& (= vh 1) (= {read r1_valid} 1))
          (begin
            {write h 0}
            {write r1_valid 0}
            {write cnt (minus (# vcnt 1))})
          (if (& (= vh 0) (= {read r0_valid} 1))
            (begin
              {write h 1}
              {write r0_valid 0}
              {write cnt (minus (# vcnt 1))})
          (* all entries not valid *)
          abort)))).
  Arguments deq /.

  Definition update :=
    (action_method (tag n)
      (begin
        (set vh {read h})
        (set vcnt {read cnt})
        (* should also check if cnt is 0 *)
        (if (& (<= tag 1) (! (= vcnt 0)))
          pass
          abort)
        (if (& (& (= tag 1) (= {read r1_valid} 0))
            (| (= vh 1) (= vcnt 2)))
          (begin
            {write r1 n}
            {write r1_valid 1})
          (if (& (& (= tag 0) (= {read r0_valid} 0))
              (| (= vh 0) (= vcnt 2)))
            (begin
              {write r0 n}
              {write r0_valid 1})
            abort)))).
  Arguments update /.

  Definition get_tag :=
    (value_method ()
      (begin
        (if (= {read cnt} 2)
          abort
          {read t}))).
  Arguments get_tag /.

  Definition first :=
    (value_method ()
      (begin
        (set vh {read h})
        (if (& (= vh 0) (= {read r0_valid} 1))
          {read r0}
          (if (& (= vh 1) (= {read r1_valid} 1))
            {read r1}
            abort)))).
  Arguments first /.
  
  Global Instance mkCb_impl : module _ :=
    module#(vmet [get_tag; first] amet [reserve; deq; update]).
End Cb_impl.

Module Cb_spec.
  Inductive Cb_entry :=
    | completed : forall (tag : N) (res : N), Cb_entry
    | inflight : forall (tag : N), Cb_entry.

  Fixpoint not_in (tag : N) (l : list Cb_entry) : Prop :=
    match l with
      | nil => True
      | completed _ _ :: t => not_in tag t
      | inflight tag' :: t => tag' <> tag /\ (not_in tag t)
    end.

  Lemma not_in_dist : forall tag (l1 l2 : list Cb_entry), not_in tag (l1 ++ l2) = (not_in tag l1 /\ not_in tag l2).
  induction l1.
    - intros. simpl. rewrite PropLemmas.and_True_l. eauto.
    - intros. destruct a.
      * simpl. rewrite IHl1. eauto.
      * simpl. apply PropExtensionality.propositional_extensionality. rewrite IHl1. split.
        ** intros; apply and_assoc; eauto.
        ** intros; apply and_assoc in H; eauto.
  Qed.

  (* Another way to define the predicate: *)
  Definition not_in' (tag : N) (l : list (N * option N)) := 
    let just_tags := map fst l in 
    not (List.In tag just_tags).
  Arguments not_in' /.

  Fixpoint extract_res (l : list Cb_entry) :=
    match l with
      | nil => []
      | completed _ res :: t => res :: extract_res(t)
      | inflight _ :: t => extract_res(t)
      end.

  Lemma extract_res_app : forall l l', extract_res (l ++ l') = extract_res l ++ extract_res l'.
  Proof.
    induction l.
    - eauto.
    - intros.
      simpl.
      destruct a;
      rewrite IHl; eauto.
  Qed.

  Fixpoint all_completed (l : list Cb_entry) :=
    match l with
    | nil => True
    | completed _ _ :: t => all_completed(t)
    | inflight _ :: t => False
    end.

  Lemma all_completed_app : forall l l', all_completed (l ++ l') = (all_completed l /\ all_completed l').
  Proof.
    induction l; intros.
    - rewrite PropLemmas.and_True_l in *. eauto.
    - simpl.
      destruct a;
      apply PropExtensionality.propositional_extensionality;
      try rewrite IHl;
      tauto.
  Qed. 

  (* Typical stuff you might want to prove: *)
  Lemma lemma2 : forall l l2 tag, not_in' tag l -> not_in' tag l2 -> not_in' tag (l ++ l2). 
    intros.
    unfold not_in' in *.
    rewrite map_app.
    intro.
    eapply in_app_iff in H1.
    destruct H1; eauto.
  Qed.

  Lemma lemma2' : forall l l2 tag, not_in tag l -> not_in tag l2 -> not_in tag (l ++ l2). 
  induction l.
  - intros; simpl; eauto.
  - intros; simpl in*.
    destruct a eqn:?.
    firstorder.
    destruct H.
    split; eauto.
(*  (* manual proof: *)
  split; try eapply H.
  apply IHl.
  apply H.
  apply H0.
  intros.
 *)
  Qed.

  Definition reserve' (tag : N) (l : list Cb_entry) : list Cb_entry :=
    inflight tag :: l.
  Arguments reserve' /.

  Definition extract_tag (l : list Cb_entry) :=
    List.map (fun e => match e with
                | inflight t => t
                | completed t _ => t
              end) l.
  Arguments extract_tag l /.

  Definition unique_tag (l : list Cb_entry) :=
    NoDup (extract_tag l).
  Arguments unique_tag l /.

  Definition reserve (arg : N) (st : SModule) (st' : SModule) :=
    exists (l : list Cb_entry), st = *( l )* /\
    unique_tag l /\
    (* NoDup (reserve' arg l) /\ *)
    (* not_in arg l /\ *)
    st' = *( reserve' arg l )*.
  Arguments reserve /.

  Definition deq (arg : N) (st : SModule) (st' : SModule) :=
    exists (l : list Cb_entry) (tag n : N), st = *( l ++ [completed tag n] )* /\
    st' = *( l )*.
  Arguments deq /.

  Definition update' (l1 l2 : list Cb_entry) e :=
    l1 ++ [e] ++ l2.
  Arguments update' /.

  Definition update (arg : N) (st : SModule) (st' : SModule) :=
    dlet {tag n} := arg in
    exists (l1 l2: list Cb_entry), st = *( update' l1 l2 (inflight tag) )* /\
    unique_tag (update' l1 l2 (inflight tag)) /\
    st' = *( update' l1 l2 (completed tag n) )*.
  Arguments update /.

  Definition get_tag (_arg : N) (st : SModule) (ret : N) :=
    exists (l : list Cb_entry) (tag : N), st = *( l )* /\
    unique_tag (reserve' tag l) /\ ret = tag.
  Arguments get_tag /.

  Definition first (_arg : N) (st : SModule) (ret : N) :=
    exists (l : list Cb_entry) (tag n : N), st = *( l ++ [completed tag n] )* /\
    ret = n.
  Arguments first /.
  
  Global Instance mkCb : module _ :=
    primitive_module#(vmet [get_tag; first] amet [reserve; deq; update]).
End Cb_spec.

Module Bag. 
    Notation map := {fmap BinNums_N__canonical__Ord_Ord -> N}.

    Definition map_update (k v : N) (m : map) : map :=
      setm m k v.
    Arguments map_update /.

    Definition map_remove (k : N) (m : map) : map :=
      remm m k.
    Arguments map_remove /.

    Definition add (arg : N) (st : SModule) (st' : SModule) :=
      dlet {k v} := arg in
      exists (m : map), st = *( m )* /\
      m k = None /\
      st' = *( map_update k v m )*.
    Arguments add /.
    
    Definition remove (arg : N) (st : SModule) (st' : SModule) :=
      exists (m : map) (v : N), st = *( m )* /\
      m arg = Some(v) /\
      st' = *( map_remove arg m )*.
    Arguments remove /.

    Definition get_random (_arg : N) (st : SModule) (ret : N) :=
      exists (m : map) (k v : N), st = *( m )* /\
      m k = Some(v) /\
      ret = {# k v}.
    Arguments get_random /.

    Definition not_in (arg : N) (st : SModule) (_ret : N) :=
      exists (m : map), st = *( m )* /\
      m arg = None.
    Arguments not_in /.

    Definition empty_bag :=
      (emptym : map).
    Arguments empty_bag /.

    Global Instance mkBag : module _ :=
      primitive_module#(vmet [get_random; not_in] amet [add; remove]).
End Bag.

Module Proc (gen_m : GenericReqResp_t).
  Module m := GenericReqResp gen_m.
  Import m.
  Definition m := mkGenericReqResp.

  Notation map := {fmap N -> N}.

  Definition map_update (k v : N) (m : map) : map :=
    setm m k v.
  Arguments map_update /.

  Definition map_remove (k : N) (m : map) : map :=
    remm m k.
  Arguments map_remove /.

  Definition empty_bag :=
    (emptym : map).
  Arguments empty_bag /.

  Inductive buffered_input := 
  | NoneB 
  | InFlight (tag : N) (input : N).

  Definition construct_proc (ms : gen_m.st) (b : map) (inp : buffered_input) : array SModule :=
    [| ms; b; inp |].
  Arguments construct_proc /.

  Definition push (arg : N) (st : SModule) (st' : SModule) :=
    dlet {tag op} := arg in
    exists ms ms' (b : map),
    st = *( construct_proc ms b NoneB)* /\
    b tag = None /\
    (aget (action_spec m) 0 (* enq method is 0 *)
      op *( ms )* *( ms' )*) /\
    st' = *( construct_proc ms' b (InFlight tag op) )*.
  Arguments push /.

  Definition pull (arg : N) (st : SModule) (st' : SModule) :=
    exists ms (inp : buffered_input) (b : map) v,
    st = *( construct_proc ms b inp )* /\
    b arg = Some v /\
    st' = *( construct_proc ms (map_remove arg b) inp )*.
  Arguments pull /.

  Definition peek (_arg : N) (st : SModule) (ret : N) :=
    exists ms (inp : buffered_input) (b : map) (k v : N) ,
    st = *( construct_proc ms b inp )* /\
    b k = Some v /\
    ret = {# k v}.
  Arguments peek /.

  Definition complete_m (st : SModule) (st' : SModule) :=
    exists ms ms' (b : map) _arg _arg' op tag ret,
    st = *( construct_proc ms b (InFlight tag op) )* /\
    (aget (value_spec m) 0 (* get_result *)
      _arg' *( ms )* ret) /\
    b tag = None /\
    (aget (action_spec m) 1 (* deq genericReqResp *)
      _arg *( ms )* *( ms' )*) /\
    st' = *( construct_proc ms' (map_update tag ret b) NoneB )*.
  Arguments complete_m /.

  Definition flushed_proc (ms : gen_m.T) :=
    let state := {| gen_m.module_state := ms; gen_m.inp := gen_m.None |} in
    construct_proc state empty_bag NoneB.
  Arguments flushed_proc /.

  Global Instance mkProc : module _ :=
    primitive_module#(rules [complete_m] vmet [peek] amet [push; pull]).
End Proc.

Module Ooo (gen_m : GenericReqResp_t).
  Module m := Proc gen_m.
  Import m.
  Local Instance sub_modules : instances :=
    #|
      mkProc proc;
      Cb_spec.mkCb cb
    |#.

  Definition enq' ms b tag x l :=
    [| m.construct_proc ms b (m.InFlight tag x); Cb_spec.reserve' tag l |].
  Arguments enq' /.

  Definition enq :=
      (action_method (op) 
        (begin
          (set tag {get_tag cb})
          {reserve cb tag}
          {push proc (# tag op)})).
  Arguments enq /.

  Definition deq :=
      (action_method () {deq cb}).
  Arguments deq /.
  
  Definition first :=
    (value_method () {first cb}).
  Arguments first /.

  Definition complete :=
    (rule
      (begin
        (set (tag res) {peek proc})
        {update cb (# tag res)}
        {pull proc tag})).
  Arguments complete /.
  
  Global Instance mkOoo : module _ :=
    module#(rules [complete] vmet [first] amet [enq; deq]).
End Ooo.

Module Pipeline_spec (gen_m : GenericReqResp_t).
  Module m := GenericReqResp gen_m.
  Import m.
  Definition m := mkGenericReqResp.

  Definition enq' (ms : gen_m.st) (res : N) l :=
    [| ms; res :: l |].
  Arguments enq' /.

  Definition enq (arg : N) (st : SModule) (st' : SModule) :=
    (* we have to specifically define the types of sm *)
    (* the inferred type would be SModule *)
    (* since action method expects SModule? *)
    exists (ms ms' ms'' : gen_m.st) _arg _arg' (l : list N) x, st = *[| ms; l |]* /\ 
    (aget (action_spec m) 0 arg *( ms )* *( ms' )*) /\
    (aget (value_spec m) 0 _arg *( ms' )* x) /\
    (aget (action_spec m) 1 _arg' *( ms' )* *( ms'' )*) /\
    st' = *( enq' ms'' x l )*.
  Arguments enq /.

  Definition deq (_arg : N) (st : SModule) (st' : SModule) :=
    exists (ms : gen_m.st) (l : list N) x, st = *[| ms; l ++ [x] |]* /\ 
    st' = *[| ms; l |]*.
  Arguments deq /.

  Definition first (_arg : N) (st : SModule) (ret : N) :=
    exists (ms : gen_m.st) (l : list N) x, st = *[| ms; l ++ [x] |]* /\ 
    ret = x.
  Arguments first /.
  
  Global Instance mkPipeline : module _ :=
    primitive_module#(vmet [first] amet [enq; deq]).
End Pipeline_spec.

Class EqDec (T: Type) :=
  { eq_dec: forall t1 t2: T, { t1 = t2 } + { t1 <> t2 } }.

#[export] Instance EqDecN : EqDec N.
Proof.
    constructor.
    intros.
    repeat decide equality.
Defined.

#[export] Instance EqDecCb_entry : EqDec Cb_spec.Cb_entry.
Proof.
  constructor.
  intros.
  repeat decide equality.
Defined.

Require Import TransitionNotation.

Module Ooo_pipeline (gen_m : GenericReqResp_t).
  Module ooo := Ooo gen_m.
  Import ooo.
  Module pipeline := Pipeline_spec gen_m.
  Import pipeline.
  Import Cb_spec.

  Inductive ϕ : forall (ist sst : SModule), Prop :=
  | flushed : forall proc ms cb l, proc = (ooo.m.flushed_proc ms) ->
    Cb_spec.all_completed cb ->
    (Cb_spec.extract_res cb) = l ->
    ϕ *[| proc; cb |]* *[| {| gen_m.module_state := ms; gen_m.inp := gen_m.None |}; l |]*
  | enq : forall (ist : N -> N -> SModule) (sst : N -> SModule) prev_ist prev_sst,
    indistinguishable ooo.mkOoo pipeline.mkPipeline prev_ist prev_sst ->
    (forall x tag, ϕ (ist x tag) (sst x) /\
      (exists (i_ms : gen_m.st) (b : ooo.m.map) (l : list Cb_entry),
        (ist x tag) = *( ooo.enq' i_ms b tag x l )* /\
        (prev_ist --{{ ooo.mkOoo enq (x) }}--> (ist x tag)) /\
        (prev_sst --{{ pipeline.mkPipeline enq (x) }}--> (sst x))
      )
    ) ->
    ϕ prev_ist prev_sst
  | deq : forall ist sst prev_ist prev_sst x, ϕ ist sst ->
    indistinguishable ooo.mkOoo pipeline.mkPipeline prev_ist prev_sst ->
    (prev_ist --{{ ooo.mkOoo deq (x) }}--> ist) ->
    (prev_sst --{{ pipeline.mkPipeline deq (x) }}--> sst) ->
    ϕ prev_ist prev_sst
  (* process *)
  | complete : forall (ist prev_ist prev_sst : SModule),
    indistinguishable ooo.mkOoo pipeline.mkPipeline prev_ist prev_sst -> ϕ ist prev_sst ->
    (prev_ist --{{ ooo.mkOoo complete }}--> ist) ->
    ϕ prev_ist prev_sst
  (* pull *)
  | complete_m : forall (ist prev_ist prev_sst : SModule),
    indistinguishable ooo.mkOoo pipeline.mkPipeline prev_ist prev_sst -> ϕ ist prev_sst ->
    lift_to 0 (nth 0 (nth 0 (subrules_spec ooo.mkOoo) []) unexisting_rule) prev_ist ist ->
    ϕ prev_ist prev_sst.

  Definition ϕ_ind' : forall (P : SModule -> SModule -> Prop)
  (f : forall (proc : array SModule) (ms : gen_m.T) 
	     (cb : list Cb_entry) (l : list N),
       proc = m.flushed_proc ms ->
       all_completed cb ->
       extract_res cb = l ->
       P *[| proc; cb |]*
         *[| {| gen_m.module_state := ms; gen_m.inp := gen_m.None |}; l |]*)
  (f0 : forall (ist : N -> N -> SModule) (sst : N -> SModule)
         (prev_ist prev_sst : SModule),
       indistinguishable mkOoo mkPipeline prev_ist prev_sst ->
       (forall x tag : N,
        ϕ (ist x tag) (sst x) /\
        (exists
           (i_ms _ : gen_m.st) (b : m.map) (l : list Cb_entry) 
         (_ : list N),
           ist x tag = *( ooo.enq' i_ms b tag x l )* /\
           match index_of "enq" (@action_methods mkOoo mkOoo) 0 with
           | Some x0 => @aget action_method_spec_t (action_spec mkOoo) x0 x
           | None => unexisting_rule
           end (prev_ist : SModule) (ist x tag : SModule) /\
           match
             index_of "enq" (@action_methods mkPipeline mkPipeline) 0
           with
           | Some x0 =>
               @aget action_method_spec_t (action_spec mkPipeline) x0 x
           | None => unexisting_rule
           end (prev_sst : SModule) (sst x : SModule)) /\
        P (ist x tag) (sst x)) ->
       P prev_ist prev_sst)
  (f1 : forall (ist sst prev_ist prev_sst : SModule) (x : N),
        ϕ ist sst ->
        P ist sst ->
        indistinguishable mkOoo mkPipeline prev_ist prev_sst ->
        match index_of "deq" (@action_methods mkOoo mkOoo) 0 with
        | Some x0 => @aget action_method_spec_t (action_spec mkOoo) x0 x
        | None => unexisting_rule
        end (prev_ist : SModule) (ist : SModule) ->
        match index_of "deq" (@action_methods mkPipeline mkPipeline) 0 with
        | Some x0 => @aget action_method_spec_t (action_spec mkPipeline) x0 x
        | None => unexisting_rule
        end (prev_sst : SModule) (sst : SModule) -> 
        P prev_ist prev_sst)
  (f2 : forall ist prev_ist prev_sst : SModule,
        indistinguishable mkOoo mkPipeline prev_ist prev_sst ->
        ϕ ist prev_sst ->
        P ist prev_sst ->
        match index_of "complete" (@rule_names mkOoo mkOoo) 0 with
        | Some x => @nth rule_spec_t x (rule_spec mkOoo) unexisting_rule
        | None =>
            match index_of "complete" (@action_methods mkOoo mkOoo) 0 with
            | Some x => @aget action_method_spec_t (action_spec mkOoo) x 0
            | None => unexisting_rule
            end
        end (prev_ist : SModule) (ist : SModule) -> 
        P prev_ist prev_sst)
  (f3 : forall ist prev_ist prev_sst : SModule,
        indistinguishable mkOoo mkPipeline prev_ist prev_sst ->
        ϕ ist prev_sst ->
        P ist prev_sst ->
        lift_to 0
          (@nth rule_spec_t 0
             (@nth (list rule_spec_t) 0 (subrules_spec mkOoo) [])
             unexisting_rule) prev_ist ist -> P prev_ist prev_sst), forall (ist sst : SModule), ϕ ist sst -> P ist sst.
  intros.
  revert H. revert ist sst.
  refine (fix F (ist sst : SModule) (ϕ : ϕ ist sst) {struct ϕ} : P ist sst :=
  match ϕ in (Ooo_pipeline.ϕ ist0 sst0) return (P ist0 sst0) with
  | flushed proc ms cb l e a e0 => f proc ms cb l e a e0
  | enq ist0 sst0 prev_ist prev_sst i a => _
  | deq ist0 sst0 prev_ist prev_sst x ϕ0 i y y0 =>
      f1 ist0 sst0 prev_ist prev_sst x ϕ0 (F ist0 sst0 ϕ0) i y y0
  | complete ist0 prev_ist prev_sst i ϕ0 y =>
      f2 ist0 prev_ist prev_sst i ϕ0 (F ist0 prev_sst ϕ0) y
  | complete_m ist0 prev_ist prev_sst i ϕ0 l =>
      f3 ist0 prev_ist prev_sst i ϕ0 (F ist0 prev_sst ϕ0) l
  end).
  specialize f0 with (1 := i).
  eapply f0.
  intros.
  specialize (a x tag).
  cleanup.
  split; [exact H | ].
  split; [eauto | ].
  rm_existentials.
  assumption.
  eapply [].
  eauto.
  eapply F.
  eapply H.
  Qed.

  Definition related ist sst :=
    ϕ ist sst /\
    exists (bag : Bag.map) (inp : ooo.m.buffered_input) (cb : list Cb_spec.Cb_entry) (m_state_i m_state_s : gen_m.st) (l : list N),
      (* m module state can be different between impl and spec *)
      ist = *[| [| m_state_i; bag; inp |]; cb |]* /\
      sst = *[| m_state_s; l |]*.
  Arguments related /.

  Definition lock_step {smi sms} (impl : module smi) (spec : module sms) (n : nat) (phi  : SModule -> SModule -> Prop) (si ss : SModule):=  
    match n with
    (* enq *)
    | 0%nat => forall x (ei : SModule),
      (si --{{ impl enq ( x ) }}--> ei) ->
      (exists es, (ss --{{ spec enq ( x ) }}--> es) /\ phi ei es)
    (* deq *)
    | 1%nat => forall x ei,
      (si --{{ impl deq ( x ) }}--> ei) ->
      (exists es, (ss --{{ spec deq ( x ) }}--> es) /\ phi ei es)
    (* complete *)
    | 2%nat => forall ei,
      (si --{{ impl complete }}--> ei) ->
      phi ei ss
    (* complete_m *)
    | 3%nat => forall ei,
      lift_to 0 (nth 0 (nth 0 (subrules_spec impl) []) unexisting_rule)
      si ei ->
      phi ei ss
    | _ => True
    end.
    Arguments lock_step {smi sms} impl spec n phi si ss : simpl never.

  Ltac prove_precond H :=
    match type of H with
      | ?a -> ?b =>
        let newname := fresh in
        assert a as newname; [ | specialize (H newname)]; cycle 1
      end.

  Lemma remm_get : forall {T S} m k tag, getm m tag = None -> (remm (T:=T) (S:=S) m k) tag = None.
  Proof.
    intros.
    rewrite remmE.
    destruct (eqtype.eq_op tag k); eauto.
  Qed.

  Lemma extract_tag_app : forall l1 l2, extract_tag (l1 ++ l2) = extract_tag l1 ++ extract_tag l2.
  Proof.
    induction l1.
    - intros. simpl. eauto.
    - intros.
      destruct a; simpl; rewrite IHl1; eauto.
  Qed.

  Lemma tag_inflight_completed : forall l1 l2 k v, extract_tag (l1 ++ inflight k :: l2) = extract_tag (l1 ++ completed k v :: l2).
  Proof.
    intros.
    rewrite extract_tag_app.
    rewrite extract_tag_app.
    eauto.
  Qed.

  Lemma after_inflight_completed_tail : forall l3 l1 l2 k tag n, l1 ++ inflight k :: l2 = l3 ++ [completed tag n] ->
    exists l, l2 = l ++ [completed tag n].
  Proof.
      induction l3.
        - intros.
          destruct l2.
            * simpl in H.
              destruct l1.
                ** inversion H.
                ** apply (f_equal (@List.length Cb_entry)) in H.
                   rewrite app_length in H.
                   simpl in H.
                   lia.
            * apply (f_equal (@List.length Cb_entry)) in H. 
              rewrite app_length in H.
              simpl in H.
              lia. 
        - intros.
          destruct l1.
            * apply (f_equal (@tl Cb_entry)) in H.
              simpl in H.
              rm_existentials.
              eauto.
            * apply (f_equal (@tl Cb_entry)) in H.
              simpl in H.
              apply IHl3 in H.
              eauto.
  Qed.
  
  Lemma aftter_completed_completed_tail : forall l3 l1 l2 k v tag n, l1 ++ completed k v :: l2 = l3 ++ [completed tag n] ->
    l2 = [] \/ (exists l, l2 = l ++ [completed tag n]).
  Proof.
    induction l3.
      - simpl.
        intros.
        destruct l2.
        left.
        eauto.
        apply (f_equal (@List.length Cb_entry)) in H.
        rewrite app_length in H.
        simpl in H.
        lia.
    - simpl.
      intros.
      destruct l2.
      left.
      eauto.
      right.
      apply (f_equal (@tl Cb_entry)) in H.
      destruct l1.
      simpl in H.
      eauto.
      simpl in H.
      apply IHl3 in H.
      destruct H.
      inversion H.
      eauto.
  Qed.

  Lemma unqiue_tag_remove : forall l l' k, unique_tag (l ++ inflight k :: l') -> unique_tag (l ++ l').
  Proof.
    intros.
    unfold unique_tag in *.
    unfold extract_tag in *.
    rewrite map_app in H.
    simpl in H.
    apply NoDup_remove in H.
    destruct H.
    rewrite <- map_app in H.
    eauto.
  Qed.

  Lemma unique_partition' :
    forall l1 l2 l3 l4 k, l1 ++ inflight k :: l2 = l3 ++ inflight k :: l4 ->
    unique_tag (l1 ++ inflight k :: l2) -> unique_tag (l3 ++ inflight k :: l4) -> l1 = l3 /\ l2 = l4.
  Proof.
    induction l1, l3.
      - intros.
        split; [eauto | ].
        apply (f_equal (@tl Cb_entry)) in H.
        simpl in H.
        eauto.
      - intros.
        apply (f_equal (@hd Cb_entry (inflight 0))) in H.
        simpl in H.
        apply NoDup_map_inv in H1.
        apply NoDup_remove in H1.
        destruct H1.
        unfold List.In in H2.
        simpl in H2.
        apply Decidable.not_or in H2.
        destruct H2.
        unfold not in H2.
        rewrite H in H2.
        exfalso.
        apply H2.
        eauto.
      - intros.
        apply (f_equal (@hd Cb_entry (inflight 0))) in H.
        simpl in H.
        apply NoDup_map_inv in H0.
        apply NoDup_remove in H0.
        destruct H0.
        unfold List.In in H2.
        simpl in H2.
        apply Decidable.not_or in H2.
        destruct H2.
        unfold not in H2.
        rewrite H in H2.
        exfalso.
        apply H2.
        eauto.
      - intros.
        pose proof (f_equal (@hd Cb_entry (inflight 0)) H) as new_eq.
        simpl in new_eq.
        apply (f_equal (@tl Cb_entry)) in H.
        simpl in H.
        rewrite <- app_comm_cons in H0, H1.
        apply unqiue_tag_remove with (l := []) in H0, H1.
        apply IHl1 in H; eauto.
        destruct H.
        split.
        rewrite new_eq.
        rewrite H.
        eauto.
        eauto.
    Qed.

  Theorem auxiliary_one {dec : EqDec N} {dec' : EqDec Cb_entry} :
    forall (l1 l2: list Cb_entry) (e1 e2: N) (random1 random2 : list Cb_entry)
     (new_hyp : l1 ++ inflight e1 :: l2 = random1 ++ inflight e2 :: random2),
     ( e2 <> e1 /\ exists (l3 l4 l5 l6 : list Cb_entry),
        l3 ++ inflight e1 :: l4 ++ l5 ++ inflight e2 :: l6 = l1 ++ inflight e1 :: l2 \/ 
        l3 ++ inflight e2 :: l4 ++ l5 ++ inflight e1 :: l6 = l1 ++ inflight e1 :: l2 
        ) \/ (e2 = e1).
    Proof.
      intros.
      assert (e1 <> e2 \/ e1 = e2) as mycase.
      destruct dec as [ n_dec ].
      specialize (n_dec e1 e2); firstorder congruence.
      destruct mycase as[ l | r ];[ | right; eauto ].
      {
        left.
        split; eauto.
        destruct dec' as [ cb_dec ].
        pose proof (in_dec cb_dec (inflight e2) l2) as Indec.
        destruct Indec as [in_l' | not_in_l'].
        {
          exists l1.
          pose proof (in_split _ _ in_l') as insplit.
          destruct insplit as (foo & bar & pf).
          rewrite pf.
          exists foo.
          exists nil.
          exists bar.
          left; eauto.
        }
        {
          pose proof (in_dec cb_dec (inflight e2) l1) as Indec.
          destruct Indec as [in_l'' | not_in_l''].
          {
            pose proof (in_split _ _ in_l'') as insplit.
            destruct insplit as (foo & bar & pf).
            rewrite pf.
            exists foo.
            exists bar.
            exists [].
            exists l2.
            right.
            simpl.
            rewrite app_comm_cons.
            rewrite app_assoc.
            eauto.
          }
          {
            exfalso.
            assert (List.In (inflight e2) ( l1 ++ inflight e1 :: l2 )).
            rewrite new_hyp.
            eapply in_app_iff.
            right; econstructor; eauto.
            eapply in_elt_inv in H as cool.
            destruct cool as [win | alsowin].
            inversion win.
            firstorder.
            eapply in_app_iff in alsowin.
            destruct alsowin; eauto.
          }
        }
      }
  Qed.

  Ltac map_hammer :=
    repeat (match goal with
      | [ |- ?a = _] => match type of a with
                          | @FMap.fmap_of _ _ (_ _) => idtac a; eapply eq_fmap; unfold ssrfun.eqfun; intros
                        end
      | [ H : getm (remm _ _) _ = None |- _ ] => rewrite remmE in H
      | [ |- context[setm _ _]] => rewrite setmE
      | [ |- context[remm _ _] ] => rewrite remmE
      | [ |- context[emptym _] ] => rewrite emptymE
      | [ |- context[if eqtype.eq_op ?a ?b then _ else _] ] => 
        destruct (@eqtype.eq_op BinNums_N__canonical__Ord_Ord a b) eqn:?; try eauto
      | [ H : eqtype.eq_op ?a ?b = true |- _ ] => apply N.eqb_eq in H; light_clean_propagate; try lia
      | [ H : eqtype.eq_op ?a ?b = false |- _ ] => apply N.eqb_neq in H; light_clean_propagate; eauto
      | [ H1 : ?a ?b = Some _, H2 : ?a ?b = None |- _ ] => rewrite H1 in H2; discriminate H2
      | _ => eauto
    end).

  Ltac clear_trivial_evar :=
    try rm_existentials; split; try (repeat rewrite merge_split1); try (repeat rewrite merge_split2); eauto.

  Ltac clear_trivial_wpa_step :=
    repeat (match goal with
      | [ |- wpa _ _ _ _ _ _ _ _ _ _ ] => reconstruct_wpa; merge_simpl; simpl
      | [ |- step _ _ _ _ _ _ _ _ _ ] => reconstruct_step; merge_simpl; simpl
      | _ => solve clear_trivial_evar
    end).

  Ltac extract_equality' H n destroyH :=
    match goal with 
    | [H2 :*( 0 %nat )*  = *( 0%nat )* |- _ ] =>
      clear H2
    | _ =>
      let name := fresh "fnEq" H "_" in
      pose proof (FunctionalExtensionality.equal_f H n) as name;
      simpl in name; extract_equality' H (S n) destroyH
    end.

  Ltac extract_all_fnequality := 
    repeat match goal with 
    | [ H : (?f : nat -> _) = ?g |- _] => extract_equality' H 0%nat 1%nat; light_clean_propagate; clear H
    end.

  Ltac unify_equality :=
    repeat match goal with
      | [ H1 : ?a = *( _ )*, H2 : ?a = *( _ )* |- _ ] =>
        rewrite H1 in H2; light_clean_propagate
      | [ H1 : ?a = *( _ )*, H2 : *( _ )* = ?a |- _ ] =>
        rewrite H1 in H2; light_clean_propagate
      | [ H1 : ?a = Some _, H2 : ?a = Some _ |- _ ] =>
        rewrite H1 in H2; inversion H2; light_clean_propagate; clear H2
      | _ => simpl in * |-
    end.

  Lemma ϕ_implies_eq_size : forall ist sst,
    related ist sst ->
    exists (proc : array SModule) (cb : list Cb_entry) (sm : gen_m.st) (l : list N), ist = *[| proc; cb |]* /\ sst = *[| sm; l |]* /\
    List.length cb = List.length l.
  Proof.
    unfold related.
    intros.
    cleanup.
    revert H0 H1.
    generalize dependent x0.
    generalize dependent x1.
    generalize dependent x2.
    generalize dependent x3.
    generalize dependent x4.
    generalize dependent x.

    induction H using ϕ_ind'; intros.
    {
      light_clean_propagate.
      extract_all_fnequality.
      rm_existentials.
      split; eauto.
      split; [eauto | ].
      induction x1.
        - eauto.
        - induction a.
          ** simpl. eauto.
          ** unfold all_completed in H0. inversion H0.
    }
    {
      specialize (H0 0 0).
      simpl in H0.
      light_clean_propagate.
      extract_all_fnequality.
      symb_ex_split.
      extract_all_fnequality.
      merge_simpl.
      specialize (
        HB0 b0 (gen_m.get_resp (gen_m.req sm1 0) :: l0) 
        {| gen_m.module_state := gen_m.deq (gen_m.req sm1 0); gen_m.inp := gen_m.None |} 
        {| gen_m.module_state := gen_m.req sm 0; gen_m.inp := gen_m.Done |} (inflight tag :: l1) (m.InFlight tag 0)
      ).
      light_clean_propagate.
      prove_precond HB0.
      prove_precond HB0.
      light_clean_propagate.
      unify_equality.
      extract_all_fnequality.
      rm_existentials.
      simpl in HB0.
      inversion HB0.
      split; eauto.
      rewrite HB1.
      eauto.
      rewrite HA0.
      wrapped_arrays_equal 2%nat.
    }
    {
      simpl in *.
      light_clean_propagate.
      extract_all_fnequality.
      symb_ex_split.
      specialize (IHϕ x0 l ms x2 l0 x5).
      prove_precond IHϕ.
      prove_precond IHϕ.
      light_clean_propagate.
      extract_all_fnequality.
      simpl in *.
      light_clean_propagate.
      rm_existentials.
      split; [eauto | split].
      wrapped_arrays_equal 2%nat.
      rewrite app_length.
      rewrite HB2.
      rewrite app_length.
      eauto.
      eauto.
      apply app_inj_tail in H2.
      light_clean_propagate.
      wrapped_arrays_equal 2%nat.
    }
    {
      simpl in *.
      light_clean_propagate.
      symb_ex_split.
      merge_simpl.
      extract_all_fnequality.
      specialize (IHϕ (remm b k) x4 x3 ms (l0 ++ completed k v :: l3) inp).
      prove_precond IHϕ.
      prove_precond IHϕ.
      light_clean_propagate.
      extract_all_fnequality.
      simpl in *.
      light_clean_propagate.
      rm_existentials.
      split; [eauto | split].
      eauto.
      apply unique_partition' in H4; eauto.
      light_clean_propagate.
      rewrite app_length in HB3.
      simpl in HB3.
      rewrite app_length.
      simpl.
      eauto.
      eauto.
      wrapped_arrays_equal 2%nat.
    }
    {
      unfold lift_to in H1.
      light_clean_propagate.
      simpl in *.
      light_clean_propagate.
      extract_all_fnequality.
      specialize (IHϕ (setm b tag (gen_m.get_resp sm)) x4 x3 {| gen_m.module_state := gen_m.deq sm; gen_m.inp := gen_m.None |} x1 m.NoneB).
      prove_precond IHϕ.
      prove_precond IHϕ.
      light_clean_propagate.
      extract_all_fnequality.
      rm_existentials.
      split; [eauto | split].
      eauto.
      eauto.
      eauto.
      wrapped_arrays_equal 2%nat.
    }
  Qed.

  Theorem ϕ_implies_indistinguishable : forall (ist sst : SModule), ϕ ist sst -> indistinguishable ooo.mkOoo pipeline.mkPipeline ist sst.
  Proof.
    simpl.
    intros.
    induction H using ϕ_ind'; intros.
    {
      prove_indistinguishable.
      {
        light_clean_propagate.
        symb_ex_split.
        rm_existentials.
        split.
        rewrite extract_res_app.
        wrapped_arrays_equal 2%nat.
        eauto.
      }
      {
        light_clean_propagate.
        symb_ex_split.
        extract_all_fnequality.
        rm_existentials.
        assumption.
        assumption.
        rm_existentials.
        split; [wrapped_arrays_equal 2%nat | repeat clear_trivial_evar].
      }
      {
        light_clean_propagate.
        symb_ex_split.
        rm_existentials.
        split.
        rewrite extract_res_app.
        wrapped_arrays_equal 2%nat.
        eauto.
      }
    }
    all: eauto.
  Qed.

  Theorem relation_preserved : forall (init_i init_s : SModule), related init_i init_s ->
    forall i, lock_step (ooo.mkOoo) (pipeline.mkPipeline) i ϕ init_i init_s.
  Proof.
    simpl.
    intros init_i init_s H.
    inversion H.
    clear H.
    match goal with
    | [ H : ϕ ?ist ?sst |- _] =>
      induction H using ϕ_ind'; intros
    end.
    (* flushed case *)
    {
      destruct i; unfold lock_step.
      (* enq *)
      (* apply complete_m and complete horizontally *)
      (* then it's flushed again *)
      {
        (* proving enq is available at spec_nw *)
        unfold ooo.m.flushed_proc in H.
        simpl.
        light_clean_propagate.
        extract_all_fnequality.
        symb_ex_split.
        merge_simpl.
        extract_all_fnequality.
        rm_existentials.
        split.
        rm_existentials.
        assumption.
        assumption.
        split.
        wrapped_arrays_equal 2%nat.
        repeat clear_trivial_evar.

        (* proving ϕ impl_sw spec_sw *)
        (* applying complete_m horizontally *)
        eapply complete_m.
        all: cycle 2.
        (* instantiating resulting state after complete_m *)
        unfold lift_to.
        simpl.
        rm_existentials.
        split; [clear_trivial_evar | ].
        {
          rm_existentials.
          split.
          2:{
            rm_existentials.
            assumption.
            assumption.
            repeat clear_trivial_evar.
          }
          eauto.
        }
        (* proving impl_sw ≺ spec_sw *)
        {
          prove_indistinguishable.
          (* vm: first *)
          (* in flushed (extract_res cb) = l  *)
          (* calling first in impl-side imples *)
          (* availability of calling first in spec-side *)
          {
            light_clean_propagate.
            symb_ex_split.
            rm_existentials.
            unify_equality.
            split; [wrapped_arrays_equal 2%nat | eauto].
            apply (f_equal extract_res) in H1.
            rewrite extract_res_app in H1.
            simpl in H1.
            rewrite H1.
            rewrite app_comm_cons.
            eauto.
          }
          (* am: enq *)
          (* impl side can't enq back to back *)
          {
            simpl.
            rm_existentials.
            assumption.
            assumption.
            repeat clear_trivial_evar.
          }
          (* am: deq *)
          (* similar to first *)
          (* extract cb = l -> impl and spec are in sync *)
          (* availability of deq in impl -> availability of deq in spec *)
          {
            light_clean_propagate.
            symb_ex_split.
            rm_existentials.
            unify_equality.
            split; [wrapped_arrays_equal 2%nat | eauto].
            apply (f_equal extract_res) in H2.
            rewrite extract_res_app in H2.
            simpl in H2.
            rewrite H2.
            rewrite app_comm_cons.
            eauto.
          }
        }

        (* applying complete horizontally *)
        eapply complete.
        all: cycle 2.
        (* instantiating resulting state after complete *)
        simpl.
        rm_existentials.
        split; [eauto | split].
        eauto.
        split.
        clear_trivial_wpa_step; try rewrite HA4; simpl.
        split; [eauto | clear_trivial_evar].
        rewrite setmE.
        rewrite N.eqb_refl.
        split; eauto.
        split; [eauto | clear_trivial_evar]; merge_simpl.
        (* there's no other element in front of just enqueued element *)
        instantiate (2 := []).
        simpl.
        eauto.
        split; eauto.
        split; [eauto | clear_trivial_evar].
        merge_simpl.
        rewrite setmE.
        rewrite N.eqb_refl.
        split; eauto.
        simpl.
        merge_simpl.
        let y := eexists_st_array 2%nat in instantiate (1 := y).
        apply_log_fn 2%nat; rewrite HA4; simpl; merge_simpl; intros; try lia.
        rm_existentials.
        split; [eauto | split].
        rewrite setmE.
        rewrite N.eqb_refl.
        split; eauto.
        eauto.
        rm_existentials.
        instantiate (2 := []).
        simpl.
        split; eauto.

        (* proving impl ≺ spec after complete_m *)
        {
          prove_indistinguishable.
          (* vm: first *)
          (* after complete_m impl and spec are still in sync *)
          {
            simpl.
            light_clean_propagate.
            symb_ex_split.
            rewrite HA4 in HA7.
            simpl in HA7.
            unfold aget in HB3.
            unify_equality.
            rm_existentials.
            split; [wrapped_arrays_equal 2%nat | eauto].
            apply (f_equal extract_res) in H1.
            rewrite extract_res_app in H1.
            simpl in H1.
            rewrite H1.
            rewrite app_comm_cons.
            eauto.
          }
          (* am: enq *)
          (* impl side can't enq back to back *)
          {
            simpl.
            rm_existentials.
            assumption.
            assumption.
            repeat clear_trivial_evar.
          }
          (* am: deq *)
          (* similar to first *)
          {
            light_clean_propagate.
            symb_ex_split.
            rewrite HA4 in HA.
            simpl in *.
            unfold aget in HB3.
            unify_equality.
            rm_existentials.
            split; [wrapped_arrays_equal 2%nat | eauto].
            apply (f_equal extract_res) in H1.
            rewrite extract_res_app in H1.
            simpl in H1.
            rewrite H1.
            rewrite app_comm_cons.
            eauto.
          }
        }

        (* after complete_m and complete, impl and spec are back to flushed *)
        eapply flushed; eauto.
        custom_eq_array 3%nat.
        {
          f_equal. (* TODO check here if problem at QED time *)
          map_hammer.
        }
      }
      destruct i.
      (* deq *)
      (* from flushed, impl and spec are in sync *)
      (* dequeuing in impl -> dequeuing in spec *)
      {
        (* proving deq is available at spec_nw *)
        intros.
        simpl in *.
        light_clean_propagate.
        extract_all_fnequality.
        symb_ex_split.
        rm_existentials.
        split.
        rm_existentials.
        rewrite extract_res_app.
        simpl.
        split; [wrapped_arrays_equal 2%nat | eauto].

        (* proving ϕ impl_sw spec_sw *)
        assert (
          nxt_st = [| [| {| gen_m.module_state := ms; gen_m.inp := gen_m.None |}; emptym; m.NoneB |]; l0 |]
        ) by custom_eq_array 2%nat.
        light_clean_propagate.
        rewrite all_completed_app in H0.
        apply app_inj_tail in H1.
        light_clean_propagate.
        (* after deq, impl and spec are still flushed *)
        eapply flushed;
        try unfold m.flushed_proc;
        simpl;
        eauto.
      }
      destruct i.
      (* complete *)
      (* there's no element to complete in flushed *)
      (* -> contradiction *)
      {
        intros.
        simpl in *.
        light_clean_propagate.
        extract_all_fnequality.
        symb_ex_split.
        merge_simpl.
        extract_all_fnequality.
        inversion HA7.
      }
      destruct i.
      (* complete_m *)
      (* there's no element to pull from the bag in flushed *)
      (* -> contradiction *)
      {
        unfold lift_to.
        intros.
        unfold m.flushed_proc in H.
        light_clean_propagate.
        simpl in *.
        extract_all_fnequality.
      }
      eauto.
    }
    (* enq case *)
    {
      unfold lock_step.
      simpl.
      destruct i.
      (* enq *)
      (* first get the tag used in vertical enq *)
      (* and feed the tag to inductive hypothesis (horizontal enq) *)
      (* -> the two enq converge *)
      {
        (* remove print_array in this Ltac *)
        Ltac symb_ex_split ::= 
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
        end); simpl; repeat simpl_applylog.

        (* symbolically executing enq in impl-side (vertical) *)
        intros.
        light_clean_propagate.
        symb_ex_split.
        extract_all_fnequality.
        merge_simpl.

        (* specialize inductive hypothesis with the tag from vertical enq *)
        (* and symbolically executing enq horizontally *)
        specialize (H0 x tag).
        light_clean_propagate.
        extract_all_fnequality.
        symb_ex_split.
        extract_all_fnequality.
        merge_simpl.

        (* proving enq is available at spec_nw *)
        unify_equality.
        simpl in *.
        light_clean_propagate.
        extract_all_fnequality.
        rm_existentials.
        split.
        rm_existentials.
        assumption.
        assumption.
        repeat clear_trivial_evar.

        (* since they converge we have ϕ impl_se spec_se *)
        assert (
          nxt_st = [| 
            [| {| gen_m.module_state := gen_m.req sm0 x; gen_m.inp := gen_m.Done |}; b1; m.InFlight tag0 x |];
            inflight tag0 :: l 
          |]
        ) by custom_eq_array 2%nat.
        light_clean_propagate.
        rewrite HA6 in HA.
        eauto.
      }
      destruct i.
      (* deq *)
      (* do enq horizontally after deq in the lower side                *)
      (* do deq vertically after enq in the upper side                  *)
      (* 1. To prove deq is possible at the spec_nw: use                *)
      (*    the fact that impl_nw ≺ spec_nw                             *)
      (* 2. Get the tag from lower enq and use it to specialize         *)
      (*    the inductive hypothesis                                    *)
      (* 3. Do lock_step deq (it's trivial to prove preconditions since *)
      (*    enq-deq and deq-enq commute                                 *)
      {
        (* remove print_array *)
        Ltac symb_ex_split ::= 
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
          end); simpl; repeat simpl_applylog.

        (* symbolically executing deq in impl-side (vertical) *)
        intros.
        light_clean_propagate.
        destruct m_state_i.
        destruct m_state_s.
        symb_ex_split.

        (* prove deq is available at spec_nw *)
        (* and symbolically executing enq horizontally *)
        unfold indistinguishable in H.
        cleanup.
        specialize (H1 x 1%nat *( nxt_st )*).
        simpl in H1.
        prove_precond H1.
        light_clean_propagate.
        extract_all_fnequality.
        symb_ex_split.
        rm_existentials.
        split.
        rm_existentials.
        split; eauto.

        (* precondition for ≺ *)
        (* proving impl_nw can deq which is trivial *)
        2:{
          apply app_inj_tail in H2.
          destruct H2.
          light_clean_propagate. 
          rm_existentials.
          split; [eauto | split].
          eauto.
          split.
          clear_trivial_wpa_step.
          split; [eauto | clear_trivial_evar].
          apply_log_fn 2%nat.
          lia.
        }

        (* there's some problem with this tactic with fiber in the goal *)
        (* make sure it only substitute hypotheses *)
        Ltac fast_subst ::=
          try
          match goal with
          | H:?a = ?b |- _ => is_var a; subst a
          | H:?a = ?b |- _ => is_var b; subst b
          | H:?a ?x = ?b |- _ => is_var a; is_var x; rewrite H in *|-
        end.

        (* applying enq horizontally *)
        eapply enq.
        all: cycle 1.
        intros.
        (* specialize inductive hypothesis with the tag from horizontal enq *)
        (* and get all necessary information in hypotheses through symbolic execution *)
        (* so that we can prove it's possible to enq at impl_sw and spec_sw *)
        specialize (H0 x1 tag3).
        light_clean_propagate.
        unify_equality.
        extract_all_fnequality.
        light_clean_propagate.
        symb_ex_split.
        merge_simpl.
        extract_all_fnequality.
        prove_precond HB3.
        2:{
          rm_existentials.
          rewrite HA5.
          split; wrapped_arrays_equal 2%nat.
        }
        split.
        (* proving enq is available at impl_sw and spec_sw *)
        2:{
          (* impl_sw *)
          rm_existentials.
          split.
          2:{
            apply app_inj_tail in H4.
            light_clean_propagate.
            rm_existentials.
            split.
            rm_existentials.
            split; [eauto | split].
            2:{
              rewrite map_app in HA9.
              rewrite app_comm_cons in HA9.
              apply NoDup_app_remove_r in HA9.
              rewrite map_app in HA14.
              apply NoDup_app_remove_r in HA14.
              split.
              clear_trivial_wpa_step.
              merge_simpl.
              simpl.
              1-3: repeat clear_trivial_evar.
              let y := eexists_st_array 2%nat in instantiate (1 := y).
              instantiate (
                3 := [| 
                  {| gen_m.module_state := gen_m.req sm x1; gen_m.inp := gen_m.Done |};
                  b0;
                  m.InFlight tag4 x1
                |]
              ).
              instantiate (1 := inflight tag4 :: l3).
              apply_log_fn 2%nat.
              intros.
              clear_trivial_evar.
              destruct i.
              intros.
              simpl.
              clear_trivial_evar.
              lia.
            }
            instantiate (1 := fun x tag =>
            *[| 
              [| 
                {| gen_m.module_state := gen_m.req module_state x; gen_m.inp := gen_m.Done |};
                bag;
                m.InFlight tag x
              |];
              inflight tag :: l0
            |]*
            ).
            simpl.
            eauto.

            (* spec_sw *)
            rm_existentials.
            assumption.
            assumption.
            repeat clear_trivial_evar.
            instantiate (1 := fun x =>
            *[|
              {| gen_m.module_state := gen_m.deq (gen_m.req module_state0 x); gen_m.inp := gen_m.None |};
              _ 
            |]*
            ).
            simpl.
            eauto.
          }
          simpl.
          eauto.
        }
        simpl.
        (* specialize lock_step as deq to get ϕ impl_se spec_se *)
        specialize (HB3 1%nat).
        unfold lock_step in HB3.
        specialize (HB3 0 
          *[|
            [| {| gen_m.module_state := gen_m.req sm x1; gen_m.inp := gen_m.Done |}; b0; m.InFlight tag4 x1 |]; 
            inflight tag4 :: l0
          |]*
        ).
        prove_precond HB3.
        simpl in *.
        light_clean_propagate.
        apply app_inj_tail in H2.
        light_clean_propagate.
        symb_ex_split.
        extract_all_fnequality.
        rewrite app_comm_cons in H2.
        apply app_inj_tail in H2.
        light_clean_propagate.
        eauto.

        (* precondition for lock_step *)
        (* proving deq is possible at impl_nw which trivial (from vertical deq) *)
        simpl.
        rm_existentials.
        split; [eauto | split].
        eauto.
        split.
        clear_trivial_wpa_step.
        rewrite app_comm_cons.
        split; [eauto | clear_trivial_evar].
        simpl.
        apply_log_fn 2%nat.
        destruct i.
        intros.
        simpl.
        rewrite app_comm_cons.
        clear_trivial_evar.
        lia.

        (* proving impl_sw ≺ spec_sw *)
        prove_indistinguishable.
        (* vm: first *)
        (* it's given that first is available at impl_sw                      *)
        (* and ϕ impl_se spec_se -> impl_se ≺ spec_se,                        *)
        (* -> first is also available at impl_se                              *)
        (* -> there are at least 2 elements (inflight/completed) in CB        *)
        (* -> there are at least 2 elements ready to be dequeued in spec side *)
        {
          light_clean_propagate.
          symb_ex_split.
          apply app_inj_tail in H4.
          light_clean_propagate.
          rewrite HA6 in HB1.
          light_clean_propagate.
          specialize (H0 0 0).
          light_clean_propagate.
          extract_all_fnequality.
          unify_equality.
          symb_ex_split.
          merge_simpl.
          extract_all_fnequality.
          prove_precond HB3; [ | clear_trivial_evar].
          specialize (HB3 1%nat).
          unfold lock_step in HB3.
          specialize (HB3 0 *[| 
          [| {| gen_m.module_state := gen_m.req sm 0; gen_m.inp := gen_m.Done |}; b0; m.InFlight 0 0 |]; 
          inflight 0 :: (l4 ++ [completed tag3 n3]) |]*).
          prove_precond HB3.
          2:{
            simpl.
            rm_existentials.
            split; eauto.
            split; [eauto | split].
            clear_trivial_wpa_step.
            rewrite app_comm_cons.
            split; [eauto | clear_trivial_evar].
            apply_log_fn 2%nat.
            destruct i.
            intros.
            simpl.
            rewrite app_comm_cons.
            clear_trivial_evar.
            lia.
          }
          simpl in *.
          light_clean_propagate.
          unify_equality.
          extract_all_fnequality.
          rewrite app_comm_cons in H4.
          apply app_inj_tail in H4.
          light_clean_propagate.
          pose proof (HB6).
          apply ϕ_implies_indistinguishable in H0.
          unfold indistinguishable in H0.
          cleanup.
          specialize (H0 0 0%nat n3).
          simpl in H0.
          prove_precond H0.
          light_clean_propagate.
          extract_all_fnequality.
          symb_ex_split.

          (* there are at least 2 elements (inflight/completed) in impl side *)
          (* -> there are at least 2 elements ready to be dequeued in spec side *)
          assert (exists n l, l2 = l ++ [n]).
          {
            assert (related 
              *[| 
                [| {| gen_m.module_state := gen_m.req sm 0; gen_m.inp := gen_m.Done |}; bag; m.InFlight 0 0 |];
                inflight 0 :: l4 ++ [completed tag3 n3]
              |]*
              *[| 
                {| gen_m.module_state := gen_m.deq (gen_m.req sm1 0); gen_m.inp := gen_m.None |};
                gen_m.get_resp (gen_m.req sm1 0) :: l2 
              |]*
            )
            by repeat clear_trivial_evar.
            eapply ϕ_implies_eq_size in H0.
            light_clean_propagate.
            extract_all_fnequality.
            destruct l2.

            (* l2 cannot be empty *)
            simpl in HB3.
            rewrite app_length in HB3.
            simpl in HB3.
            lia.

            (* l0 cannot be empty when l2 has at least 1 element *)
            destruct l0.
            inversion H5.
            rewrite <- app_comm_cons in H5.
            apply (f_equal (@tail N)) in H5.
            simpl in H5.
            eauto.
          }
          light_clean_propagate.
          rewrite app_comm_cons in H5.
          apply app_inj_tail in H5.
          light_clean_propagate.
          repeat clear_trivial_evar.
          rm_existentials.
          split; [eauto | reconstruct_step].
          rewrite app_comm_cons.
          split; [eauto | clear_trivial_evar].
        }
        (* am: enq *)
        (* deq doesn't affect internal module state         *)
        (* enq is available at impl_sw and                  *)
        (* impl_nw ≺ spec_nw -> enq is available at spec_nw *)
        (* -> available at spec_sw                          *)
        {
          specialize (H0 0 0).
          light_clean_propagate.
          extract_all_fnequality.
          simpl.
          rm_existentials.
          assumption.
          assumption.
          repeat clear_trivial_evar.
        }
        (* am: deq *)
        (* similar to first *)
        {
          light_clean_propagate.
          symb_ex_split.
          specialize (H0 0 0).
          light_clean_propagate.
          extract_all_fnequality.
          unify_equality.
          symb_ex_split.
          extract_all_fnequality.
          merge_simpl.
          prove_precond HB5; [ | clear_trivial_evar].
          specialize (HB5 1%nat).
          unfold lock_step in HB5.
          specialize (HB5 0 
          *[| [| {| gen_m.module_state := gen_m.req sm 0; gen_m.inp := gen_m.Done |}; b0;  m.InFlight 0 0 |];
          inflight 0 :: l0 |]*).
          prove_precond HB5.
          2:{
            simpl.
            rm_existentials.
            split; [eauto | split].
            eauto.
            split.
            clear_trivial_wpa_step.
            rewrite app_comm_cons.
            split; [eauto | clear_trivial_evar].
            apply_log_fn 2%nat.
            destruct i.
            intros.
            simpl.
            rewrite app_comm_cons.
            clear_trivial_evar.
            lia.
          }
          simpl in H1.
          light_clean_propagate.
          symb_ex_split.
          apply app_inj_tail in H4.
          light_clean_propagate.
          extract_all_fnequality.
          apply app_inj_tail in H1.
          light_clean_propagate.
          pose proof HB4.
          eapply ϕ_implies_indistinguishable in HB4.
          unfold indistinguishable in HB4.
          cleanup.
          specialize (H4 0 1%nat 
          *[| [| {| gen_m.module_state := gen_m.req sm 0; gen_m.inp := gen_m.Done |}; b0; m.InFlight 0 0 |];
          inflight 0 :: l5 |]*).
          simpl in H4.
          light_clean_propagate.
          prove_precond H4.
          2:{
            rm_existentials.
            split; [eauto | split].
            eauto.
            split.
            clear_trivial_wpa_step.
            rewrite app_comm_cons.
            split; [eauto | clear_trivial_evar].
            apply_log_fn 2%nat.
            destruct i.
            simpl.
            intros.
            rewrite app_comm_cons.
            clear_trivial_evar.
            lia.
          }
          light_clean_propagate.
          extract_all_fnequality.
          unify_equality.
          extract_all_fnequality.
          assert (exists l, l2 = l ++ [x2]).
          {
            assert (related 
              *[| [| {| gen_m.module_state := gen_m.req sm 0; gen_m.inp := gen_m.Done |}; bag; m.InFlight 0 0 |];
              inflight 0 :: l5 ++ [completed tag3 n3] |]* 
              *[| {| gen_m.module_state := gen_m.deq (gen_m.req sm1 0); gen_m.inp := gen_m.None |}; l0 ++ [x2] |]*
            )
            by repeat clear_trivial_evar.
            apply ϕ_implies_eq_size in H4.
            light_clean_propagate.
            extract_all_fnequality.
            rewrite app_comm_cons in H7.
            apply app_inj_tail in H7.
            light_clean_propagate.
            destruct l0.
            simpl in HB9.
            rewrite app_length in HB9.
            simpl in HB9.
            lia.
            
            destruct l6.
            inversion H10.
            apply (f_equal (@tail N)) in HA0.
            simpl in HA0.
            eauto. 
          }
          light_clean_propagate.
          clear_trivial_evar.
        }
      }
      destruct i.
      (* complete *)
      (* enq-complete in the upper corner            *)
      (* complete-enq in the lower corner            *)
      (* 1. Take the tag in the lower enq and use it *)
      (*    to specialize inductive hypothesis       *)
      (* 2. Do lock_step complete                    *)
      {
        (* symbolically executing complete in impl-side vertically *)
        intros.
        light_clean_propagate.
        destruct m_state_i.
        destruct m_state_s.
        symb_ex_split.
        merge_simpl.
        extract_all_fnequality.

        (* applying enq horizontally *)
        eapply enq.
        all: cycle 1.
        (* specialize inductive hypothesis with the tag from horizontal enq *)
        (* and get all necessary information in hypotheses through symbolic execution *)
        (* so that we can prove it's possible to enq at impl_sw and spec_sw *)
        intros.
        specialize (H0 x tag).
        light_clean_propagate.
        extract_all_fnequality.
        symb_ex_split.
        extract_all_fnequality.
        merge_simpl.
        prove_precond HB3; [ | clear_trivial_evar].
        specialize (HB3 2%nat).
        unfold lock_step in HB3.
        unify_equality.
        extract_all_fnequality.
        specialize (HB3 
        *[| [| {| gen_m.module_state := gen_m.req sm x; gen_m.inp := gen_m.Done |}; remm b1 k; m.InFlight tag0 x |]; 
        inflight tag0 :: l1 ++ completed k v1 :: l2 |]*).
        apply unique_partition' in H4; eauto.
        light_clean_propagate.
        prove_precond HB3.
        (* proving complete is possible at impl_ne *)
        (* which is trivial from the other vertical complete *)
        2:{
          rm_existentials.
          split; [eauto | split].
          eauto.
          split.
          clear_trivial_wpa_step.
          1-3: split; [eauto | try rewrite app_comm_cons; clear_trivial_evar].
          apply_log_fn 2%nat.
          intros.
          simpl.
          rm_existentials.
          merge_simpl.
          split; [eauto | split; eauto].
          destruct i.
          simpl.
          intros.
          rewrite app_comm_cons.
          clear_trivial_evar.
          lia.
        }
        split.
        all: cycle 1.
        (* proving enq is possible at impl_sw and spec_sw *)
        rm_existentials.
        split.
        2:{
          split.
          rm_existentials.
          split; [eauto | split].
          2:{
            rewrite tag_inflight_completed with (v := v1) in HA15.
            rewrite tag_inflight_completed with (v := v1) in HA19.
            apply remm_get with (k := k) in HA18.
            rewrite tag_inflight_completed with (v := v1) in HA20.
            split.
            clear_trivial_wpa_step.
            1-3: split; [eauto | clear_trivial_evar].
            simpl.
            let y := eexists_st_array 2%nat in instantiate (1 := y).
            instantiate (3 := 
            [| {| gen_m.module_state := gen_m.req sm x ; gen_m.inp := gen_m.Done |}; 
            remm b1 k; m.InFlight tag0 x |]).
            apply_log_fn 2%nat.
            intros.
            clear_trivial_evar.
            destruct i.
            simpl.
            intros.
            clear_trivial_evar.
            lia.
          }
          instantiate (1 := fun x tag => 
            *[| 
              [|
                {| gen_m.module_state := gen_m.req module_state x; gen_m.inp := gen_m.Done |};
                remm b k;
                m.InFlight tag x
              |]; 
              inflight tag :: l0 ++ completed k v :: l3 
            |]*
          ).
          simpl.
          eauto.
          rm_existentials.
          assumption.
          assumption.
          repeat clear_trivial_evar.
        }
        simpl.
        eauto.
        unify_equality.

        (* proving impl_sw ≺ spec_sw *)
        (* overall: the proof is similar to the case where enq-deq *)
        prove_indistinguishable.
        (* vm: first *)
        (* it's given that first is available at impl_sw *)
        (* and ϕ impl_se spec_se -> impl_se ≺ spec_se, *)
        (* -> first is also available at impl_se *)
        (* -> there are at least 2 elements (inflight/completed) in CB *)
        (* -> there are at least 2 elements ready to be dequeued in spec side *)
        {
          simpl.
          light_clean_propagate.
          symb_ex_split.
          specialize (H0 0 0).
          light_clean_propagate.
          extract_all_fnequality.
          unify_equality.
          light_clean_propagate.
          symb_ex_split.
          merge_simpl.
          extract_all_fnequality.
          apply unique_partition' in H4; eauto.
          light_clean_propagate.
          prove_precond HB3; [ | clear_trivial_evar].
          specialize (HB3 2%nat).
          unfold lock_step in HB3.
          specialize (HB3 *[| [| {| gen_m.module_state := gen_m.req sm 0; gen_m.inp := gen_m.Done |}; 
          remm b1 k; m.InFlight 0 0 |];
          inflight 0 :: l0 ++ completed k v1 :: l3 |]*).
          simpl in HB3.
          extract_all_fnequality.
          prove_precond HB3.
          2:{
            rm_existentials.
            split; [eauto | split].
            eauto.
            split.
            clear_trivial_wpa_step.
            1-3: split; [eauto | try rewrite app_comm_cons; clear_trivial_evar].
            apply_log_fn 2%nat.
            intros.
            clear_trivial_evar.
            destruct i.
            simpl.
            intros.
            rewrite app_comm_cons.
            clear_trivial_evar.
            lia.
          }
          light_clean_propagate.
          symb_ex_split.
          merge_simpl.
          unify_equality.
          extract_all_fnequality.
          symb_ex_split.
          extract_all_fnequality.
          merge_simpl.
          pose proof (HB3).
          apply ϕ_implies_indistinguishable in H0.
          unfold indistinguishable in H0.
          cleanup.
          specialize (H0 0 0%nat n).
          simpl in H0.
          prove_precond H0.
          light_clean_propagate.
          symb_ex_split.
          unify_equality.
          extract_all_fnequality.
          (* there are at least 2 elements in the list *)
          (* -> there must be at least 1 element in l6 *)
          assert (exists l, l6 = l ++ [n]).
          {
            assert (related 
              *[|
                [| {| gen_m.module_state := gen_m.req sm 0; gen_m.inp := gen_m.Done |}; remm b k; m.InFlight 0 0 |];
                inflight 0 :: l0 ++ completed k v1 :: l3
              |]* 
              (sst 0)
            ).
            {
              simpl.
              rm_existentials.
              split; [eauto | clear_trivial_evar].
            }
            apply ϕ_implies_eq_size in H0.
            light_clean_propagate.
            unify_equality.
            extract_all_fnequality.
            destruct l6.
            simpl in HB5.
            rewrite app_length in HB5.
            simpl in HB5.
            lia.

            destruct l.
            inversion H9.
            rewrite <- app_comm_cons in H9.
            apply (f_equal (@tail N)) in H9.
            simpl in H9.
            eauto.
          }
          light_clean_propagate.
          clear_trivial_evar.
          rm_existentials.
          split; [eauto | reconstruct_step].
          rewrite H1.
          rewrite app_comm_cons.
          split; [eauto | clear_trivial_evar].
        }
        (* am: enq *)
        (* trivial since spec_nw can enq *)
        {
          specialize (H0 0 0).
          light_clean_propagate.
          extract_all_fnequality.
          simpl.
          rm_existentials.
          assumption.
          assumption.
          repeat clear_trivial_evar.
        }
        (* am: deq *)
        (* similar to the proof for first *)
        {
          light_clean_propagate.
          symb_ex_split.
          specialize (H0 0 0).
          light_clean_propagate.
          extract_all_fnequality.
          unify_equality.
          symb_ex_split.
          merge_simpl.
          extract_all_fnequality.
          prove_precond HB5; [ | clear_trivial_evar].
          specialize (HB5 2%nat).
          unfold lock_step in HB5.
          specialize (HB5
          *[| [| {| gen_m.module_state := gen_m.req sm 0; gen_m.inp := gen_m.Done |}; remm b1 k;  m.InFlight 0 0 |];
          (inflight 0 :: l1) ++ completed k v1 :: l2 |]*).
          prove_precond HB5.
          2:{
            simpl.
            rm_existentials.
            split; [eauto | split].
            eauto.
            split.
            clear_trivial_wpa_step.
            1-3: split; [eauto | try rewrite app_comm_cons; clear_trivial_evar].
            merge_simpl.
            simpl.
            apply_log_fn 2%nat.
            intros.
            clear_trivial_evar.
            destruct i.
            simpl.
            intros.
            simpl.
            rewrite app_comm_cons.
            clear_trivial_evar.
            lia.
          }
          light_clean_propagate.
          unify_equality.
          extract_all_fnequality.
          symb_ex_split.
          merge_simpl.
          apply unique_partition' in H4; eauto.
          light_clean_propagate.
          unify_equality.
          extract_all_fnequality.
          pose proof HB5.
          eapply ϕ_implies_indistinguishable in HB5.
          unfold indistinguishable in HB5.
          cleanup.
          specialize (H5 0 1%nat 
          *[| [| {| gen_m.module_state := gen_m.req sm 0; gen_m.inp := gen_m.Done |}; remm b0 k; m.InFlight 0 0 |];
          inflight 0 :: l4 |]*).
          simpl in H5.
          prove_precond H5.
          2:{
            rewrite H2.
            rm_existentials.
            split; [eauto | split].
            eauto.
            split.
            clear_trivial_wpa_step.
            rewrite app_comm_cons.
            split; [eauto | clear_trivial_evar].
            apply_log_fn 2%nat.
            destruct i.
            simpl.
            intros.
            rewrite app_comm_cons.
            clear_trivial_evar.
            lia.
          }
          unify_equality.
          extract_all_fnequality.
          assert (exists x l, l7 = l ++ [x]).
          {
            assert (related 
            *[|
              [| {| gen_m.module_state := gen_m.req sm 0; gen_m.inp := gen_m.Done |}; remm b0 k; m.InFlight 0 0 |];
              inflight 0 :: l0 ++ completed k v1 :: l3
            |]*
            (sst 0)).
            {
              simpl.
              split; [eauto | clear_trivial_evar].
            }
            unify_equality.
            extract_all_fnequality.
            apply ϕ_implies_eq_size in H5.
            light_clean_propagate.
            unify_equality.
            extract_all_fnequality.
            destruct l7.
            rewrite app_comm_cons in HB8.
            rewrite app_length in HB8.
            simpl in HB8.
            lia.

            destruct l.
            inversion H7.
            rewrite <- app_comm_cons in H7.
            apply (f_equal (@tail N)) in H7.
            simpl in H7.
            eauto. 
          }
          light_clean_propagate.
          rm_existentials.
          split; eauto.
        }
        simpl.
        unify_equality.
        rewrite HB4.
        eauto.
      }
      (* complete_m *)
      (* can't do complete_m and enq at one state *)
      (* -> contradiction *)
      destruct i.
      {
        unfold lift_to.
        intros.
        light_clean_propagate.
        specialize (H0 0 0).
        light_clean_propagate.
        extract_all_fnequality.
        symb_ex_split.
        extract_all_fnequality.
      }
      unfold lock_step.
      eauto.
    }
    (* deq case *)
    {
      unfold lock_step.
      simpl.
      destruct i.
      (* enq *)
      (* due to non-determinism within enq *)
      (* use the tag from the left enq to specialize lock_step enq *)
      (* -> deq-enq and enq-deq reconverge *)
      {
        (* symbolically executing deq horizontally *)
        (* and enq vertically in the impl-side *)
        intros.
        simpl in *|-.
        light_clean_propagate.
        extract_all_fnequality.
        symb_ex_split.
        extract_all_fnequality.
        merge_simpl.

        (* get the lock_step from inductive hypothesis *)
        (* and all the associated information through symbolic execution *)
        (* to avoid problems with context when instantiating evars later *)
        prove_precond IHϕ.
        light_clean_propagate.
        extract_all_fnequality.
        simpl in *.
        light_clean_propagate.
        extract_all_fnequality.
        specialize (IHϕ 0%nat). (* specialize lock_step to be enq *)
        unfold lock_step in IHϕ.
        simpl in IHϕ.
        (* important: the tag here is the tag introduced by the previous vertical enq *)
        (* this state can be derived from nxt_st by removing the last element from the CB *)
        specialize (IHϕ x0 
        *[| [| {| gen_m.module_state := gen_m.req sm x0; gen_m.inp := gen_m.Done |}; bag; m.InFlight tag x0 |];
        inflight tag :: l1 |]*).
        prove_precond IHϕ.
        light_clean_propagate.
        extract_all_fnequality.
        symb_ex_split.
        extract_all_fnequality.
        merge_simpl.

        (* proving enq is possible at spec_nw *)
        (* which is provable given we have lock_step enq *)
        unfold indistinguishable in H.
        cleanup.
        rm_existentials.
        split.
        rm_existentials.
        assumption.
        assumption.
        split; [eauto | repeat clear_trivial_evar].
        (* applying deq horizontally *)
        eapply deq.
        all: cycle 1.
        (* proving impl_sw ≺ spec_sw *)
        {
          prove_indistinguishable.
          (* vm: first *)
          (* trivial to prove since deq is available at nw *)
          {
            symb_ex_split.
            specialize (H 0 0%nat n1).
            prove_precond H.
            simpl in H5.
            light_clean_propagate.
            symb_ex_split.
            extract_all_fnequality.
            apply app_inj_tail in H10.
            light_clean_propagate.
            rm_existentials.
            rewrite app_comm_cons.
            split; eauto.
            simpl.
            rm_existentials.
            split; [eauto | ].
            reconstruct_step.
            split; [eauto | rm_existentials].
            unify_equality.
            rewrite app_comm_cons in H8.
            apply app_inj_tail in H8.
            light_clean_propagate.
            inversion HB1.
            light_clean_propagate.
            split; eauto.
          }
          (* am: enq *)
          (* impl can't enq back to back *)
          (* -> contradiction *)
          (* since we have all information of spec with the vertical enq *)
          (* we know enq is available at spec_sw *)
          {
            rm_existentials.
            simpl.
            rm_existentials.
            assumption.
            assumption.
            split.
            wrapped_arrays_equal 2%nat.
            repeat (split; eauto; rm_existentials).
          }
          (* am: deq *)
          (* trivial since deq is available at spec_nw *)
          {
            simpl.
            rewrite app_comm_cons.
            rm_existentials.
            split; eauto.
          }
        }
        {
          simpl.
          rm_existentials.
          split; eauto.
          split.
          2:{
            split.
            clear_trivial_wpa_step.
            rewrite app_comm_cons in HB4.
            split; [eauto | clear_trivial_evar].
            let y := eexists_st_array 2%nat in instantiate (1 := y).
            apply_log_fn 2%nat.
            intros.
            rm_existentials.
            rewrite app_comm_cons in HB4.
            apply app_inj_tail in H4.
            light_clean_propagate.
            split; eauto.
            lia.
          }
          eauto.
        }

        (* proving deq is possible at spec_sw *)
        (* which is trivial since deq is possible at spec_nw *)
        {
          simpl.
          rm_existentials.
          rewrite app_comm_cons.
          split; eauto.
        }
        (* preconditions *)
        {
          apply app_inj_tail in H4.
          rewrite map_app in HA3.
          rewrite app_comm_cons in HA3.
          apply NoDup_app_remove_r in HA3.
          light_clean_propagate.
          rm_existentials.
          split; [eauto | rm_existentials].
          split.
          eauto.
          rewrite map_app in HA9.
          apply NoDup_app_remove_r in HA9.
          split.
          clear_trivial_wpa_step.
          1-3: split; [eauto | clear_trivial_evar].
          apply_log_fn 2%nat.
          intros.
          clear_trivial_evar.
        }
        {
          assert (nxt_st0 = 
          [| [| {| gen_m.module_state := sm; gen_m.inp := gen_m.None |}; b; m.NoneB |]; l1 |]) by custom_eq_array 2%nat.
          light_clean_propagate.
          rm_existentials.
          split; [wrapped_arrays_equal 2%nat | eauto].
        }
        (* ϕ follows *)
        eauto.
      }
      destruct i.
      (* deq *)
      (* trivial to prove since 2 deqs simply converge *)
      {
        intros.
        simpl in *.
        light_clean_propagate.
        extract_all_fnequality.
        symb_ex_split.
        rm_existentials.
        split.
        rm_existentials.
        split; eauto.
        apply app_inj_tail in H3.
        apply app_inj_tail in H4.
        light_clean_propagate.
        eauto.
        assert (nxt_st = [| [| m_state_i; bag; inp |]; l2 |]) by custom_eq_array 2%nat.
        assert (nxt_st = nxt_st0).
        {
          light_clean_propagate.
          custom_eq_array 2%nat.
          rewrite HA4.
          eauto.
        }
        light_clean_propagate.
        eauto.
      }
      (* complete *)
      (* deq-complete and complete-deq converge *)
      (* conceptually this case is easy to prove *)
      (* but since it involves completing an element in between 2 lists *)
      (* it's tricky to keep everything in place *)
      destruct i.
      {
        (* symoblically executing deq horizontally *)
        (* and complete vertically in impl-side vertically *)
        intros.
        simpl in *|-.
        light_clean_propagate.
        extract_all_fnequality.
        symb_ex_split.
        merge_simpl.
        extract_all_fnequality.

        (* get lock_step from inductive hypothesis *)
        prove_precond IHϕ.
        light_clean_propagate.
        extract_all_fnequality.
        specialize (IHϕ 2%nat). (* specialize lock_step to be complete *)
        unfold lock_step in IHϕ.
        apply unique_partition' in H6; eauto.
        light_clean_propagate.
        pose proof H5 as tmp.
        apply after_inflight_completed_tail in tmp.
        light_clean_propagate.
        rewrite app_comm_cons in HB4.
        rewrite app_assoc in HB4.
        rewrite app_comm_cons in H5.
        rewrite app_assoc in H5.
        apply app_inj_tail with (a := completed tag0 n0) (b := completed tag0 n0) in H5.
        light_clean_propagate.
        rewrite app_comm_cons in HA11.
        rewrite app_assoc in HA11.
        rewrite map_app in HA11.
        apply NoDup_app_remove_r in HA11.

        (* applying deq horizontally *)
        eapply deq.
        all: cycle 1.
        (* proving impl_sw ≺ spec_sw *)
        {
          prove_indistinguishable.
          (* vm: first *)
          (* trivial since deq is available at spec_nw *)
          {
            light_clean_propagate.
            simpl.
            unfold indistinguishable in H.
            cleanup.
            specialize (H 0 0%nat n0).
            simpl in H.
            prove_precond H.
            light_clean_propagate.
            extract_all_fnequality.
            apply app_inj_tail in H3.
            light_clean_propagate.
            symb_ex_split.
            extract_all_fnequality.
            unify_equality.
            apply app_inj_tail in H3.
            light_clean_propagate.
            inversion HB0.
            light_clean_propagate.
            rm_existentials.
            split; eauto.
            symb_ex_split.
            extract_all_fnequality.
            rm_existentials.
            rewrite app_comm_cons.
            rewrite app_assoc.
            split; [eauto | clear_trivial_wpa_step].
            split; [eauto | clear_trivial_evar].
          }
          (* am: enq *)
          (* ϕ impl_se spec_se -> impl_se ≺ spec_se *)
          (* given the availability of enq at impl_sw *)
          (* -> enq is available at spec_sw *)
          {
            symb_ex_split.
            extract_all_fnequality.
            merge_simpl.
            unify_equality.
            extract_all_fnequality.
            specialize (IHϕ *[| 
              [| {| gen_m.module_state := sm0; gen_m.inp := gen_m.None |}; remm bag k; m.NoneB |];
              l4 ++ completed k v1 :: l0 
            |]*
            ).
            prove_precond IHϕ.
            light_clean_propagate.
            symb_ex_split.
            merge_simpl.
            extract_all_fnequality.
            apply ϕ_implies_indistinguishable in IHϕ.
            unfold indistinguishable in IHϕ.
            cleanup.
            specialize (H2 0 0%nat 
            *[| [| {| gen_m.module_state := gen_m.req sm0 0; gen_m.inp := gen_m.Done |}; remm b k; m.InFlight tag1 0 |];
            inflight tag1 :: l4 ++ completed k v1 :: l0|]*).
            prove_precond H2.
            2:{
              simpl.
              unify_equality.
              rewrite map_app in HA14.
              rewrite app_comm_cons in HA14.
              apply NoDup_app_remove_r in HA14.
              rewrite map_app in HA20.
              apply NoDup_app_remove_r in HA20.
              rm_existentials.
              split; [eauto | split].
              eauto.
              split.
              clear_trivial_wpa_step.
              1-3: split; [eauto | clear_trivial_evar].
              apply_log_fn 2%nat.
              intros.
              clear_trivial_evar.
            }
            light_clean_propagate.
            extract_all_fnequality.
            rm_existentials.
            assumption.
            assumption.
            split; [eauto | repeat clear_trivial_evar].
            rm_existentials.
            split; [eauto | split].
            eauto.
            split.
            clear_trivial_wpa_step.
            1-3: split; [eauto | clear_trivial_evar].
            apply_log_fn 2%nat.
            1-2: intros; clear_trivial_evar.
          }
          (* am: deq *)
          (* trivial since deq is available at nw *)
          {
            simpl.
            rm_existentials.
            split; eauto.
          }
        }
        (* proving deq is available at impl_sw and spec_sw *)
        (* which is trivial since deq is available at nw *)
        {
          simpl.
          rm_existentials.
          split; [eauto | split].
          2:{
            split.
            clear_trivial_wpa_step.
            split; [eauto | clear_trivial_evar].
            let y := eexists_st_array 2%nat in instantiate (1 := y).
            apply_log_fn 2%nat.
            lia.
          }
          eauto.
        }
        {
          simpl.
          clear_trivial_evar.
        }
        (* precondition *)
        {
          rm_existentials.
          split; [wrapped_arrays_equal 2%nat | eauto].
        }
        (* specialize lock_step with the state obtained from the lower deq *)
        (* so that two paths converge *)
        unify_equality.
        light_clean_propagate.
        specialize (IHϕ *[| [| ms0; remm b k; inp0 |]; l4 ++ completed k v1 :: l0 |]*).
        simpl in *.
        light_clean_propagate.
        extract_all_fnequality.
        prove_precond IHϕ.
        eauto.

        (* precondition *)
        clear_trivial_evar.
        split; [eauto | ].
        split.
        clear_trivial_wpa_step.
        1-3: split; [eauto | clear_trivial_evar].
        merge_simpl.
        simpl.
        apply_log_fn 2%nat.
        1-2: intros; clear_trivial_evar.
      }
      destruct i.
      (* complete_m *)
      (* deq-complete_m and complete_m-deq simply converge *)
      (* no non-determinism *)
      {
        (* symbolically executing deq horizontally *)
        (* and destructing hypotheses related to vertical complete_m *)
        (* state transition in impl-side *)
        unfold lift_to.
        intros.
        simpl in *.
        light_clean_propagate.
        extract_all_fnequality.
        symb_ex_split.
        extract_all_fnequality.
        merge_simpl.

        (* get lock_step from inductive hypothesis *)
        prove_precond IHϕ.
        light_clean_propagate.
        extract_all_fnequality. 
        specialize (IHϕ 3%nat). (* specialize lock_step to be complete_m *)
        unfold lock_step in IHϕ.
        specialize (IHϕ *[| 
        [| 
          {| gen_m.module_state := gen_m.deq sm; gen_m.inp := gen_m.None |};
          setm b tag (gen_m.get_resp sm); m.NoneB 
        |];
        l1 |]*).
        prove_precond IHϕ.
        unfold lift_to in H1.
        light_clean_propagate.
        merge_simpl.
        extract_all_fnequality.

        (* applying deq horizontally *)
        eapply deq.
        all: cycle 1.
        (* proving impl_sw ≺ spec_sw *)
        {
          unfold indistinguishable in H.
          cleanup.
          prove_indistinguishable.
          (* vm: first *)
          (* trivial since first is available at impl_sw *)
          (* and complete_m doesn't reduce number of elements ready *)
          (* in the list -> deq is available at spec_sw *)
          {
            light_clean_propagate.
            symb_ex_split.
            extract_all_fnequality.
            specialize (H 0 0%nat n1).
            simpl in H.
            prove_precond H.
            light_clean_propagate.
            extract_all_fnequality.
            symb_ex_split.
            apply app_inj_tail in H8.
            light_clean_propagate.
            clear_trivial_evar.
            rm_existentials.
            split; [eauto | clear_trivial_wpa_step].
            apply app_inj_tail in H6.
            light_clean_propagate.
            inversion HB.
            split; [eauto | clear_trivial_evar].
          }
          (* am: enq *)
          (* since complete_m imples no transition for spec side *)
          (* we have to get the information for spec side from right lower corner *)
          (* ϕ impl_se spec_se -> impl_se ≺ spec_se *)
          (* given enq is available at impl_sw -> enq is also available at spec_sw *)
          {
            light_clean_propagate.
            symb_ex_split.
            merge_simpl.
            extract_all_fnequality.
            apply ϕ_implies_indistinguishable in IHϕ.
            unfold indistinguishable in IHϕ.
            cleanup.
            apply app_inj_tail in H3.
            light_clean_propagate.
            specialize (H7 0 0%nat *[| [| {| gen_m.module_state := gen_m.req (gen_m.deq sm0) 0; gen_m.inp := gen_m.Done |};
            setm b0 tag2 (gen_m.get_resp sm0); m.InFlight tag3 0 |];
            inflight tag3 :: cb |]*).
            prove_precond H7.
            light_clean_propagate.
            extract_all_fnequality.
            rm_existentials.
            assumption.
            assumption.
            split;[eauto | repeat clear_trivial_evar].
            simpl.
            rewrite map_app in HA9.
            rewrite app_comm_cons in HA9.
            apply NoDup_app_remove_r in HA9.
            rewrite map_app in HA12.
            apply NoDup_app_remove_r in HA12.
            rm_existentials.
            split; [eauto | split].
            eauto.
            split.
            clear_trivial_wpa_step.
            1-3: split; [eauto | clear_trivial_evar].
            apply_log_fn 2%nat.
            intros.
            clear_trivial_evar.
          }
          (* am: deq *)
          (* trivial since deq is already available at spec_nw *)
          (* and complete_m implies no transition for spec side *)
          {
            simpl.
            rm_existentials.
            split; [wrapped_arrays_equal 2%nat | eauto].
          }
        }
        (* proving deq is available at impl_sw and spec_sw *)
        (* which is trivial since deq is available at nw *)
        {
          simpl.
          rm_existentials.
          split; [eauto | split].
          2:{
            split.
            clear_trivial_wpa_step.
            split; [eauto | clear_trivial_evar].
            let y := eexists_st_array 2%nat in instantiate (1 := y).
            apply_log_fn 2%nat.
          }
          eauto.
        }
        {
          simpl.
          clear_trivial_evar.
        }

        (* preconditions *)
        unfold lift_to.
        rm_existentials.
        split; eauto.
        rm_existentials.
        split.
        2:{
          simpl.
          rm_existentials.
          assumption.
          assumption.
          split.
          eauto.
          clear_trivial_evar.
        }
        apply app_inj_tail in H3.
        light_clean_propagate.
        wrapped_arrays_equal 2%nat.
        rm_existentials.
        split; [wrapped_arrays_equal 2%nat | eauto].
        apply app_inj_tail in H3.
        light_clean_propagate.
        eauto.
      }
      unfold lock_step.
      eauto.
    }
    (* complete case *)
    (* there's non-determinism within complete too *)
    (* but for all cases, we are free to choose a state *)
    (* to match non-determinism *)
    {
      simpl in H2.
      unfold lock_step.
      destruct i.
      (* enq *)
      (* complete-enq and enq-complete converge when we pick *)
      (* the tag in the lock_step to be the tag introduced *)
      (* by the left vertical enq *)
      {
        (* symbolically executing complete horizontally *)
        (* and enq in impl-side vertically *)
        simpl.
        intros.
        light_clean_propagate.
        symb_ex_split.
        extract_all_fnequality.
        merge_simpl.

        (* proving enq is available at spec_nw *)
        (* since complete in impl-side implies no transition *)
        (* in spec-side, we use the impl_nw ≺ spec_nw *)
        (* and given enq is possible at impl_nw to prove this *)
        unfold indistinguishable in H.
        cleanup.
        pose proof H1.
        specialize (H1 x 0%nat *[| [| {| gen_m.module_state := gen_m.req sm x; gen_m.inp := gen_m.Done |}; b; m.InFlight tag x |];
        inflight tag :: l0 ++ inflight k :: l2 |]*).
        prove_precond H1.
        light_clean_propagate.
        extract_all_fnequality.
        rm_existentials.
        split.
        rm_existentials.
        assumption.
        assumption.
        split; [eauto | repeat clear_trivial_evar].

        (* applying complete horizontally *)
        eapply complete.
        (* proving impl_sw ≺ spec_sw *)
        {
          prove_indistinguishable.
          (* vm: first *)
          (* ϕ impl_se spec_se -> impl_se ≺ spec_se *)
          (* first is available at impl_sw -> also available at impl_se -> spec_se *)
          (* complete doesn't remove anything from the list -> first is also available at spec_sw *)
          {
            symb_ex_split.
            merge_simpl.
            extract_all_fnequality.
            specialize (H 0 0%nat n).
            prove_precond H.
            simpl in *.
            light_clean_propagate.
            extract_all_fnequality.
            rm_existentials.
            rewrite app_comm_cons.
            split; eauto.
            simpl.
            rewrite HB4 in HA18.
            light_clean_propagate.
            (* there must be at least 1 element inside l *)
            apply (f_equal (@tl Cb_entry)) in H5.
            simpl in H5.
            destruct l.
            simpl in H5.
            apply (f_equal (@List.length Cb_entry)) in H5.
            rewrite app_length in H5.
            simpl in H5.
            lia.
            rm_existentials.
            split; [eauto | clear_trivial_wpa_step].
            simpl in H5.
            rewrite H5.
            split; [eauto | clear_trivial_evar].
          }
          (* am: enq *)
          (* impl can't enq back to back *)
          (* contradiction *)
          {
            light_clean_propagate.
            simpl.
            rm_existentials.
            assumption.
            assumption.
            split; [eauto | repeat clear_trivial_evar].
          }
          (* am: deq *)
          (* similar to first *)
          {
            light_clean_propagate.
            symb_ex_split.
            merge_simpl.
            extract_all_fnequality.
            rewrite HA18 in HA.
            light_clean_propagate.
            apply app_inj_tail in H5.
            light_clean_propagate.
            rewrite HB4 in HA18.
            light_clean_propagate.
            (* there must be at least 1 element in l *)
            apply (f_equal (@tl Cb_entry)) in H5.
            simpl in H5.
            destruct l5.
            apply (f_equal (@List.length Cb_entry)) in H5.
            rewrite app_length in H5.
            simpl in H5.
            lia.
            simpl in H5.
            specialize (H2 0 1%nat
            *[| [| {| gen_m.module_state := sm0; gen_m.inp := gen_m.None |}; b0; m.NoneB |]; l5 |]*).
            prove_precond H2.
            light_clean_propagate.
            extract_all_fnequality.
            rm_existentials.
            rewrite app_comm_cons.
            split; eauto.
            simpl.
            rm_existentials.
            split; [eauto | split].
            eauto.
            rewrite H5.
            split; [clear_trivial_wpa_step | ].
            split; [eauto | clear_trivial_evar].
            apply_log_fn 2%nat.
          }
        }

        (* proving complete is possible at impl_sw *)
        (* which is trivial since complete is available at impl_nw *)
        (* and enqueuing doens't affect that *)
        2:{
          simpl.
          rm_existentials.
          split; [eauto | split].
          2:{
            split.
            clear_trivial_wpa_step.
            1, 3: split; [eauto | repeat clear_trivial_evar].
            merge_simpl.
            simpl.
            split; [eauto | rm_existentials].
            split.
            instantiate (2 := inflight tag :: l0).
            simpl.
            eauto.
            split; eauto.
            merge_simpl.
            simpl.
            let y := eexists_st_array 2%nat in instantiate (1 := y).
            instantiate (3 := [| 
            {| gen_m.module_state := gen_m.req sm x; gen_m.inp := gen_m.Done |}; remm b k; m.InFlight tag x |]).
            apply_log_fn 2%nat; rewrite HA2.
            intros.
            clear_trivial_evar.
            intros.
            merge_simpl.
            rm_existentials.
            split.
            instantiate (2 := inflight tag :: l0).
            eauto.
            split; eauto.
            lia.
          }
          eauto.
        }

        (* get lock_step from inductive hypothesis *)
        simpl.
        apply remm_get with (k := k) in HA9.
        apply unique_partition' in H6; eauto.
        light_clean_propagate.
        prove_precond IHϕ.
        specialize (IHϕ 0%nat). (* specialize lock_step to be enq *)
        unfold lock_step in IHϕ.
        (* specialize the state with the tag introduced by left enq *)
        (* and the (k, v) from the upper complete *)
        specialize (IHϕ x *[| [| 
        {| gen_m.module_state := gen_m.req sm x; gen_m.inp := gen_m.Done |}; remm b k; m.InFlight tag x |]; 
        inflight tag :: l1 ++ completed k v :: l3 |]*).
        prove_precond IHϕ.
        light_clean_propagate.
        extract_all_fnequality.
        rewrite HA5 in HA14.
        inversion HA14.
        light_clean_propagate.
        eauto.

        (* precondition for lock_step *)
        simpl.
        rewrite HA5 in HA14.
        inversion HA14.
        light_clean_propagate.
        rewrite tag_inflight_completed with (v := v1) in HA6.
        rewrite tag_inflight_completed with (v := v1) in HA16.
        rm_existentials.
        split; [eauto | split].
        eauto.
        split.
        unfold extract_tag in HA6.
        clear_trivial_wpa_step.
        1-3: split; [eauto | clear_trivial_evar].
        simpl.
        apply_log_fn 2%nat.
        intros.
        clear_trivial_evar.

        (* precondition for inducitve hypothesis *)
        rm_existentials.
        split; [wrapped_arrays_equal 2%nat | eauto].
        simpl.
        rm_existentials.
        split; [eauto | split].
        eauto.
        split.
        clear_trivial_wpa_step.
        1-3: split; [eauto | clear_trivial_evar].
        simpl.
        apply_log_fn 2%nat.
        intros.
        clear_trivial_evar.
      }
      destruct i.
      (* deq *)
      (* straight-forward convergence *)
      (* specializing the lower complete state with (k, v) from upper complete *)
      {
        (* symbolically executing complete horizontally *)
        (* and deq in the impl-side vertically *)
        simpl.
        intros.
        light_clean_propagate.
        symb_ex_split.
        merge_simpl.
        extract_all_fnequality.

        (* proving deq is available at spec_nw *)
        rewrite H4 in H5.
        apply app_inj_tail in H5.
        light_clean_propagate.
        unfold indistinguishable in H.
        cleanup.
        specialize (H1 0 1%nat *[| [| ms; b; inp0 |]; l3 |]*).
        prove_precond H1.
        light_clean_propagate.
        extract_all_fnequality.
        rm_existentials.
        split.
        rm_existentials.
        split; eauto.

        (* get lock_step from inductive hypothesis *)
        apply unique_partition' in H6; eauto.
        light_clean_propagate.
        pose proof H4 as tmp.
        apply after_inflight_completed_tail in tmp.
        light_clean_propagate.
        prove_precond IHϕ.
        specialize (IHϕ 1%nat). (* specialize lock_step to be deq *)
        unfold lock_step in IHϕ.
        specialize (IHϕ 0 *[| [| ms; remm b k; inp0 |]; l4 ++ completed k v :: l |]*).
        prove_precond IHϕ.
        light_clean_propagate.
        extract_all_fnequality.
        apply app_inj_tail in H6.
        light_clean_propagate.
        simpl.
        unify_equality.
        light_clean_propagate.
        extract_all_fnequality.

        (* applying complete horizontally *)
        eapply complete.
        (* proving impl_sw ≺ spec_sw *)
        {
          prove_indistinguishable.
          (* vm: first *)
          (* similar to the first for complete-enq *)
          {
            light_clean_propagate.
            symb_ex_split.
            unify_equality.
            rewrite app_comm_cons in H3.
            rewrite app_assoc in H3.
            apply app_inj_tail in H3.
            light_clean_propagate.
            extract_all_fnequality.
            apply ϕ_implies_indistinguishable in HB6.
            unfold indistinguishable in HB6.
            cleanup.
            specialize (H1 0 0%nat n1).
            prove_precond H1.
            simpl in H1.
            light_clean_propagate.
            extract_all_fnequality.
            rm_existentials.
            split; eauto.
            simpl.
            rewrite app_comm_cons in H5.
            rewrite app_assoc in H5.
            apply app_inj_tail in H5.
            light_clean_propagate.
            pose proof HA0 as tmp.
            apply after_inflight_completed_tail in tmp.
            light_clean_propagate.
            rm_existentials.
            split; [eauto | ].
            rewrite app_comm_cons.
            rewrite app_assoc.
            clear_trivial_wpa_step.
            split; [eauto | clear_trivial_evar].
          }
          (* am: enq *)
          (* ϕ impl_se spec_se -> impl_se ≺ spec_se *)
          (* and it's possible to enq at impl_sw and complete *)
          (* doesn't affect internal module state -> it's also possible to enq at impl_se *)
          (* -> enq at spec_se and complete implies no transition in spec-side *)
          (* -> enq is available at spec_sw *)
          {
            light_clean_propagate.
            symb_ex_split.
            merge_simpl.
            unify_equality.
            extract_all_fnequality.
            apply ϕ_implies_indistinguishable in HB6.
            unfold indistinguishable in HB6.
            cleanup.
            extract_all_fnequality.
            light_clean_propagate.
            rewrite app_comm_cons in H4.
            rewrite app_assoc in H4.
            apply app_inj_tail in H4.
            light_clean_propagate.
            rewrite tag_inflight_completed with (v := v1) in HA14.
            specialize (H7 arg 0%nat *[| [| 
            {| gen_m.module_state := gen_m.req sm0 arg; gen_m.inp := gen_m.Done |}; remm b1 k; m.InFlight tag1 arg |];
            inflight tag1 :: l4 ++ completed k v1 :: l |]*).
            prove_precond H7.
            light_clean_propagate.
            extract_all_fnequality.
            rm_existentials.
            assumption.
            assumption.
            split; [eauto | repeat clear_trivial_evar].
            rewrite tag_inflight_completed with (v := v1) in HA16.
            apply remm_get with (k := k) in HA18.
            simpl.
            rm_existentials.
            split; [eauto | split].
            eauto.
            split.
            clear_trivial_wpa_step.
            1-3: split; [eauto | clear_trivial_evar].
            simpl.
            apply_log_fn 2%nat.
            intros.
            clear_trivial_evar.
          }
          (* am: deq *)
          (* similar to first *)
          {
            light_clean_propagate.
            symb_ex_split.
            unify_equality.
            rewrite app_comm_cons in H2.
            rewrite app_assoc in H2.
            apply app_inj_tail in H2.
            light_clean_propagate.
            apply ϕ_implies_indistinguishable in HB6.
            unfold indistinguishable in HB6.
            cleanup.
            rewrite app_comm_cons in H5.
            rewrite app_assoc in H5.
            apply app_inj_tail in H5.
            light_clean_propagate.
            pose proof HA0 as tmp.
            apply after_inflight_completed_tail in tmp.
            light_clean_propagate.
            specialize (H2 0 1%nat *[| [| ms; remm b k; inp0 |]; l4 ++ completed k v1 :: l1 |]*).
            prove_precond H2.
            light_clean_propagate.
            extract_all_fnequality.
            rm_existentials.
            split; eauto.
            simpl.
            rm_existentials.
            split; [eauto | split].
            eauto.
            rewrite app_comm_cons.
            rewrite app_assoc.
            split.
            clear_trivial_wpa_step.
            split; [eauto | clear_trivial_evar].
            simpl.
            apply_log_fn 2%nat.
          }
        }
        (* proving complete is available at impl_sw *)
        2:{
          simpl.
          rewrite app_comm_cons in H4.
          rewrite app_assoc in H4.
          apply app_inj_tail in H4.
          light_clean_propagate.
          rewrite app_comm_cons in HA9.
          rewrite app_assoc in HA9.
          rewrite map_app in HA9.
          apply NoDup_app_remove_r in HA9.
          rm_existentials.
          split; [eauto | split].
          2:{
            split.
            clear_trivial_wpa_step.
            1, 3: split; [eauto | clear_trivial_evar].
            merge_simpl.
            simpl.
            split; [eauto | rm_existentials].
            instantiate (1 := l).
            instantiate (1 := l4).
            split; eauto.
            merge_simpl.
            simpl.
            let y := eexists_st_array 2%nat in instantiate (1 := y).
            instantiate (3 := [| ms; remm b k; inp0 |]).
            instantiate (1 := l4 ++ completed k v1 :: l).
            apply_log_fn 2%nat.
            1-2: intros; clear_trivial_evar.
            lia.
          }
          eauto.
        }
        (* ϕ impl_se spec_se *)
        eauto.

        (* precondition for lock_step deq *)
        simpl.
        light_clean_propagate.
        simpl in HB4.
        light_clean_propagate.
        rm_existentials.
        split; [eauto | split].
        eauto.
        split.
        clear_trivial_wpa_step.
        rewrite app_comm_cons.
        rewrite app_assoc.
        split; [eauto | clear_trivial_evar].
        simpl.
        apply_log_fn 2%nat.
        intros.
        rewrite app_comm_cons.
        rewrite app_assoc.
        clear_trivial_evar.

        (* precondition for inductive hypothesis *)
        rm_existentials.
        split; [eauto | split].
        wrapped_arrays_equal 2%nat.

        (* precondition for impl_nw ≺ spec_nw *)
        simpl.
        rm_existentials.
        split; [eauto | split].
        eauto.
        split.
        clear_trivial_wpa_step.
        rewrite H4.
        split; [eauto | clear_trivial_evar].
        simpl.
        apply_log_fn 2%nat.
        intros.
        rewrite H4.
        clear_trivial_evar.
      }
      destruct i.
      (* complete *)
      (* tedious to prove with completing in the middle of two lists *)
      (* complete involves non-determinism but changing ϕ doesn't like *)
      (* deq doesn't quite work (issues with other cases) *)
      (* overall strategy: do lock_step complete and apply complete horizontally *)
      (* have the opposite completes match each other *)
      {
        (* symbolically executing complete horizontally and vertically *)
        simpl.
        intros.
        light_clean_propagate.
        symb_ex_split.
        merge_simpl.
        extract_all_fnequality.
        unify_equality.

        (* either the two completes complete the same element -> k = k0 *)
        (* or different elements -> k <> k0 -> either k is in front or k0 is *)
        pose proof (auxiliary_one l1 l2 k0 k l4 l5 H7).
        light_clean_propagate.
        destruct H1.
        (* proving the case where k <> k0 *)
        light_clean_propagate.
        destruct HB.
        (* k0 in front *)
        {
          light_clean_propagate.
          (* forall (b : m.map) k k0 v, k <> k0 /\ b k = Some v -> remm b k0 k = Some v *)
          assert (remm b k0 k = Some v3) by map_hammer.
          assert (remm b k k0 = Some v4) by map_hammer.
          pose proof HA16.
          rewrite H9 in H1.
          rewrite <- H1 in HA16.
          apply unique_partition' in H1; eauto.
          light_clean_propagate.
          prove_precond IHϕ.
          specialize (IHϕ 2%nat).
          unfold lock_step in IHϕ.
          specialize (IHϕ *[| 
          [| ms; remm (remm b k) k0; inp0 |]; l6 ++ completed k0 v4 :: l9 ++ l10 ++ completed k v3 :: l11 |]*).
          prove_precond IHϕ.
          (* applying complete horizontally *)
          eapply complete.
          (* proving impl_sw ≺ spec_sw *)
          {
            prove_indistinguishable.
            (* vm: first *)
            (* ϕ impl_se spec_se -> impl_se ≺ spec_se *)
            (* and first is avaiable at impl_sw -> first is possible at impl_sw *)
            {
              light_clean_propagate.
              extract_all_fnequality.
              symb_ex_split.
              merge_simpl.
              unify_equality.
              extract_all_fnequality.
              apply ϕ_implies_indistinguishable in IHϕ.
              unfold indistinguishable in IHϕ.
              cleanup.
              specialize (H5 0 0%nat n).
              prove_precond H5.
              simpl in H5.
              light_clean_propagate.
              extract_all_fnequality.
              rm_existentials.
              split; eauto.
              simpl.
              assert (exists l', l11 = l' ++ [completed tag n]).
              {
                rewrite app_comm_cons in H16.
                rewrite app_assoc in H16.
                rewrite app_assoc in H16.
                apply after_inflight_completed_tail in H16.
                eauto.
              }
              light_clean_propagate.
              rm_existentials.
              split; [eauto | clear_trivial_wpa_step].
              rewrite app_comm_cons with (x := l').
              rewrite app_assoc with (l := l10).
              rewrite app_assoc.
              rewrite app_comm_cons.
              rewrite app_assoc.
              split; [eauto | clear_trivial_evar].
            }
            (* am: enq *)
            (* similar to the trick in first *)
            (* ϕ impl_se spec_se -> impl_se ≺ spec_se *)
            (* and enq is possible at impl_sw -> it's also possible at spec_sw *)
            {
              light_clean_propagate.
              symb_ex_split.
              merge_simpl.
              extract_all_fnequality.
              apply ϕ_implies_indistinguishable in IHϕ.
              unfold indistinguishable in IHϕ.
              cleanup.
              unify_equality.
              extract_all_fnequality.
              specialize (H8 arg 0%nat *[| [| 
                {| gen_m.module_state := gen_m.req sm0 arg ; gen_m.inp := gen_m.Done |};
                remm (remm b k) k0;
                m.InFlight tag arg |];
                inflight tag :: l6 ++ completed k0 v4 :: l9 ++ l10 ++ completed k v3 :: l11 |]*).
              prove_precond H8.
              light_clean_propagate.
              extract_all_fnequality.
              rm_existentials.
              assumption.
              assumption.
              split; [eauto | repeat clear_trivial_evar].
              simpl.
              rm_existentials.
              split; [eauto | split].
              eauto.
              (* forall (b : m.map) (k k0 tag : N), remm b k0 tag = None -> remm (remm b k) k0 tag = None *)
              assert (remm (remm b k) k0 tag = None) by map_hammer.
              Ltac complete_an_inflight H l v' :=
                (rewrite app_assoc with (m := l) in H;
                rewrite app_comm_cons in H;
                rewrite app_assoc in H;
                rewrite tag_inflight_completed with (v := v') in H;
                rewrite <- app_assoc in H;
                rewrite <- app_comm_cons in H;
                rewrite <- app_assoc in H).
              complete_an_inflight HA30 l10 v3.
              complete_an_inflight HA15 l10 v3.
              split.
              clear_trivial_wpa_step.
              1-3: split; [eauto | clear_trivial_evar].
              apply_log_fn 2%nat.
              intros.
              clear_trivial_evar.
            }
            (* am: deq *)
            (* similar to first *)
            {
              light_clean_propagate.
              extract_all_fnequality.
              symb_ex_split.
              merge_simpl.
              extract_all_fnequality.
              apply ϕ_implies_indistinguishable in IHϕ.
              unfold indistinguishable in IHϕ.
              cleanup.
              unify_equality.
              rewrite app_assoc with (m := l10) in H17.
              rewrite app_comm_cons in H17.
              rewrite app_assoc in H17.
              pose proof H17 as tmp.
              apply after_inflight_completed_tail in tmp.
              light_clean_propagate.
              specialize (H10 0 1%nat 
              *[| [| ms0; remm (remm b k) k0; inp1 |]; l6 ++ completed k0 v4 :: l9 ++ l10 ++ completed k v3 :: l16 |]*).
              prove_precond H10.
              light_clean_propagate.
              extract_all_fnequality.
              rm_existentials.
              split; eauto.
              simpl.
              rewrite app_comm_cons with (x := l16).
              rewrite app_assoc with (l := l10).
              rewrite app_assoc.
              rewrite app_comm_cons.
              rewrite app_assoc.
              rm_existentials.
              split; [eauto | split].
              eauto.
              split.
              clear_trivial_wpa_step.
              split; [eauto | clear_trivial_evar].
              apply_log_fn 2%nat.
            }
          }
          
          (* proving complete is available at impl_sw *)
          2:{
            simpl.
            rm_existentials.
            split; [eauto | split].
            2:{
              rewrite app_assoc in HB5.
              rewrite app_comm_cons in HB5.
              rewrite app_assoc in HB5.
              rewrite tag_inflight_completed with (v := v4) in HA16.
              rewrite app_assoc in HA16.
              rewrite app_comm_cons in HA16.
              rewrite app_assoc in HA16.
              split.
              clear_trivial_wpa_step.
              1-3: split; [eauto | clear_trivial_evar].
              merge_simpl.
              simpl.
              let y := eexists_st_array 2%nat in instantiate (1 := y).
              instantiate (3 := [| ms; remm (remm b k0) k; inp0 |]).
              apply_log_fn 2%nat.
              1-2: intros; clear_trivial_evar.
              lia.
            }
            eauto.
          }

          (* ϕ impl_se spec_se *)
          simpl.
          (* remm commutes *)
          assert (remm (remm b k) k0 = remm (remm b k0) k) by map_hammer.
          rewrite <- H8.
          rewrite <- app_assoc.
          rewrite <- app_comm_cons.
          rewrite <- app_assoc.
          simpl in IHϕ.
          eauto.

          (* precondition for lock_step complete *)
          rewrite H9 in H7.
          rewrite app_comm_cons in H7.
          rewrite app_assoc in H7.
          rewrite app_assoc in H7.
          apply unique_partition' in H7; eauto.
          light_clean_propagate.
          simpl in HB3.
          light_clean_propagate.
          simpl.
          rm_existentials.
          split; [eauto | split].
          eauto.
          rewrite <- app_assoc.
          rewrite <- app_assoc.
          rewrite <- app_comm_cons.
          rewrite app_comm_cons in H4.
          rewrite app_assoc in H4.
          rewrite app_assoc in H4.
          rewrite tag_inflight_completed with (v := v3) in H4.
          rewrite <- app_assoc in H4.
          rewrite <- app_assoc in H4.
          rewrite <- app_comm_cons in H4.
          split.
          clear_trivial_wpa_step.
          1-3: split; [eauto | clear_trivial_evar].
          merge_simpl.
          simpl.
          apply_log_fn 2%nat.
          1-2: intros; clear_trivial_evar.
          rewrite <- app_assoc.
          rewrite <- app_assoc.
          rewrite <- app_comm_cons.
          eauto.
          rm_existentials.
          split; [wrapped_arrays_equal 2%nat | eauto].
        }
        (* k1 in front *)
        (* the proof is symmetric to the previous case *)
        {
          light_clean_propagate.
          (* forall (b : m.map) k k0 v, k <> k0 /\ b k = Some v -> remm b k0 k = Some v *)
          assert (remm b k0 k = Some v3) by map_hammer.
          assert (remm b k k0 = Some v4) by map_hammer.
          pose proof HA16.
          rewrite H9 in H1.
          rewrite <- H1 in HA16.
          rewrite app_comm_cons in H1.
          rewrite app_assoc in H1.
          rewrite app_assoc in H1.
          apply unique_partition' in H1; eauto.
          light_clean_propagate.
          prove_precond IHϕ.
          specialize (IHϕ 2%nat).
          unfold lock_step in IHϕ.
          specialize (IHϕ *[| [| ms; remm (remm b k) k0; inp0 |]; l8 ++ completed k v3 :: l9 ++ l10 ++ completed k0 v4 :: l7 |]*).
          prove_precond IHϕ.
          (* applying complete horizontally *)
          eapply complete.
          (* proving impl_sw ≺ spec_sw *)
          {
            prove_indistinguishable.
            (* vm: first *)
            (* ϕ impl_se spec_se -> impl_se ≺ spec_se *)
            (* and first is avaiable at impl_sw -> first is possible at impl_sw *)
            {
              light_clean_propagate.
              extract_all_fnequality.
              symb_ex_split.
              merge_simpl.
              extract_all_fnequality.
              unify_equality.
              apply ϕ_implies_indistinguishable in IHϕ.
              unfold indistinguishable in IHϕ.
              cleanup.
              specialize (H5 0 0%nat n).
              prove_precond H5.
              simpl in H5.
              light_clean_propagate.
              extract_all_fnequality.
              rm_existentials.
              split; eauto.
              simpl.
              rm_existentials.
              rewrite app_assoc.
              rewrite app_comm_cons.
              rewrite app_assoc.
              split; [eauto | reconstruct_step].
              assert (l7 = [] \/ (exists l, l7 = l ++ [completed tag n])).
              {
                apply aftter_completed_completed_tail in H10.
                eauto.
              }
              destruct H16.
              (* l7 = [] *)
              light_clean_propagate.
              apply app_inj_tail in H10.
              light_clean_propagate.
              split; [eauto | rm_existentials].
              rewrite HB.
              split; eauto.

              (* exists l, l7 = l ++ [completed tag n] *)
              light_clean_propagate.
              rewrite app_comm_cons with (x := l15).
              rewrite app_assoc.
              split; [eauto | clear_trivial_evar].
            }
            (* am: enq *)
            (* similar to the trick in first *)
            (* ϕ impl_se spec_se -> impl_se ≺ spec_se *)
            (* and enq is possible at impl_sw -> it's also possible at spec_sw *)
            {
              light_clean_propagate.
              symb_ex_split.
              merge_simpl.
              extract_all_fnequality.
              apply ϕ_implies_indistinguishable in IHϕ.
              unfold indistinguishable in IHϕ.
              cleanup.
              unify_equality.
              extract_all_fnequality.
              specialize (H8 arg 0%nat *[| [| 
                {| gen_m.module_state := gen_m.req sm0 arg ; gen_m.inp := gen_m.Done |};
                remm (remm b k) k0;
                m.InFlight tag arg |];
                inflight tag :: l8 ++ completed k v3 :: l9 ++ l10 ++ completed k0 v4 :: l7 |]*).
              prove_precond H8.
              light_clean_propagate.
              extract_all_fnequality.
              rm_existentials.
              assumption.
              assumption. 
              split; [eauto | repeat clear_trivial_evar].
              simpl.
              rm_existentials.
              split; [eauto | split].
              eauto.
              (* forall (b : m.map) k k0 tag, remm b k0 tag = None -> remm (remm b k) k0 tag = None *)
              assert (remm (remm b k) k0 tag = None) by map_hammer.
              rewrite tag_inflight_completed with (v := v4) in H4.
              rewrite <- app_assoc in H4.
              rewrite <- app_assoc in H4.
              rewrite <- app_comm_cons in H4.
              rewrite tag_inflight_completed with (v := v3) in H4.
              split.
              rewrite <- app_assoc in HA15.
              rewrite <- app_assoc in HA15.
              rewrite <- app_comm_cons in HA15.
              rewrite tag_inflight_completed with (v := v3) in HA15.
              clear_trivial_wpa_step.
              1-3: split; [eauto | clear_trivial_evar].
              apply_log_fn 2%nat.
              intros.
              clear_trivial_evar.
            }
            (* am: deq *)
            (* similar to first *)
            {
              light_clean_propagate.
              extract_all_fnequality.
              symb_ex_split.
              merge_simpl.
              extract_all_fnequality.
              apply ϕ_implies_indistinguishable in IHϕ.
              unfold indistinguishable in IHϕ.
              cleanup.
              unify_equality.
              assert (l7 = [] \/ (exists l, l7 = l ++ [completed tag n])).
              {
                apply aftter_completed_completed_tail in H17.
                eauto.
              }
              rewrite <- app_assoc in H17.
              rewrite <- app_assoc in H17.
              rewrite <- app_comm_cons in H17.
              destruct H14.

              (* l7 = [] *)
              light_clean_propagate.
              specialize (H10 0 1%nat *[| [| ms0; remm (remm b k) k0; inp1 |]; l8 ++ completed k v3 :: l9 ++ l10 |]*).
              prove_precond H10.
              light_clean_propagate.
              extract_all_fnequality.
              rm_existentials.
              split; eauto.
              simpl.
              rm_existentials.
              rewrite app_assoc with (m := l10).
              rewrite app_comm_cons.
              rewrite app_assoc.
              split; [eauto | split].
              eauto.
              split.
              clear_trivial_wpa_step.
              split; [eauto | clear_trivial_evar].
              apply_log_fn 2%nat.

              (* exists l, l7 = l ++ [completed tag n] *)
              light_clean_propagate.
              specialize (H10 0 1%nat *[| [| ms0; remm (remm b k) k0; inp1 |]; l8 ++ completed k v3 :: l9 ++ l10 ++ completed k0 v4 :: l16 |]*).
              prove_precond H10.
              light_clean_propagate.
              extract_all_fnequality.
              rm_existentials.
              split; eauto.
              simpl.
              rm_existentials.
              split; [eauto | split].
              eauto.
              rewrite app_comm_cons with (x := l16).
              rewrite app_assoc with (l := l10).
              rewrite app_assoc.
              rewrite app_comm_cons.
              rewrite app_assoc.
              split.
              clear_trivial_wpa_step.
              split; [eauto | clear_trivial_evar].
              apply_log_fn 2%nat.
            }
          }

          (* proving complete is available at impl_sw *)
          2:{
            simpl.
            rm_existentials.
            split; [eauto | split].
            2:{
              rewrite <- app_assoc in HB5.
              rewrite <- app_assoc in HB5.
              rewrite <- app_comm_cons in HB5.
              rewrite tag_inflight_completed with (v := v4) in H4.
              rewrite <- app_assoc in H4.
              rewrite <- app_assoc in H4. 
              rewrite <- app_comm_cons in H4.
              split.
              clear_trivial_wpa_step.
              1, 3: split; [eauto | clear_trivial_evar].
              merge_simpl.
              simpl.
              split; [eauto | clear_trivial_evar].
              merge_simpl.
              simpl.
              let y := eexists_st_array 2%nat in instantiate (1 := y).
              instantiate (3 := [| ms; remm (remm b k0) k; inp0 |]).
              apply_log_fn 2%nat.
              1-2: intros; clear_trivial_evar.
              lia.
            }
            eauto.
          }
          (* ϕ impl_se spec_se *)
          simpl.
          (* remm commutes *)
          assert (remm (remm b k) k0 = remm (remm b k0) k) by map_hammer.
          rewrite <- H8.
          simpl in IHϕ.
          eauto.

          (* precondition for lock_step complete *)
          rewrite H9 in H7.
          rewrite <- app_assoc in H7.
          rewrite <- app_assoc in H7.
          rewrite <- app_comm_cons in H7.
          apply unique_partition' in H7; eauto.
          light_clean_propagate.
          simpl in HB3.
          light_clean_propagate.
          simpl.
          rm_existentials.
          do 2 (
            rewrite app_comm_cons;
            rewrite app_assoc;
            rewrite app_assoc
          ).
          rewrite <- app_assoc in H4.
          rewrite <- app_assoc in H4.
          rewrite <- app_comm_cons in H4.
          rewrite tag_inflight_completed with (v := v3) in H4.
          rewrite app_comm_cons in H4.
          rewrite app_assoc in H4.
          rewrite app_assoc in H4.
          split; [eauto | split].
          eauto.
          split.
          clear_trivial_wpa_step.
          1-3: split; [eauto | clear_trivial_evar].
          merge_simpl.
          simpl.
          apply_log_fn 2%nat.
          1-2: intros; clear_trivial_evar.
          rm_existentials.
          split; [wrapped_arrays_equal 2%nat | eauto].
          rewrite <- app_assoc.
          rewrite <- app_assoc.
          rewrite <- app_comm_cons.
          eauto.
        }

        (* k = k0 *)
        light_clean_propagate.
        rewrite H7 in H9.
        apply unique_partition' in H9; eauto.
        light_clean_propagate.
        unify_equality.
        assert (nxt_st0 = [| [| ms; remm b k0; inp0 |]; l6 ++ completed k0 v4 :: l7 |]) by custom_eq_array 2%nat.
        assert (nxt_st = nxt_st0).
        {
          rewrite H1.
          custom_eq_array 2%nat.
        }
        light_clean_propagate.
        simpl.
        eauto.
      }
      destruct i.
      (* complete_m *)
      (* straight-forward convergence *)
      (* specializing the lower complete state with (k, v) from upper complete *)
      {
        (* symoblically executing complete horizontally *)
        (* and complete_m vertically *)
        simpl.
        unfold lift_to.
        intros.
        light_clean_propagate.
        simpl in *.
        light_clean_propagate.
        extract_all_fnequality.
        symb_ex_split.
        merge_simpl.
        extract_all_fnequality.
        (* forall (b : m.map) k k0 v, k <> k0 -> setm b k v k0 = b k0 *)
        assert (setm b0 tag (gen_m.get_resp sm) k = Some v) by map_hammer.

        (* get lock_step from inductive hypothesis *)
        prove_precond IHϕ.
        specialize (IHϕ 3%nat). (* specalize lock_step to complete_m *)
        unfold lock_step in IHϕ.
        specialize (IHϕ *[| 
        [| 
          {| gen_m.module_state := gen_m.deq sm; gen_m.inp := gen_m.None |}; 
          setm (remm b0 k) tag (gen_m.get_resp sm);
          m.NoneB
        |];
        l1 ++ completed k v :: l2 |]*).
        unfold lift_to in IHϕ.
        prove_precond IHϕ.
        (* forall (b : m.map) k k0 v, k <> k0 -> remm (setm b k v) k0 = setm (remm b k0) k v *)
        assert (setm (remm b0 k) tag (gen_m.get_resp sm) = remm (setm b0 tag (gen_m.get_resp sm)) k) by map_hammer.
        rewrite H5 in IHϕ.
        light_clean_propagate.
        extract_all_fnequality.

        (* applying complete horizontally *)
        eapply complete.
        (* proving impl_sw ≺ spec_sw *)
        { 
          prove_indistinguishable.
          (* vm: first *)
          (* similar to complete-enq case *)
          (* but complete_m implies no transition in spec-side *)
          (* making it simpler *)
          {
            light_clean_propagate.
            symb_ex_split.
            extract_all_fnequality.
            apply ϕ_implies_indistinguishable in H0.
            unfold indistinguishable in H0.
            cleanup.
            specialize (H0 0 0%nat n).
            prove_precond H0.
            simpl in H0.
            light_clean_propagate.
            extract_all_fnequality.
            rm_existentials.
            split; eauto.
            simpl.
            apply unique_partition' in H4; eauto.
            light_clean_propagate.
            pose proof H3 as tmp.
            apply after_inflight_completed_tail in tmp.
            light_clean_propagate.
            rewrite app_comm_cons.
            rewrite app_assoc.
            rm_existentials.
            split; [eauto | clear_trivial_wpa_step].
            split; [eauto | clear_trivial_evar].
          }
          (* am: enq *)
          (* ϕ impl_se spec_se -> impl_se ≺ spec_se *)
          (* given it's possible to enq at impl_se -> *)
          (* enq is possible at impl_se -> spec_se -> spec_sw *)
          {
            light_clean_propagate.
            symb_ex_split.
            merge_simpl.
            extract_all_fnequality.
            apply ϕ_implies_indistinguishable in IHϕ.
            unfold indistinguishable in IHϕ.
            cleanup.
            specialize (H3 arg 0%nat *[| [| 
              {| gen_m.module_state := gen_m.req (gen_m.deq sm0) arg; gen_m.inp := gen_m.Done |}; 
              remm (setm b0 tag0 (gen_m.get_resp sm0)) k; 
              m.InFlight tag1 arg |];
              inflight tag1 :: l1 ++ completed k v :: l2
            |]*).
            apply remm_get with (k := k) in HA18.
            rewrite tag_inflight_completed with (v := v) in HA15.
            rewrite tag_inflight_completed with (v := v) in HA19.
            prove_precond H3.
            light_clean_propagate.
            extract_all_fnequality.
            rm_existentials.
            assumption.
            assumption.
            split; [eauto | repeat clear_trivial_evar].
            simpl.
            rm_existentials.
            split; [eauto | split].
            eauto.
            split.
            clear_trivial_wpa_step.
            1-3: split; [eauto | clear_trivial_evar].
            simpl.
            apply_log_fn 2%nat.
            intros.
            clear_trivial_evar.
          }
          (* am: deq *)
          (* ϕ impl_se spec_se -> impl_se ≺ spec_se *)
          (* given it's possible to deq at impl_se -> *)
          (* deq is possible at impl_se -> spec_se -> spec_sw *)
          {
            light_clean_propagate.
            symb_ex_split.
            extract_all_fnequality.
            apply ϕ_implies_indistinguishable in IHϕ.
            unfold indistinguishable in IHϕ.
            cleanup.
            rewrite H3 in H11.
            apply app_inj_tail in H11.
            light_clean_propagate.
            pose proof H3 as tmp.
            apply after_inflight_completed_tail in tmp.
            light_clean_propagate.
            specialize (H6 0 1%nat *[| [| 
            {| gen_m.module_state := gen_m.deq sm0; gen_m.inp := gen_m.None |}; 
            remm (setm b0 tag0 (gen_m.get_resp sm0)) k; m.NoneB |];
            l1 ++ completed k v :: l |]*).
            prove_precond H6.
            light_clean_propagate.
            extract_all_fnequality.
            rm_existentials.
            split; eauto.
            simpl.
            rewrite app_comm_cons.
            rewrite app_assoc. 
            rm_existentials.
            split; [eauto | split].
            eauto.
            split.
            clear_trivial_wpa_step.
            split; [eauto | clear_trivial_evar].
            apply_log_fn 2%nat.
          }
        }

        (* proving complete is possible at impl_sw *)
        2:{
          simpl.
          rm_existentials.
          split; [eauto | split].
          2:{
            split.
            clear_trivial_wpa_step.
            1-3: split; [eauto | clear_trivial_evar].
            simpl.
            let y := eexists_st_array 2%nat in instantiate (1 := y).
            instantiate (3 := [| {| gen_m.module_state := gen_m.deq sm; gen_m.inp := gen_m.None |}; 
            remm (setm b0 tag (gen_m.get_resp sm)) k; m.NoneB |]).
            apply_log_fn 2%nat.
            1-2: intros; clear_trivial_evar.
          }
          eauto.
        }
        (* ϕ impl_se spec_se *)
        eauto.

        (* precondition for lock_step *)
        rm_existentials.
        split; [eauto | rm_existentials].
        split.
        2:{
          simpl.
          rm_existentials.
          assumption.
          assumption.
          apply remm_get with (k := k) in HA3.
          split; [eauto | repeat clear_trivial_evar].
        }
        apply unique_partition' in H4; eauto.
        light_clean_propagate.
        unfold aset.
        rewrite HA4.
        rewrite HB.
        wrapped_arrays_equal 2%nat.

        (* precondition for inductive hypothesis *)
        rm_existentials.
        split; [wrapped_arrays_equal 2%nat | eauto].
      }
      eauto.
    }
    (* complete_m case *)
    {
      destruct i;
      unfold lock_step;
      intros;
      simpl in *;
      unfold lift_to in H2.
      (* enq *)
      (* impl can't do complete_m and enq at one state *)
      {
        light_clean_propagate.
        symb_ex_split.
        extract_all_fnequality.
      }
      destruct i.
      (* deq *)
      (* straight-forward convergence *)
      (* no non-determinism *)
      {
        (* symbolically executing  *)
        intros.
        light_clean_propagate.
        symb_ex_split.
        extract_all_fnequality.

        (* proving deq is possible at spec_nw *)
        unfold indistinguishable in H.
        cleanup.
        specialize (H1 0 1%nat *[| 
        [| {| gen_m.module_state := sm; gen_m.inp := gen_m.Done |}; b; m.InFlight tag op |]; l0 |]*).
        prove_precond H1.
        apply app_inj_tail in H3. 
        light_clean_propagate.
        extract_all_fnequality.
        rm_existentials.
        split.
        rm_existentials.
        split; eauto.

        (* get lock_step from inductive hypothesis *)
        pose proof H0.
        prove_precond IHϕ.
        light_clean_propagate.
        extract_all_fnequality.
        specialize (IHϕ 1%nat). (* specialize lock_step to be deq *)
        unfold lock_step in IHϕ.
        specialize (IHϕ 0 *[| 
        [| 
          {| gen_m.module_state := gen_m.deq sm; gen_m.inp := gen_m.None |};
          setm b tag (gen_m.get_resp sm); m.NoneB |];
          l1
        |]*).
        prove_precond IHϕ.
        light_clean_propagate.
        extract_all_fnequality.
        simpl in *.
        light_clean_propagate.
        symb_ex_split.
        all: cycle 1.

        (* precondition for lock_step deq *)
        {
          simpl.
          rm_existentials.
          split; [eauto | ].
          split; [eauto | ].
          split.
          clear_trivial_wpa_step.
          split; [eauto | clear_trivial_evar].
          apply_log_fn 2%nat.
        }
        (* precondition for inductive hypothesis *)
        {
          rm_existentials.
          split; [wrapped_arrays_equal 2%nat | eauto].
        }
        (* precondition for impl_nw ≺ spec_nw *)
        simpl.
        rm_existentials.
        split; [eauto | split].
        eauto.
        split.
        clear_trivial_wpa_step.
        split; [eauto | clear_trivial_evar].
        apply_log_fn 2%nat.

        (* applying complete_m horizontally *)
        eapply complete_m.
        {
          prove_indistinguishable.
          (* vm: first *)
          (* ϕ impl_se spec_se -> impl_se ≺ spec_se *)
          (* given first at impl_sw -> first at impl_se *)
          (* -> first at spec_se -> first at spec_sw *)
          {
            light_clean_propagate.
            symb_ex_split.
            apply ϕ_implies_indistinguishable in HB2.
            unfold indistinguishable in HB2.
            cleanup.
            specialize (H2 0 0%nat n5).
            unify_equality.
            prove_precond H2.
            simpl in H2.
            light_clean_propagate.
            extract_all_fnequality.
            apply app_inj_tail in H6.
            light_clean_propagate.
            clear_trivial_evar.
            rm_existentials.
            split; [eauto | clear_trivial_wpa_step].
            split; [eauto | clear_trivial_evar].
          }
          (* am: enq *)
          (* impl can't enq before first doing complete_m *)
          (* -> contradiction *)
          {
            light_clean_propagate.
            symb_ex_split.
            merge_simpl.
            unify_equality.
            extract_all_fnequality.
          }
          (* am: deq *)
          (* similar to first *)
          {
            light_clean_propagate.
            symb_ex_split.
            apply ϕ_implies_indistinguishable in HB2.
            unfold indistinguishable in HB2.
            cleanup.
            unify_equality.
            apply app_inj_tail in H4.
            light_clean_propagate.
            specialize (H8 0 1%nat *[| [| {| 
            gen_m.module_state := gen_m.deq sm; gen_m.inp := gen_m.None |};
            setm b tag (gen_m.get_resp sm); m.NoneB |];
            l4 |]*).
            prove_precond H8.
            light_clean_propagate.
            extract_all_fnequality.
            apply app_inj_tail in H6.
            light_clean_propagate.
            rm_existentials.
            split; eauto.
            simpl.
            rm_existentials.
            split; [eauto | split].
            eauto.
            split.
            clear_trivial_wpa_step.
            split; [eauto | clear_trivial_evar].
            apply_log_fn 2%nat.
          }
        }
        (* proving complete_m is possible at impl_nw *)
        (* and instantiating the resulting state *)
        2:{
          unfold lift_to.
          rm_existentials.
          split; [eauto | rm_existentials].
          split.
          2:{
            simpl.
            rm_existentials.
            assumption.
            assumption.
            split; [eauto | repeat clear_trivial_evar].
          }
          eauto.
        }

        (* some massaging to get ϕ impl_se spec_sw *)
        apply app_inj_tail in H6.
        light_clean_propagate.
        assert ( *(aset nxt_st 0 *[| {| gen_m.module_state := gen_m.deq sm; gen_m.inp := gen_m.None |}; setm b tag (gen_m.get_resp sm); m.NoneB |]* )* =
        *[| [| {| gen_m.module_state := gen_m.deq sm; gen_m.inp := gen_m.None |}; setm b tag (gen_m.get_resp sm); m.NoneB |]; l1 |]*).
        {
          unfold aset.
          rewrite HA2.
          rewrite HB0.
          simpl.
          wrapped_arrays_equal 2%nat.
        }
        simpl in H2.
        rewrite <- H2 in HB2.
        eauto.
      }
      destruct i.
      (* complete *)
      {
        (* destructing information from doing complete_m horizontally *)
        (* and symbolically executing complete in impl-side vertically *)
        intros.
        light_clean_propagate.
        symb_ex_split.
        merge_simpl.
        extract_all_fnequality.
        (* forall (b : m.map) k k0 v, k <> k0 -> remm (setm b k v) k0 = setm (remm b k0) k v *)
        assert (remm (setm b0 tag (gen_m.get_resp sm)) k = setm (remm b0 k) tag (gen_m.get_resp sm)) by map_hammer.
        prove_precond IHϕ.
        specialize (IHϕ 2%nat).
        unfold lock_step in IHϕ.
        specialize (IHϕ *[| [| 
        {| gen_m.module_state := gen_m.deq sm; gen_m.inp := gen_m.None |};
        remm (setm b0 tag (gen_m.get_resp sm)) k; m.NoneB |];
        l1 ++ completed k v :: l2 |]*).
        prove_precond IHϕ.

        (* applying complete_m horizontally *)
        eapply complete_m.
        (* proving impl_nw ≺ spec_nw *)
        { 
          prove_indistinguishable.
          (* vm: first *)
          (* same old trick *)
          (* ϕ impl_se spec_se -> impl_se ≺ spec_se *)
          (* given first is available at impl_sw -> first at impl_se *)
          {
            light_clean_propagate.
            extract_equality H4 2%nat 1%nat.
            light_clean_propagate.
            symb_ex_split.
            merge_simpl.
            extract_all_fnequality.
            apply ϕ_implies_indistinguishable in IHϕ.
            unfold indistinguishable in IHϕ.
            cleanup.
            specialize (H2 0 0%nat n).
            prove_precond H2.
            simpl in H2.
            light_clean_propagate.
            extract_all_fnequality.
            rm_existentials.
            split; eauto.
            apply unique_partition' in H5; eauto.
            light_clean_propagate.
            rewrite HB2 in HA12.
            light_clean_propagate.
            simpl.
            rm_existentials.
            rewrite H5.
            split; [eauto | clear_trivial_wpa_step].
            split; [eauto | clear_trivial_evar].
          }
          (* am: enq *)
          (* impl-side can't do enq beforeing doing complete_m *)
          (* -> contradiction *)
          {
            light_clean_propagate.
            extract_all_fnequality.
            symb_ex_split.
            merge_simpl.
            unify_equality.
            extract_all_fnequality.
          }
          (* am: deq *)
          (* similar to first *)
          {
            light_clean_propagate.
            extract_all_fnequality.
            symb_ex_split.
            merge_simpl.
            extract_all_fnequality.
            unify_equality.
            apply app_inj_tail in H3.
            light_clean_propagate.
            apply ϕ_implies_indistinguishable in IHϕ.
            unfold indistinguishable in IHϕ.
            cleanup.
            apply unique_partition' in H5; eauto.
            light_clean_propagate.
            specialize (H3 0 1%nat *[| [| 
            {| gen_m.module_state := gen_m.deq sm; gen_m.inp := gen_m.None |};
            remm (setm b0 tag (gen_m.get_resp sm)) k;
            m.NoneB |];
            l9 |]*).
            prove_precond H3.
            light_clean_propagate.
            extract_all_fnequality.
            rm_existentials.
            split; eauto.
            simpl.
            rm_existentials.
            rewrite H4.
            split; [eauto | split].
            eauto.
            split.
            clear_trivial_wpa_step.
            split; [eauto | clear_trivial_evar].
            simpl.
            apply_log_fn 2%nat.
          }
        }
        (* proving complete_m is possible at impl_nw *)
        (* and instantiating resulting state *)
        2:{
          unfold lift_to.
          rm_existentials.
          split; [eauto | rm_existentials].
          split.
          2:{
            simpl.
            rm_existentials.
            assumption.
            assumption.
            apply remm_get with (k := k) in HA7.
            split; [eauto | repeat clear_trivial_evar].
          }
          eauto.
        }

        (* getting ϕ impl_se spec_se *)
        rewrite H1 in IHϕ.
        simpl in IHϕ.
        apply unique_partition' in H5; eauto.
        light_clean_propagate.
        assert ( *(aset nxt_st 0 *[| {| gen_m.module_state := gen_m.deq sm; gen_m.inp := gen_m.None |}; setm (remm b0 k) tag (gen_m.get_resp sm); m.NoneB |]* )* =
        *[| [| {| gen_m.module_state := gen_m.deq sm; gen_m.inp := gen_m.None |}; setm (remm b0 k) tag (gen_m.get_resp sm); m.NoneB |]; l0 ++ completed k v :: l3 |]*).
        {
          unfold aset.
          rewrite HA3.
          rewrite HB0.
          simpl.
          wrapped_arrays_equal 2%nat.
        }
        simpl in H2.
        rewrite <- H2 in IHϕ.
        eauto.

        (* precondition for lock_step complete *)
        simpl.
        rm_existentials.
        split; [eauto | split].
        eauto.
        (* b0 k = Some v /\ b0 tag = None *)
        assert (setm b0 tag (gen_m.get_resp sm) k = Some v) by map_hammer.
        split.
        clear_trivial_wpa_step.
        1-3: split; [eauto | clear_trivial_evar].
        merge_simpl.
        simpl.
        apply_log_fn 2%nat.
        1-2: intros; clear_trivial_evar.
        rm_existentials.
        split; [wrapped_arrays_equal 2%nat | eauto].
      }
      destruct i.
      (* complete_m *)
      (* trivial case the two complete_m's simply *)
      (* converge *)
      {
        unfold lift_to.
        intros.
        light_clean_propagate.
        simpl in HA1.
        simpl in *.
        light_clean_propagate.
        extract_all_fnequality.
        merge_simpl.
        eauto.
      }
      eauto.
    }
    Unshelve.
    all: econstructor.
  Qed.

  Theorem refinement: refines ooo.mkOoo pipeline.mkPipeline related.
  Proof.
    prove_refinement.
    {
      pose proof relation_preserved as lem.
      specialize lem with (1 := related_i_s) (i := 0%nat).
      unfold lock_step in lem.
      simpl in lem.
      specialize lem with (x := arg_method) (ei := mid_i).
      specialize lem with (1 := init2mid_i).
      light_clean_propagate.
      symb_ex_split.
      extract_all_fnequality.
      merge_simpl.
      rm_existentials.
      split.
      rm_existentials.
      trivial.
      trivial.
      split; [eauto | repeat clear_trivial_evar].
      split; [eapply existSR_done | ].
      split.
      split; [eauto | ].
      clear_trivial_evar.
      wrapped_arrays_equal 2%nat.
      eapply ϕ_implies_indistinguishable.
      eauto.
    }
    {
      pose proof relation_preserved as lem.
      specialize lem with (1 := related_i_s) (i := 1%nat).
      unfold lock_step in lem.
      simpl in lem.
      specialize lem with (x := arg_method) (ei := mid_i).
      specialize lem with (1 := init2mid_i).
      light_clean_propagate.
      symb_ex_split.
      extract_all_fnequality.
      rm_existentials.
      split.
      clear_trivial_evar.
      split; [eapply existSR_done | ].
      split; [split; [eauto | clear_trivial_evar] | ].
      wrapped_arrays_equal 2%nat.
      eapply ϕ_implies_indistinguishable.
      eauto.
    }
    {
      pose proof relation_preserved as lem.
      specialize lem with (1 := related_i_s) (i := 2%nat).
      unfold lock_step in lem.
      simpl in lem.
      specialize lem with (ei := mid_i).
      specialize lem with (1 := init2mid_i).
      light_clean_propagate.
      symb_ex_split.
      extract_all_fnequality.
      merge_simpl.
      rm_existentials.
      split; [eapply existSR_done | ].
      split; [split; [eauto | clear_trivial_evar] | ].
      wrapped_arrays_equal 2%nat.
      eapply ϕ_implies_indistinguishable.
      eauto.
    }
    {
      pose proof relation_preserved as lem.
      specialize lem with (1 := related_i_s) (i := 3%nat).
      unfold lock_step in lem.
      simpl in lem.
      specialize lem with (ei := mid_i).
      specialize lem with (1 := init2mid_i).
      unfold lift_to in init2mid_i.
      light_clean_propagate.
      symb_ex_split.
      extract_all_fnequality.
      rm_existentials.
      unfold related.
      split; [eapply existSR_done | ].
      split; [split; [eauto | clear_trivial_evar] | ].
      wrapped_arrays_equal 2%nat.
      eapply ϕ_implies_indistinguishable.
      eauto. 
    }
  Qed.
End Ooo_pipeline.
