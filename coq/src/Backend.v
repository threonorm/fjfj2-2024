Require Import Lia.
(* Require Import String. *)
Require Import NArith.
Require Import LangFjfj2.
Require Import Indexification.
Require Import FjfjParsing.
Require Import List.

Local Set Universe Polymorphism.
Unset Universe Minimization ToSet.


Require Import Tactics.
Import ListNotations.
Require Import reg.
Require FifoSpec.
Import FifoSpec.FifoSpec.
Import FifoSpec.FifoF.
Require Processor.
Require Import RfScored.
Open Scope N.

Require Import Tactics.
Require Import egg.Loader.
Require Import LoadBufferStoresafe.

(* Local Instance nouninterp : Uninterpreted_Functions := _. *)
Module Backend.
    Local Instance processor_modules : instances :=
      #| 
        mkReg expected_pc;
        mkRf rf; 

        mkFifoSpec d2e;

        mkFifoFSpec e2w;
        mkFifoFSpec ldQ_sent;
        mkFifoFSpec ldQ_received;

        mkFifoSpec to_dmem;
        mkFifoSpec from_dmem;
        mkFifoSpec to_mmio;
        mkFifoSpec from_mmio;
        mkReg processing_st_mmio
      |#.

     Definition push_instr :=
      (* This is the method one can call *)
      Eval cbv in (action_method (pc_received data_resp)
            (begin 
              (set decoded (decode data_resp))
              (if (has_destination decoded)
                {declare_write rf (destination decoded)}
                pass)
              (set src1 {read1 rf (src1 decoded)})
              (set src2 {read2 rf (src2 decoded)})
              {enq d2e (# src1 src2 pc_received decoded)})).
    Arguments push_instr/.

    Definition do_execute :=
      Eval cbv in (rule 
        (begin
            (set (val1 val2 coming_pc decoded) {first d2e})
            {deq d2e}
            (set cur_pc {read expected_pc})
            (if (= cur_pc coming_pc)
              (begin 
                (if {read processing_st_mmio} abort pass)
                (set output_alu (alu (# decoded val1 val2))) 
                (set ppc (nextpc (# cur_pc val1)))
                {write expected_pc ppc}
                (if (ismemory decoded)
                  (begin 
                    (set addr_dest (memaddr (# decoded val1)))
                    (if (store decoded)
                      (begin 
                        (set empty_e2w {assume_empty e2w})
                        {write processing_st_mmio 1}
                        (* (set empty_ldQ_sent {assume_empty ldQ_sent}) *)
                        (* (set empty_ldQ_received {assume_empty ldQ_received}) *)
                        {enq to_dmem (# 1 addr_dest val2)}
                        {enq e2w (# 1 coming_pc ppc decoded addr_dest)})
                      (begin 
                        (* (set no_ld_to_addr_sent {assume_no_target ldQ_sent addr_dest}) *)
                        (* (set no_ld_to_addr_received {assume_no_target ldQ_received addr_dest}) *)
                        {enq ldQ_sent addr_dest}
                        {enq to_dmem (# 0 addr_dest 0)}
                        {enq e2w (# 1 coming_pc ppc decoded addr_dest)})))
                  (if (ismmio decoded)
                      (begin 
                        (* MMIO -> No instruction ahead of us  *)
                        {write processing_st_mmio 1}
                        (set empty_e2w {assume_empty e2w})
                        {enq to_mmio (# (mmiostore decoded) val1 val2)}
                        {enq e2w (# 1 coming_pc ppc decoded output_alu)})
                        {enq e2w (# 1 coming_pc ppc decoded output_alu)})))
                (* We poison if it is not the expected instruction! *)
                (begin 
                (* Poisoned instruction still better to not push here *)
                  (if {read processing_st_mmio} abort pass)
                  {enq e2w (# 0 coming_pc 0 decoded output_alu)})))).
    Arguments do_execute /.

    Definition do_writeback :=
      Eval cbv in (rule
        (begin 
          (set (valid coming_pc ppc decoded dest_val) {first e2w})
          {deq e2w}
          (* Always release the scoreboard even for poisoned instruction *)
          (set producedvalue dest_val)
          (if valid
            (begin
              (if (& (ismemory decoded) (~ 1 (store decoded)))
                (begin 
                  (set (addr data) {first from_dmem})
                  {deq ldQ_received}
                  (set producedvalue data)
                  {deq from_dmem})
                (if {read processing_st_mmio} 
                  (begin 
                    (if (& (ismmio decoded) (~ 1 (mmiostore decoded)))
                      (begin 
                       (set producedvalue {first from_mmio})
                        {deq from_mmio})
                    pass)
                    {write processing_st_mmio 0})
                  pass))
              (if (has_destination decoded)
                  {write rf (# (destination decoded) producedvalue)}
                  pass))
              (if (has_destination decoded)
                  {withdraw_write rf (destination decoded)}
                  pass)))).
    Arguments do_writeback /.
    
    Definition enq_dresp :=
        (action_method (addr data)
            (begin 
                (set addr_expected {first ldQ_sent})
                {deq ldQ_sent}
                (if (= addr_expected addr)
                    (begin 
                        {enq ldQ_received addr}
                        {enq from_dmem (# (*addr*) addr  (*data*) data )})
                    abort))).
    Arguments enq_dresp /.

    Definition first_dreq := 
        (fjfj_expr
          {first to_dmem}).
    Arguments first_dreq /.

    Definition deq_dreq := 
        (fjfj_action
          {deq to_dmem}).
    Arguments deq_dreq /.

    Definition enq_mmio :=
        (fjfj_action 
            (begin 
                {enq from_mmio  met_arg}
                )).
    Arguments enq_mmio /.

    Definition mmio_req := 
        (fjfj_expr
          {first to_mmio}).
    Arguments mmio_req /.

    Definition deq_mmio := 
        (fjfj_action
          {deq to_mmio}).
    Arguments deq_mmio /.
      
  Global Instance mkBackend : module _ := 
      module#(rules [do_execute; do_writeback]
              vmet [first_dreq; mmio_req] amet [push_instr; enq_dresp; deq_dreq; enq_mmio; deq_mmio]).

End Backend.

Ltac seq_eexists_prim k := 
    idtac; [eexists;
    let y := (eexists_st_array k) in
    eexists y;
    do 3 eexists| ..].
Ltac local_simpl := 
simpl in *|-; light_clean_propagate; min_straight_line.
Ltac destruct1 := lazymatch goal with 
  | [ H: if ( ?a =? ?b) then _ else _ |- _] =>
    destruct (a =? b) eqn:?; local_simpl
  end.

Ltac autosplit := repeat match goal with 
| [ |- ?a /\ ?b] => split; eauto 
end.

Section DeclarePhi.
    Import Strings.String.

    Inductive in_flight :=
      | Decoded (val1 val2 coming_pc decoded : N)
      | Executed (valid coming_pc ppc decoded dest_val : N). 
    
    Inductive chain_pc : N -> list N -> Prop :=
      | empty : forall pc , chain_pc pc []
      | add_poison : forall ipc x e2w, 
        chain_pc ipc e2w  ->
        dlet {valid coming_pc ppc decoded dest_val} := x in
        (ipc =? coming_pc) = false ->
        valid mod 2 = 0 ->
        chain_pc ipc (e2w ++ [x])
      | add_real  : forall e2w dest_val ppc decoded cur_pc, 
        chain_pc cur_pc e2w ->
        chain_pc ppc (e2w ++ [{# 1 cur_pc ppc decoded dest_val}]).

    Lemma chain_head_only_one : forall head l ipc ,
      chain_pc ipc (head :: l) -> 
      Forall (fun x => split1 x mod 2 = 0) l ->
      split1 head mod 2 = 1 -> split1 (split2 (split2 head)) = ipc.
      intros.
      remember (head::l).
      generalize dependent head.
      generalize dependent l.
      generalize dependent l0.
      induction 1.
      {
        intros.
          inversion Heql0.
      }
      {
        intros.
        destruct l using rev_ind.
        change ([head]) with ([] ++ [head]) in Heql0.
        eapply app_inj_tail_iff in Heql0.
        light_clean_propagate.
        subst valid dest_val decoded coming_pc.
        lia.
        (* rewrite H3 in H0; inversion H0. *)
        rewrite app_comm_cons in Heql0.
        eapply app_inj_tail_iff in Heql0.
        light_clean_propagate.
        eapply Forall_app in H2.
        light_clean_propagate.
        eapply IHchain_pc. 
        apply HA.
        eauto.
        eauto.
      }
      {
        intros.
        destruct l using rev_ind.
        intros.
        change ([head]) with ([] ++ [head]) in Heql0.

        (* rewrite app_comm_cons in Heql0. *)
        eapply app_inj_tail_iff in Heql0.
        light_clean_propagate.
        merge_simpl.
        eauto.
        rewrite app_comm_cons in Heql0.
        eapply app_inj_tail_iff in Heql0.
        light_clean_propagate.
        eapply Forall_app in H0.
        light_clean_propagate.
        inversion HB.
        subst; eauto.
        merge_simpl.
        inversion H3.
      }
      Qed.
 
      
    Definition related (ist : SModule) (sst : SModule) := 
        exists 
            (ipc pc processing_st_mmio cur_s: N)
            (dld: N -> LoadBufferStoresafe.Entry)
            (decode_inst src_val1 src_val2 dest_val : N)
            (to_mmio from_mmio
              e2w d2e 
              (* to_dmem_s *)
              from_dmem to_dmem 
              (* to_mmio_s from_mmio_s  *)
              from_imem 
              ldQ_sent ldQ_received
                : list N)
            (* (from_dmem_s : option N) *)
            (irf : N -> bool * N) 
            (rf : N -> N),
          (* There cannot be outstanding response in the state of sst as those are transitory *)
          (* decode_isnt, src_val1 src_v{enq to_mmio (# (mmiostore decoded) val1 val2)} al2 and dest_val don't matter at all *)
          sst = *[| pc; rf; cur_s; decode_inst; src_val1; src_val2;
                        dest_val; [| tt |]; dld; to_dmem; 
                        (* fifo_from_dmem is always empty on the spec *)
                        @None N;
                        to_mmio; from_mmio; from_imem |]* /\
          ist = *[| ipc; irf; d2e; e2w; ldQ_sent; ldQ_received;
                    to_dmem; from_dmem;
                    to_mmio; from_mmio; processing_st_mmio|]* /\ 
          (* The rf always match *)
          (forall idx, let '(valid, idata) := irf idx in 
                      let sdata := rf idx in
                      idata = sdata) /\
          (* Everything in the from_dmem indicates something in the dld
            to_dmem_s is the same as to_dmem.
            Moreover to_mmio and from_mmio are the same in the two spaces? 
            The first fifo, d2e is basically whatever is in from_imem of the spec!  *)
          Forall2 (fun resp track => 
                    dlet {addr data} := resp in 
                    track = addr) from_dmem ldQ_received /\
          (forall addr, 
          res (dld addr) = map (fun y => dlet {iaddr idata} := y in idata)
                                    (filter (fun x => dlet {iaddr idata} := x in iaddr =? addr) from_dmem)) /\ 
          (forall addr, outI (dld addr) = 0%nat) /\
          Forall2 
            (fun addr y =>
                (* dlet {addr data} := x in  *)
                dlet {valid coming_pc ppc decoded dest_val} := y in 
                addr = dest_val)
            (ldQ_received ++ ldQ_sent)
            (filter (fun x => 
                        dlet {valid coming_pc ppc decoded dest_val} := x in 
                        andb (valid mod 2 =? 1)
                          (andb ((? "ismemory"%string decoded) mod 2 =? 1) ((? "store"%string decoded) mod 2 =? 0))) e2w) /\
          (* (forall addr, (List.length (List.filter (fun x => x =? addr)%N (ldQ_sent ++ ldQ_received)) <= 1)%nat) /\ *)
          (forall addr, outV (dld addr) = List.length (List.filter (fun x => x =? addr)%N ldQ_sent)) /\
          Forall2 (fun x y =>
                  match x with 
                  | Decoded val1 val2 coming_pc decoded =>
                    dlet {coming_pc' data} := y in
                    coming_pc' = coming_pc /\ 
                    (? "decode"%string data) = decoded /\
                    val1 = rf (? "src1"%string decoded) /\
                    val2 = rf (? "src2"%string decoded) /\
                    ((? "has_destination"%string decoded) mod 2 = 1  -> fst (irf (? "destination"%string decoded)) = false)
                  | Executed valid coming_pc ppc decoded dest_val =>
                    dlet {coming_pc' data} := y in
                    ((? "has_destination"%string decoded) mod 2 = 1  -> fst (irf (? "destination"%string decoded)) = false) /\
                    (valid mod 2 = 1 -> 
                    coming_pc' = coming_pc /\ 
                    (? "decode"%string data) = decoded /\
                    let val1 := rf (? "src1"%string decoded) in
                    let val2 := rf (? "src2"%string decoded) in
                    let output_alu := (?"alu"%string {# decoded val1 val2}) in 
                    ppc = (? "nextpc"%string {# coming_pc val1}) /\
                    (((? "ismemory"%string decoded) mod 2 = 0) ->
                      dest_val = output_alu) /\ 
                    (((? "ismemory"%string decoded) mod 2 = 1) ->
                      dest_val = (?"memaddr"%string {# decoded val1}))) /\
                    (valid mod 2 = 0 -> 
                    cur_s = Processor.decode /\ 
                    processing_st_mmio mod 2 = 0 /\
                    coming_pc' = coming_pc /\ 
                    (? "decode"%string data) = decoded) 
                    (* dest_val only makes sense if there is a dest_val *)
                  end)
                  (map (fun x =>
                        dlet {valid coming_pc ppc decoded dest_val}:= x in
                        Executed valid coming_pc ppc decoded dest_val)
                        e2w ++ 
                  (map (fun x =>
                        dlet {val1 val2 coming_pc decoded}:= x in
                        Decoded val1 val2 coming_pc decoded)
                        d2e)) from_imem
                  /\ 
                  (* Three cases: empty pipeline *)
          (e2w = [] -> 
          (* Pipeline is empty *)
            ldQ_sent = [] /\ ldQ_received = [] /\ from_dmem = [] /\ 
            (* to_dmem = [] /\ to_mmio = []/\ *)
            processing_st_mmio mod 2 = 0)
          /\
          (processing_st_mmio mod 2 = 1 ->
          (* Pipeline only contains an MMIO operation,
          we now precisely the state of the machine *)
            cur_s = Processor.writeback /\
            ldQ_sent = [] /\ ldQ_received = [] /\ from_dmem = [] /\
            exists epc ppc decoded dval, e2w = [ {# 1 epc ppc decoded dval} ] /\ 
                decode_inst = decoded /\
                src_val1 = rf (? "src1"%string decoded) /\
                ((? "ismmio"%string decoded) mod 2 = 1 \/
                ((? "ismemory"%string decoded) mod 2 = 1 /\ (? "store"%string decoded) mod 2 = 1)))
          /\
          (processing_st_mmio mod 2 = 0 -> 
          cur_s = Processor.decode /\
          Forall (fun x => dlet {valid coming_pc ppc decoded dest_val}:= x in
                  (valid mod 2 = 0 -> cur_s = Processor.decode /\ processing_st_mmio mod 2 = 0) /\
                  (valid mod 2 = 1 ->
                  (? "ismmio"%string decoded) mod 2 = 0
                  /\
                  ((? "ismemory"%string decoded) mod 2 = 1 -> (? "store"%string decoded) mod 2 = 0))) e2w) /\ 
          (* Chain of PC *)
           (match (filter (fun x => dlet {valid coming_pc ppc decoded dest_val}:= x in
                valid mod 2 =? 1)
                e2w) with 
            | x :: _ => 
                dlet {valid coming_pc ppc decoded dest_val} := x in
                pc = coming_pc /\ 
                chain_pc ipc e2w
            | [] => 
              pc = ipc /\
              chain_pc ipc e2w
            end) /\ 
          (forall l e1 m e2 r, 
           l ++ [e1] ++ m ++ [e2] ++ r 
            = (map (fun x =>
                        dlet {valid coming_pc ppc decoded dest_val}:= x in
                        decoded)
                        e2w ++ 
                  (map (fun x =>
                        dlet {val1 val2 coming_pc decoded}:= x in
                        decoded)
                        d2e)) ->
            (? "has_destination"%string e1) mod 2 = 1 -> 
              (? "destination"%string e1) != (? "src1"%string e2) /\
              (? "destination"%string e1) != (? "src2"%string e2) /\
              ((? "has_destination"%string e2) mod 2 = 1 -> 
                (? "destination"%string e1) != (? "destination"%string e2))).

    Arguments related / ist sst.

Lemma simul_implies_indistinguishable : 
  forall ist sst, related ist sst -> 
      indistinguishable (spec_of Backend.mkBackend) (spec_of Processor.Backend.interface)  ist sst.
  intros.  simpl in H.  light_clean_propagate.
  prove_indistinguishable'.
  3:{
    (* 3: we need to be able to push in both. That should be ok trivially. *)
    light_clean_propagate.
    min_straight_line.
    simpl.
    destruct ( _ =? _ ) eqn:? in HB1.
    {
      min_straight_line; simpl in *|-.
      simpl_applylog.
      assert ((split1 arg) == pc \/ split1 arg != pc).
      blast_arith.
      destruct H;
      eexists; seq_eexists_prim 14%nat; autosplit; reconstruct;
       simpl; eauto; apply_log_fn 14%nat.
    }
    {
      min_straight_line; simpl in *|-.
      simpl_applylog.
      assert ((split1 arg) == pc \/ split1 arg != pc).
      blast_arith.
      destruct H;
      eexists; seq_eexists_prim 14%nat; autosplit; reconstruct;
       simpl; eauto; apply_log_fn 14%nat.
    }
  }
  3:{
    light_clean_propagate.
    min_straight_line.
    min_straight_line; simpl in *|-.
    simpl_applylog.
    simpl.
    eexists.
    seq_eexists_prim 14%nat.
    autosplit.
    reconstruct; split; eauto 6; try lia.
    rm_existentials.
    autosplit.
    simpl.
    clean_arith.
    rewrite HA6.
    rewrite HA13.
    (* Think about how to make that proof go through with egg *)
    (* egg_repeat; simpl. *)
    rewrite N.eqb_refl.
    simpl; lia.
    apply_log_fn 14%nat.
    intros.
    rm_existentials.
    autosplit.
    rewrite HA6.
    clean_arith.
    rewrite HA13.
    rewrite N.eqb_refl.
    simpl; lia.
  }
  3:{
    light_clean_propagate.
    min_straight_line; simpl in *|-.
    simpl_applylog.
    simpl.
    light_clean_propagate.
    eexists.
    seq_eexists_prim 14%nat.
    autosplit.
    reconstruct; split; eauto 6.
    apply_log_fn 14%nat.
  }
  3:{
    light_clean_propagate.
    min_straight_line; simpl in *|-.
    simpl_applylog.
    simpl.
    eexists.
    seq_eexists_prim 14%nat.
    autosplit.
    reconstruct; split; eauto 6.
    apply_log_fn 14%nat.
  }
  3:{ 
    light_clean_propagate.
    min_straight_line; simpl in *|-.
    simpl_applylog.
    simpl.
    light_clean_propagate.
    eexists.
    seq_eexists_prim 14%nat.
    autosplit.
    reconstruct; split; eauto 6.
    apply_log_fn 14%nat.
  }
  { 
    light_clean_propagate.
    min_straight_line.
    simpl.
    light_clean_propagate.
    do 3 eexists.
    split;eauto.
    reconstruct.
  }
  { 
    light_clean_propagate.
    min_straight_line.
    simpl.
    light_clean_propagate.
    do 3 eexists.
    split;eauto.
    reconstruct.
  }
  Time Qed.

End DeclarePhi.


Ltac pre_method := 
      light_clean_propagate;
      simpl in *|-;
      min_straight_line;
      repeat clean_arith;
      light_clean_propagate.

Ltac substep k:= 
      simpl; unfold lift_to;
      let y := eexists_st_array k in
      eexists y; split;
      [ apply f_equal; reflexivity | ]; simpl;
      eexists;
      split; [reflexivity | ].

Ltac step_method_spec n := 
      eexists;
      let y := (eexists_st_array n)in
      eexists y;
      do 3 eexists;
      split;[eauto | ];
      split;[ eauto | ];
      split;
      [ reconstruct |
        (* apply_log_fn n *)
          ].
Import Strings.String.

Lemma imply_forall2 : forall {A B: Type} (xs : list A) (ys : list B) (f g : A -> B -> Prop) ,
      Forall2 f xs ys -> (forall x y,  In x xs -> In y ys -> f x y -> g x y) -> Forall2 g xs ys.
    intros.
    induction H; eauto.
    econstructor; eauto.
    {
      (* pose proof in_cons . *)
      (* Automatically add that guy *)
      assert (forall (A : Type) (a b : A) (l : list A), a =a -> In b l -> In b (a :: l)). intros; eapply in_cons; eauto.
      assert (forall (A : Type) (a : A) (l : list A), a = a -> l = l -> In a (a :: l) ).
      intros; eapply in_eq; eauto.
      clear IHForall2 H1.
      PropLemmas.pose_lemmas_nobh. 
      pose proof (eq_refl l').
      pose proof (eq_refl l).

      (* WE CANNOT Solve that goal with the coquetier because it is a backward reasoning *)
      egg_repeat.

    }
    eapply IHForall2.
    intros.
  (* Automatically add that guy *)
      assert (forall (A : Type) (a b : A) (l : list A), a =a -> In b l -> In b (a :: l)). intros; eapply in_cons; eauto.
      assert (forall (A : Type) (a : A) (l : list A), a = a -> l = l -> In a (a :: l) ).
      intros; eapply in_eq; eauto.
      clear IHForall2 H1.
      PropLemmas.pose_lemmas_nobh. 
      pose proof (eq_refl l').
      pose proof (eq_refl l).
    egg_simpl_goal 3; simpl; eauto.
  Qed.

    Lemma chain_head : forall head l ipc ,
      chain_pc ipc (head :: l) -> chain_pc ipc l.
      intros.
      remember (head::l).
      generalize dependent head.
      generalize dependent l.
      generalize dependent l0.
      induction 1.
      {
        intros.
          inversion Heql0.
      }
      {
        intros.
        destruct l using rev_ind.
        econstructor.
        rewrite app_comm_cons in Heql0.
        eapply app_inj_tail_iff in Heql0.
        light_clean_propagate.
        specialize (IHchain_pc _ _ eq_refl).
        eapply add_poison.
        eauto.
        eauto.
        subst valid.
        eauto.
      }
      {
        intros.
        destruct l using rev_ind.
        econstructor.
        rewrite app_comm_cons in Heql0.
        eapply app_inj_tail_iff in Heql0.
        light_clean_propagate.
        specialize (IHchain_pc _ _ eq_refl).
        eapply add_real.
        eauto.
      }
      Qed.

  Lemma filter_split : forall {A :Type} (f : A -> bool) (l t: list A) (h : A),
      filter f l = h::t  ->
      exists pl sl, l = pl ++ [h] ++ sl  /\ 
      Forall (fun x =>  (f x) = false) pl /\ 
      f h = true 
      .
      induction l.
      {
        intros.
        inversion H.
      }
      {
        intros.
        simpl in H.
        destruct (f a) eqn:?.
        inversion H; subst.
        eexists []. eexists l.
        simpl.
        split; eauto.
        specialize (IHl _ _ H).
        light_clean_propagate.
        eexists (a::pl).
        eexists sl.
        simpl.
        split; eauto.
      }
  Qed.

  Lemma chain_head_only_two : forall head l n sl ipc ,
      chain_pc ipc (head :: l ++ n :: sl) -> 
      Forall (fun x => split1 x mod 2 = 0) l ->
      split1 head mod 2 = 1 -> 
      split1 n mod 2 = 1 -> 
      split1 (split2 (split2 head)) =  split1 (split2 n).
      intros.
      remember (head::l ++ n :: sl).
      generalize dependent head.
      generalize dependent l.
      generalize dependent sl.
      generalize dependent n.
      generalize dependent l0.
      induction 1.
      {
        intros.
        inversion Heql0.
      }
      {
        intros.
        destruct sl using rev_ind.
        rewrite app_comm_cons in Heql0.
        eapply app_inj_tail_iff in Heql0.
        light_clean_propagate.
        subst valid dest_val decoded coming_pc.
        lia.
        subst valid dest_val decoded coming_pc.
        (* rewrite H2 in H0; inversion H0. *)
        rewrite app_comm_cons in Heql0.
        rewrite app_comm_cons in Heql0.
        rewrite app_assoc in Heql0.
        eapply app_inj_tail_iff in Heql0.
        light_clean_propagate.
        eapply IHchain_pc. 
        eauto.
        eauto.
        eauto.
        eauto.
      }
      {
        intros.
        destruct sl using rev_ind.
        intros.
        rewrite app_comm_cons in Heql0.
        eapply app_inj_tail_iff in Heql0.
        light_clean_propagate.
        merge_simpl.
        eapply chain_head_only_one.
        eauto.
        eauto.
        eauto.

        rewrite app_comm_cons in Heql0.
        rewrite app_comm_cons in Heql0.
        rewrite app_assoc in Heql0.
        eapply app_inj_tail_iff in Heql0.
        light_clean_propagate.
        subst; eauto.
      }
      Qed.

    Lemma filter_nil_forall : forall {A: Type} (l : list A) (f : A -> bool), 
      filter f l = [] ->
      Forall (fun x => f x = false) l.
      intros.
      induction l.
      {
        econstructor.
      } 
      {
        simpl in *.
        destruct (f a) eqn:?.
        inversion H.
        econstructor.
        eauto.
        eauto.
      }
      Qed.

    Lemma chain_head_poisoned : forall head l ipc ,
      chain_pc ipc (head :: l) -> 
      split1 head mod 2 = 0 -> 
      Forall (fun x => split1 x mod 2 = 0) l ->
      split1 (split2 head) <> ipc.
      intros.
      remember (head::l).
      generalize dependent head.
      generalize dependent l.
      generalize dependent l0.
      induction 1.
      {
        intros.
        inversion Heql0.
      }
      {
        intros.
        destruct l using rev_ind.
        change ([head]) with ([] ++ [head]) in Heql0.
        eapply app_inj_tail_iff in Heql0.
        light_clean_propagate.
        subst valid dest_val decoded coming_pc.
        clean_arith.
        lia.
        (* rewrite H3 in H0; inversion H0. *)
        rewrite app_comm_cons in Heql0.
        eapply app_inj_tail_iff in Heql0.
        light_clean_propagate.
        eapply Forall_app in H2; light_clean_propagate.
        eapply IHchain_pc. 
        eapply HA.
        eauto.
        eauto.
      }
      {
        intros.
        destruct l using rev_ind.
        intros.
        change ([head]) with ([] ++ [head]) in Heql0.

        (* rewrite app_comm_cons in Heql0. *)
        eapply app_inj_tail_iff in Heql0.
        light_clean_propagate.
        merge_simpl.
        inversion H0.
        eapply Forall_app in H1; light_clean_propagate.
        rewrite app_comm_cons in Heql0.
        eapply app_inj_tail_iff in Heql0.
        light_clean_propagate.
        inversion HB.
        subst.
        merge_simpl.
        inversion H3.
      }
      Qed.
  Lemma chain_head_poisoned_two : forall head l n sl ipc ,
      chain_pc ipc (head :: l ++ n :: sl) -> 
      Forall (fun x => split1 x mod 2 = 0) l ->
      split1 head mod 2 = 0 -> 
      split1 n mod 2 = 1 -> 
      split1 (split2 head) <> split1 (split2 n).
      intros.
      remember (head::l ++ n :: sl).
      generalize dependent head.
      generalize dependent l.
      generalize dependent sl.
      generalize dependent n.
      generalize dependent l0.
      induction 1.
      {
        intros.
        inversion Heql0.
      }
      {
        intros.
        destruct sl using rev_ind.
        rewrite app_comm_cons in Heql0.
        eapply app_inj_tail_iff in Heql0.
        light_clean_propagate.
        subst valid dest_val decoded coming_pc.
        lia.
        subst valid dest_val decoded coming_pc.
        (* rewrite H2 in H0; inversion H0. *)
        rewrite app_comm_cons in Heql0.
        rewrite app_comm_cons in Heql0.
        rewrite app_assoc in Heql0.
        eapply app_inj_tail_iff in Heql0.
        light_clean_propagate.
        eapply IHchain_pc. 
        eauto.
        eauto.
        eauto.
        eauto.
      }
      {
        intros.
        destruct sl using rev_ind.
        intros.
        rewrite app_comm_cons in Heql0.
        eapply app_inj_tail_iff in Heql0.
        light_clean_propagate.
        merge_simpl.
        eapply chain_head_poisoned.
        eauto.
        eauto.
        eauto.

        rewrite app_comm_cons in Heql0.
        rewrite app_comm_cons in Heql0.
        rewrite app_assoc in Heql0.
        eapply app_inj_tail_iff in Heql0.
        light_clean_propagate.
        subst; eauto.
      }
      Qed.

  Context (memory_not_mmio: forall d, (? "ismemory"%string d) mod 2 = 1 -> (? "ismmio"%string d) mod 2 = 0).
  Context (mmiostore_destination: forall d, 
                (? "ismmio"%string d) mod 2 = 1 ->
                (? "mmiostore"%string d) mod 2 = 1 -> (? "has_destination"%string d) mod 2 = 0).
  Context (store_destination: forall d, 
            (? "ismemory"%string d) mod 2 = 1 ->
            (? "store"%string d) mod 2 = 1 -> 
            (? "has_destination"%string d) mod 2 = 0).
  Context (mmioload_destination: forall d, 
                (? "ismmio"%string d) mod 2 = 1 ->
                (? "mmiostore"%string d) mod 2 = 0 -> (? "has_destination"%string d) mod 2 = 1).
  Context (load_destination: forall d, 
            (? "ismemory"%string d) mod 2 = 1 ->
            (? "store"%string d) mod 2 = 0 -> 
            (? "has_destination"%string d) mod 2 = 1).
  Ltac simpl_eqrefl := repeat match goal with 
      | [H: context[?a =? ?a] |- _] =>
        try progress rewrite N.eqb_refl in H
      | [  |- context[?a =? ?a]] =>
        try progress rewrite N.eqb_refl
      end.
  Ltac clearly_absurd :=
    match goal with 
    | [H: ?a :: ?b = [] |- _] => 
        inversion H
    end.
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

  Require Import ArithFacts.
  Theorem correct : refines (spec_of Backend.mkBackend) (spec_of Processor.Backend.interface) related.
  prove_refinement.
  {
    unfold related in *.
    simpl in related_i_s;
    clear indistinguishable_i_s.
    pre_method.
    repeat destruct1.
    {
      pre_method; simpl in * |- .
      print_arrays.
      repeat simpl_applylog.
      repeat clean_arith.
      do 2 eexists; split.
      step_method_spec 14%nat.
      split; eauto 6.
      apply_log_fn 14%nat.
      split.
      eapply existSR_done. 
      assert_related simul_implies_indistinguishable.
      simpl.
      rm_existentials.
      split; eauto.
      print_arrays.
      wrapped_arrays_equal 10%nat.
      split.
      wrapped_arrays_equal 10%nat.
      prove_outside nxt_st; destruct x; eauto.
      split; eauto 7.
      2:{ 
        autosplit.
        rewrite map_app.
        rewrite app_assoc.
        simpl.
        eapply Forall2_app; eauto.
        simpl.
        eapply imply_forall2. 
        eapply HA10.
        simpl; intros.
        destruct x1; split; light_clean_propagate; eauto.
        autosplit.
        intros.
        destruct ( N.eq_dec _ _); eauto.
        destruct ( N.eq_dec _ _); eauto.
        econstructor; eauto.
        simpl.
        merge_simpl.
        autosplit.
        specialize (HA4 (? ("src1"%string) (? ("decode"%string) (split2 arg_method)))).
        rewrite <- HA15 in HA4.
        eapply HA4; eauto.
        specialize (HA4 (? ("src2"%string) (? ("decode"%string) (split2 arg_method)))).
        rewrite <- HA17 in HA4.
        eapply HA4; eauto.
        destruct (N.eq_dec _ _); eauto.
        contradiction.
        {
          intros.
          rewrite map_app in H.
          simpl in H.
          merge_simpl.
          {
            destruct r as [ | ra] eqn:? using rev_ind.
            subst.
            erewrite app_assoc in H. 
            rewrite app_comm_cons in H.
            rewrite app_assoc in H.
            eapply app_inj_tail_iff in H.
            destruct H.
            light_clean_propagate.
            eapply app_eq_app in H.
            light_clean_propagate.
            destruct H.
            {
            light_clean_propagate.
            eapply map_eq_app in HB3.
            light_clean_propagate.
            eapply map_eq_cons in HB3.
            light_clean_propagate.
            eapply Forall2_app_inv_l in HA10.
            light_clean_propagate.
            rewrite map_app in HA10.
            eapply Forall2_app_inv_l in HA10.
            light_clean_propagate.
            inversion HA10.
            subst.
            light_clean_propagate.
            auto_specialize.
            clean_arith.
            erewrite !N.eqb_neq.
            split.
            intro.
            rewrite H in HB4.
            rewrite <- HA15 in HB4.
            simpl in HB4.
            inversion HB4.
            split.
            intro.
            rewrite H in HB4.
            rewrite <- HA17 in HB4.
            simpl in HB4.
            inversion HB4.
            intro.
            intro.
            rewrite H1 in *.
            rewrite  HA16 in HB4.
            simpl in HB4.
            inversion HB4.
            }
            {
            light_clean_propagate.
            eapply map_eq_app in HA.
            light_clean_propagate.
            destruct l2'; simpl in *.
            {
            symmetry in HB3.	
            eapply map_eq_cons in HB3.
            light_clean_propagate.
            rewrite app_nil_r in HA10.
            eapply Forall2_app_inv_l in HA10.
            light_clean_propagate.
            inversion HA10.
            subst.
            light_clean_propagate.
            auto_specialize.
            clean_arith.
            erewrite !N.eqb_neq.
            split.
            intro.
            rewrite H in HB4.
            rewrite <- HA15 in HB4.
            simpl in HB4.
            inversion HB4.
            split.
            intro.
            rewrite H in HB4.
            rewrite <- HA17 in HB4.
            simpl in HB4.
            inversion HB4.
            intro HH.
            intro.
            rewrite H in HB4.
            rewrite HA16 in HB4.
            simpl in HB4.
            inversion HB4.
            }
            {
            inversion HB3; subst.
            eapply Forall2_app_inv_l in HA10.
            light_clean_propagate.
            rewrite map_app in HA.
            eapply Forall2_app_inv_l in HA.
            light_clean_propagate.
            inversion HA.
            subst.
            light_clean_propagate.
            auto_specialize.
            clean_arith.
            erewrite !N.eqb_neq.
            split.
            intro.
            rewrite H in HA19.
            rewrite <- HA15 in HA19.
            simpl in HA19.
            inversion HA19.
            split.
            intro.
            rewrite H in HA19.
            rewrite <- HA17 in HA19.
            simpl in HA19.
            inversion HA19.
            intro HH.
            intro.
            rewrite H in HA19.
            rewrite HA16 in HA19. 
            simpl in HA19.
            inversion HA19.
        }
        }
        rewrite app_comm_cons in H.
        rewrite app_comm_cons in H.
        rewrite app_assoc in H.
        rewrite app_assoc in H.
        rewrite app_assoc in H.
        eapply app_inj_tail_iff in H.
        light_clean_propagate.
        eapply HB0 .
        rewrite <- app_assoc in HA.
        rewrite <- app_comm_cons in HA.
        eauto.
        eauto.
        }
      }
      }
      intros.
      destruct (N.eq_dec _ _); intros; try inversion H.
      2:eapply HA4.
      specialize (HA4 idx).
      rewrite <- e in *.
      rewrite HA20 in *.
      inversion HA16.
      subst.
      eauto.
    }
    {
      pre_method; simpl in * |- .
      repeat simpl_applylog.
      repeat clean_arith.
      do 2 eexists; split.
      step_method_spec 14%nat.
      split; eauto 6.
      apply_log_fn 14%nat.
      split.
      eapply existSR_done. 
      assert_related simul_implies_indistinguishable.
      simpl.
      rm_existentials.
      split; eauto.
      split.
      wrapped_arrays_equal 10%nat.
      prove_outside nxt_st; destruct x; eauto.
      autosplit.
      { 
        rewrite map_app.
        rewrite app_assoc.
        eapply Forall2_app; eauto.
        econstructor; eauto.
        simpl.
        merge_simpl.
        split;eauto.
        split;eauto.
        split.
        specialize (HA4 (? ("src1"%string) (? ("decode"%string) (split2 arg_method)))).
        rewrite <- HA15 in HA4.
        eapply HA4; eauto.
        specialize (HA4 (? ("src2"%string) (? ("decode"%string) (split2 arg_method)))).
        rewrite <- HA17 in HA4.
        split.
        eapply HA4; eauto.
        intros.
        blast_arith.
      }
      intros.
      rewrite map_app in H.
      simpl in H.
      merge_simpl.
      {
        destruct r as [ | ra] eqn:? using rev_ind.
        subst.
        2:{
          erewrite app_assoc in H. 
          rewrite app_comm_cons in H.
          rewrite app_assoc in H.
          rewrite app_comm_cons in H.
          rewrite app_assoc in H.
          eapply app_inj_tail_iff in H.
          light_clean_propagate.
          rewrite <- app_assoc in HA.
          rewrite <- app_comm_cons in HA.
          eapply HB0; eauto.
        }

        erewrite app_assoc in H. 
        rewrite app_comm_cons in H.
        rewrite app_assoc in H.
        eapply app_inj_tail_iff in H.
        light_clean_propagate.
        eapply app_eq_app in HA.
        light_clean_propagate.
        destruct HA.
        {
          light_clean_propagate.
          match goal with 
          | [H : map _ _ = _ ++ _ |- _] => 
            rename H into HB3
          end.
          eapply map_eq_app in HB3.
          light_clean_propagate.
          eapply map_eq_cons in HB3.
          light_clean_propagate.
          eapply Forall2_app_inv_l in HA10.
          light_clean_propagate.
          rewrite map_app in HA10.
          eapply Forall2_app_inv_l in HA10.
          light_clean_propagate.
          inversion HA10.
          subst.
          light_clean_propagate.
          auto_specialize.
          clean_arith.
          erewrite !N.eqb_neq.
          match goal with 
          | [H : fst (rf1 (? "destination"%string _)) = false |- _] => 
            rename H into HB4
          end.
          split.
          intro.
          rewrite H in HB4.
          rewrite <- HA15 in HB4.
          simpl in HB4.
          inversion HB4.
          split.
          intro.
          rewrite H in HB4.
          rewrite <- HA17 in HB4.
          simpl in HB4.
          inversion HB4.
          intro HH.
          intro.
          blast_arith.
        }
        {
          light_clean_propagate.
          let f := fresh HA0 in
          try rename HA0 into f.
          match goal with 
          | [H : map _ _ = _ ++ _ |- _] => 
            rename H into HA0
          end.
          eapply map_eq_app in HA0.
          light_clean_propagate.
          destruct l2'; simpl in *.
          {
            let f := fresh HB3 in
            try rename HB3 into f.
            match goal with 
            | [H : _ :: _ = map _ _|- _] => 
              rename H into HB3
            end.
            symmetry in HB3.	
            eapply map_eq_cons in HB3.
            light_clean_propagate.
            rewrite app_nil_r in HA10.
            eapply Forall2_app_inv_l in HA10.
            light_clean_propagate.
            match goal with
            | [ H: Forall2 _ (_::_) _ |- _] => 
            rename H into HA10
            end.
            inversion HA10.
            subst.
            light_clean_propagate.
            auto_specialize.
            clean_arith.
            erewrite !N.eqb_neq.
            match goal with 
            | [H : fst (rf1 (? "destination"%string _)) = false |- _] => 
              rename H into HB4
            end.
            split.
            intro.
            rewrite H in HB4.
            rewrite <- HA15 in HB4.
            simpl in HB4.
            inversion HB4.
            split.
            intro.
            rewrite H in HB4.
            rewrite <- HA17 in HB4.
            simpl in HB4.
            inversion HB4.
            intro.
            blast_arith.
          }
          {
            let f := fresh HB3 in
            try rename HB3 into f.
            match goal with 
            | [H : (_ :: _) = _ :: (map _ _) ++ _|- _] => 
              rename H into HB3
            end.

            inversion HB3; subst.
            eapply Forall2_app_inv_l in HA10.
            light_clean_propagate.
            rewrite map_app in HA.
            eapply Forall2_app_inv_l in HA.
            light_clean_propagate.
            inversion HA.
            subst.
            light_clean_propagate.
            auto_specialize.
            clean_arith.
            erewrite !N.eqb_neq.
            light_clean_propagate.
            let H19 := fresh yoyo in 
            match goal with 
            | [H : fst (rf1 (? "destination"%string _)) = false |- _] => 
              rename H into H19
            end.
            split.
            intro.
            rewrite H in yoyo.
            rewrite <- HA15 in yoyo.
            simpl in yoyo.
            inversion yoyo.
            split.
            intro.
            rewrite H in yoyo.
            rewrite <- HA17 in yoyo.
            simpl in yoyo.
            inversion yoyo.
            intro.
            blast_arith.
          }
        }
      }
    }
  }
  {
    unfold related in *.
    simpl in related_i_s;
    clear indistinguishable_i_s.
    pre_method.
    simpl in * |- .
    repeat simpl_applylog.
    repeat clean_arith.
    do 2 eexists; split.
    step_method_spec 14%nat.
    autosplit.
    rm_existentials.
    autosplit; simpl; try lia.
    rewrite HA9.
    rewrite N.eqb_refl.
    simpl; lia.
    apply_log_fn 14%nat.
    intros.
    rm_existentials.
    autosplit; simpl; try lia.
    rewrite HA9.
    rewrite N.eqb_refl.
    simpl; lia.
    split.
    eapply existSR_done. 
    assert_related simul_implies_indistinguishable.
    simpl.
    rm_existentials.
    split;eauto.
    split.
    wrapped_arrays_equal 10%nat.
    prove_outside nxt_st; destruct x; eauto.
    autosplit.

    2:{ 
        intros.
        destruct (_ =? _) eqn:?; eauto 6.
        destruct (outI (dld (_))) eqn:?; eauto 6.
        2:{
        exfalso.
        specialize (HA7 (split1 arg_method)).
        lia.
        }
        rewrite filter_app.
        simpl.
        merge_simpl.
        clean_arith.
        light_clean_propagate.
        simpl_eqrefl.
       
        destruct (outV (dld _)) eqn:?; eauto.
        specialize (HA9 (split1 arg_method)).
        simpl_eqrefl.
       
        simpl in *.
        lia.
        simpl.
        erewrite HA6.
        rewrite map_app.
        eauto.
        rewrite filter_app.
        simpl.
        merge_simpl.
        rewrite N.eqb_sym in Heqb.
        rewrite Heqb.
        rewrite app_nil_r.
        eauto.
    }
    2:{
        intros.
        destruct (_ =? _) eqn:?; eauto 6.
        destruct (outI (dld (_))) eqn:?; eauto 6.
        2:{
          exfalso.
          specialize (HA7  ((split1 arg_method))).
          lia.
        }
        destruct (outV (dld _)) eqn:?; simpl; eauto.
    }
    2:{
          eapply Forall2_app_inv_l in HA8.
          light_clean_propagate.
          inversion HA2.
          subst.
          rewrite HB5.
          rewrite <- app_assoc.
          eapply Forall2_app; eauto.
    }
    2:{
        intros.
        destruct (_ =? _) eqn:?; eauto 6.
        destruct (outI (dld (_))) eqn:?; eauto 6.
        2:{
        exfalso.
        specialize (HA7  (  (split1 arg_method))).
        lia.
        }
        destruct (outV (dld _)) eqn:?; simpl; eauto.
        clean_arith.
        light_clean_propagate.
        specialize (HA9 (split1 arg_method)).
        rewrite Heqn0 in HA9.
        simpl_eqrefl.
        simpl in HA9; inversion HA9.
        clean_arith.
        light_clean_propagate.
        specialize (HA9 (split1 arg_method)).
        rewrite Heqn0 in HA9.
        simpl_eqrefl.
        simpl in HA9; lia.
        specialize (HA9 addr).
        rewrite N.eqb_sym in Heqb.
        rewrite Heqb in HA9.
        simpl in HA9.
        lia.
    }
    2:{
        intros.
        auto_specialize.
        light_clean_propagate; eauto.
        clearly_absurd.
    }
    2:{
        intros.
        auto_specialize.
        light_clean_propagate; eauto.
        clearly_absurd.
    }
    { 
      eapply Forall2_app; eauto.
      econstructor; merge_simpl; eauto.
    }
  }
  {
    unfold related in *.
    simpl in related_i_s;
    clear indistinguishable_i_s.
    pre_method.
    repeat destruct1.
    {
      pre_method; simpl in * |- .
      repeat simpl_applylog.
      repeat clean_arith.
      do 2 eexists; split.
      step_method_spec 14%nat.
      split; eauto 6.
      apply_log_fn 14%nat.
      split.
      eapply existSR_done. 
      assert_related simul_implies_indistinguishable.
      simpl.
      rm_existentials.
      autosplit.
      wrapped_arrays_equal 10%nat.
      prove_outside nxt_st; destruct x; eauto.
    }
  }
  {
    unfold related in *.
    simpl in related_i_s;
    clear indistinguishable_i_s.
    pre_method.
    repeat destruct1.
    {
      pre_method; simpl in * |- .
      repeat simpl_applylog.
      repeat clean_arith.
      do 2 eexists; split.
      step_method_spec 14%nat.
      autosplit.
      apply_log_fn 14%nat.
      split.
      eapply existSR_done. 
      assert_related simul_implies_indistinguishable.
      simpl.
      rm_existentials.
      autosplit.
      wrapped_arrays_equal 10%nat.
      prove_outside nxt_st; destruct x; eauto.
    }
  }
  {
    unfold related in *.
    simpl in related_i_s;
    clear indistinguishable_i_s.
    pre_method.
    repeat destruct1.
    {
      pre_method; simpl in * |- .
      repeat simpl_applylog.
      repeat clean_arith.
      do 2 eexists; split.
      step_method_spec 14%nat.
      autosplit.
      apply_log_fn 14%nat.
      split.
      eapply existSR_done. 
      assert_related simul_implies_indistinguishable.
      simpl.
      rm_existentials.
      autosplit.
      wrapped_arrays_equal 10%nat.
      prove_outside nxt_st; destruct x; eauto.
    }
  }
  Time Optimize Proof.
  {
    (* Exec -> In most cases, do nothing, only do something when *)
    unfold related in *.
    simpl in related_i_s;
    clear indistinguishable_i_s.
    pre_method.

  Time symb_ex_split.

 
    (* user_cleanup *)
    2:{
      light_clean_propagate.
      assert (n0 mod 2 = 0) by blast_arith.
      auto_specialize.
      light_clean_propagate.
      eapply Forall2_app_inv_l in HA10.
      light_clean_propagate.
      inversion HA10.
      light_clean_propagate.
      simpl in *.
      light_clean_propagate.
      eexists.
      (* This is a load, so we need to simulate with a NDL *)
      split.
      eapply existSR_step with (r:= 0%nat).
      simpl.
      rm_existentials.
      split; eauto.
      split; eauto.
      split; eauto.
      reconstruct.
      split; eauto.
      split; eauto.
      unshelve instantiate (1:= _).
      let y := (eexists_st_array 14%nat) in
      exact y.
      apply_log_fn 14%nat.
      eapply existSR_done.
      assert_related simul_implies_indistinguishable.
      rm_existentials.
      split; eauto.
      wrapped_arrays_equal 10%nat.
      split; eauto.
      wrapped_arrays_equal 10%nat.
      prove_outside nxt_st; destruct x; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      {
        intros.
        destruct (addr =? ? "memaddr"%string {#(split2 (split2 (split2 head))) (split1 head)}) eqn:?; simpl;eauto.
        erewrite HA6.
        clean_arith.
        rewrite Heqb.
        eauto.
      }
      split; eauto.
      intros.
      destruct (_ =? _) eqn:?; simpl;eauto.
      clean_arith.
      light_clean_propagate.
      split; eauto.
      {
        rewrite filter_app.
        simpl.
        merge_simpl.
        simpl.
        rewrite Heqb1.
        assert ((? "store"%string
           (split2 (split2 (split2 head)))
         mod 2 = 0)) by blast_arith.
        rewrite H0.
        simpl.
        rewrite app_assoc.
        eapply Forall2_app; eauto.
        econstructor; eauto.
        merge_simpl; eauto.
      }
      split; eauto.
      intros.
      destruct (addr =? ? "memaddr"%string {#(split2 (split2 (split2 head))) (split1 head)}) eqn:?; simpl;eauto.
      rewrite filter_app.
      rewrite app_length.
      simpl.
      rewrite N.eqb_sym in Heqb.
      rewrite Heqb.
      simpl.
      erewrite HA9.
      clean_arith.
      rewrite Heqb.
      eauto.
      rewrite filter_app.
      (* rewrite filter_app. *)
      rewrite app_length.
      erewrite HA9.
      simpl.
      rewrite N.eqb_sym in Heqb.
      rewrite Heqb.
      simpl; eauto.
      split; eauto.
      {
      rewrite map_app.
      simpl.
      merge_simpl.
      rewrite <- app_assoc.
      eapply Forall2_app; eauto.
      (* rewrite <- H1. *)
      econstructor; eauto.
      split; eauto.
      split; eauto.
      intros.
      split; eauto.
      split.
      intros.
      blast_arith.
      intros.
      rewrite HA16; eauto.
      split; eauto.
      intros; lia.
      }
      split; eauto.
      econstructor; eauto.
      destruct l4; inversion H0.
      split; eauto.
      destruct l4; inversion H0.
      destruct l4; inversion H0.
      split; eauto.
      intros; eauto.
      split;eauto.
      intros; blast_arith.
      split;eauto.
      intros; blast_arith.
      intros; blast_arith.
      split;eauto.
      intros.
      split; eauto 7.
      eapply Forall_app; split;eauto.
      econstructor; eauto.
      merge_simpl.
      intros; eauto.
      split.
      intros.
      inversion H1.
      intros.
      split.
      eapply memory_not_mmio; eauto.
      intros.
      blast_arith.
      rewrite filter_app.
      simpl.
      merge_simpl.
      simpl.
      split; merge_simpl; simpl; eauto.
      match goal with 
      |  |- context[filter ?a ?b] => 
      destruct (filter a b) eqn:?
      end; simpl; eauto.
      { 
        light_clean_propagate.
        merge_simpl; simpl.
        split.
        lia.
        eapply add_real.
        eauto.
      }
      {
        light_clean_propagate.
        merge_simpl; simpl.
        split.
        lia.
        eapply add_real.
        eauto.
      }
      intros.
      {
        subst.
        rename H into foo.
        match goal with 
        | [Ha: _ = map _ _ ++ map _ _ |- _] => 
          rename Ha into H
        end.
        erewrite map_app in H.
        simpl in H.
        merge_simpl.
        (* rewrite app_comm_cons in H. *)
        rewrite <- app_assoc in H.
        simpl in H.
        eapply HB0.
        eauto.
        eauto.
      }
    }
    {
      inversion HA10.
      light_clean_propagate.
      auto_specialize; light_clean_propagate.
      auto_specialize; light_clean_propagate.
      eexists.
      split.
      (* We should do everything here *)
      eapply existSR_step with (r:= 1%nat).
      2:eapply existSR_step with (r:= 2%nat). 
      simpl.
      rm_existentials.
      split; eauto.
      split; eauto.
      split.
      reconstruct.
      simpl; blast_arith.
      eapply DIft.
      reconstruct.
      simpl.
      clean_arith.
      (* admit. *)
      arithmetic_hammer.
      reconstruct; simpl; eauto.
      merge_simpl;simpl.
      unshelve instantiate (1:= _).
      let y := (eexists_st_array 14%nat) in
      exact y.
      apply_log_fn 14%nat.
      simpl.
      rm_existentials.
      split; eauto.
      split; eauto.
      split.
      reconstruct.
      simpl; blast_arith.
      simpl; eauto.
      eapply DIft.
      reconstruct.
      simpl.
      change irf with (fun x => irf x) in array_ext8.
      egg_repeat.
      reconstruct.
      eapply DIft.
      reconstruct.
      simpl.
      change irf with (fun x => irf x) in array_ext8.
      egg_repeat.
      reconstruct.
      simpl; eauto 7.
      simpl; eauto 7.
      simpl; eauto 7.
      unshelve instantiate (1:= _).
      let y := (eexists_st_array 14%nat) in
      exact y.
      apply_log_fn 14%nat.
      eapply existSR_done.
      assert_related simul_implies_indistinguishable.
      rm_existentials.
      split; eauto.
      wrapped_arrays_equal 10%nat.
      split; eauto.
      wrapped_arrays_equal 10%nat.
      change irf with (fun x => irf x) in array_ext8.
      egg_elim 5 values .
      simpl; eauto.
      prove_outside nxt_st; destruct x; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      intros.
      destruct (addr =? _) eqn:?; simpl;eauto.
      rewrite HA7.
      simpl; eauto.
      erewrite HA9.
      simpl; eauto.
      split; eauto.
      light_clean_propagate.
      simpl; eauto.
      destruct (addr =? _) eqn:?; simpl;eauto.
      erewrite HA14; simpl; eauto.
      merge_simpl.
      simpl.
      merge_simpl.
      simpl.
      merge_simpl.
      split; eauto.
      rewrite Heqb1.
      rewrite Heqb2.
      simpl; eauto.
      split; eauto.
      simpl.
      intros.
      destruct (addr =? _) eqn:?; simpl;eauto.
      erewrite HA15.
      simpl; eauto.
      split; eauto.
      econstructor; eauto.
      split; eauto.
      rewrite HA14.
      rewrite HA0.
      split; eauto.
      split; eauto; intros.
      split; eauto; intros.
      split; eauto; intros.
      change irf with (fun x => irf x) in array_ext8.
      egg_repeat.
      split; eauto.
      intros.
      change irf with (fun x => irf x) in array_ext8.
      egg_repeat.
      intros.
      change irf with (fun x => irf x) in array_ext8.
      egg_repeat.
      (* intros.
      inversion H.  *)
      {
        eapply imply_forall2.
        eauto.
        intros.
        destruct x.
        {
          light_clean_propagate.
          split; eauto.
        }
        {
          eapply in_map_iff in H.
          light_clean_propagate.
          change irf with (fun x => irf x) in array_ext8.
          egg_repeat.
        }
      }
      split.
      intro H; inversion H.
      split; eauto.
      2:split; eauto.
      2:simpl; intro A; inversion A.
      intros.
      split; eauto 7.
      split; eauto 7.
      split; eauto 7.
      split; eauto 7.
      light_clean_propagate; repeat auto_specialize.
      rm_existentials.
      split; eauto.
      split; eauto.
      light_clean_propagate.
      split; eauto.
      change irf with (fun x => irf x) in array_ext8.
      egg_repeat.
      cbv beta.
      (* split; eauto.
      split; eauto. *)
      match goal with 
      | |- context[ [?a]]=> change [a] with ([] ++ [a])
      end. 
      eapply add_real.
      eauto.
      egg_repeat.
    }
    {
      inversion HA10.
      light_clean_propagate.
      auto_specialize; light_clean_propagate.
      auto_specialize; light_clean_propagate.
      eexists.
      split.
      eapply existSR_step with (r:= 1%nat).
      2:eapply existSR_step with (r:= 2%nat). 
      simpl.
      rm_existentials.
      split; eauto.
      split; eauto.
      split.
      reconstruct.
      simpl; blast_arith.
      eapply DIft.
      reconstruct.
      simpl.
      clean_arith.
      (* admit. *)
      arithmetic_hammer.
      reconstruct; simpl; eauto.
      merge_simpl;simpl.
      unshelve instantiate (1:= _).
      let y := (eexists_st_array 14%nat) in
      exact y.
      apply_log_fn 14%nat.
      simpl.
      rm_existentials.
      split; eauto.
      split; eauto.
      split.
      reconstruct.
      simpl; blast_arith.
      simpl; eauto.
      eapply DIff.
      reconstruct.
      simpl.
      change irf with (fun x => irf x) in array_ext8.
      egg_repeat.
      simpl.
      blast_arith.
      eapply DIft.
      reconstruct.
      simpl.
      change irf with (fun x => irf x) in array_ext8.
      egg_repeat.
      reconstruct.
      simpl; eauto 7.
      simpl; eauto 7.
      unshelve instantiate (1:= _).
      let y := (eexists_st_array 14%nat) in
      exact y.
      apply_log_fn 14%nat.
      eapply existSR_done.
      assert_related simul_implies_indistinguishable.
      rm_existentials.
      split; eauto.
      wrapped_arrays_equal 10%nat.
      split; eauto.
      wrapped_arrays_equal 10%nat.
      change irf with (fun x => irf x) in array_ext8.
      egg_elim 5 values.
      simpl; eauto.
      prove_outside nxt_st; destruct x; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      simpl.
      merge_simpl.
      simpl.
      assert (? "ismemory"%string
          (split2 (split2 (split2 head)))
        mod 2 = 0) by blast_arith.
      rewrite H.
      simpl.
      econstructor.
      split; eauto.
      simpl.
      merge_simpl.
      split; eauto.
      econstructor.
      intros.
      split; eauto.
      split; eauto.
      2:{
        intro yo; inversion yo.
      }
      split; eauto.
      split; eauto.
      split.
      intros.
      change irf with (fun x => irf x) in array_ext8.
      egg_repeat.
      split.
      intros.
      change irf with (fun x => irf x) in array_ext8.
      egg_repeat.
      intros.
      blast_arith.
      {
      eapply imply_forall2.
      eauto.
      intros.
      destruct x.
      {
        light_clean_propagate.
        split; eauto.
      }
      {
        eapply in_map_iff in H.
        light_clean_propagate.
        change irf with (fun x => irf x) in array_ext8.
        egg_repeat.
      }
      }
      split.
      intros.
      inversion H.
      split; eauto 7.
      intros.
      split; eauto 7.
      split; eauto 7.
      split; eauto 7.
      split; eauto 7.
      rm_existentials.
      split; eauto 7.
      split; eauto 7.
      split; eauto 7.
      change irf with (fun x => irf x) in array_ext8.
      egg_repeat.
      split; eauto.
      intro H; inversion H.
      simpl.
      merge_simpl.
      simpl.
      merge_simpl.
      split; eauto.
      split; eauto.
      match goal with 
      | |- context[ [?a]]=> change [a] with ([] ++ [a])
      end.
      eapply add_real.
      eauto.
    }
    {
      (* std inst *)
      simpl in *.
      light_clean_propagate.
      eexists.
      split.
      eapply existSR_done.
      assert_related simul_implies_indistinguishable.
      rm_existentials.
      split; eauto.
      split; eauto.
      wrapped_arrays_equal 10%nat.
      prove_outside nxt_st; destruct x; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      rewrite filter_app.
      simpl.
      merge_simpl.
      simpl.
      assert (? "ismemory"%string
          (split2 (split2 (split2 head)))
        mod 2 = 0) by blast_arith.
      rewrite H.
      simpl.
      rewrite app_nil_r.
      eauto.
      split; eauto.
      split; eauto.
      2:{ 
        split; eauto.
        intros.
        assert (List.length (@nil N) = List.length []) by reflexivity.
        rewrite <- H in H0 at 1.
        rewrite app_length in H0.
        simpl in H0.
        lia.
        split; eauto.
        intros.
        lia.
        split; eauto.
        intros.
        auto_specialize; light_clean_propagate; eauto.
        split; eauto.
        eapply Forall_app.
        split; eauto.
        econstructor; eauto.
        merge_simpl.
        intros.
        blast_arith.
        assert (n0 mod 2 = 0) by blast_arith.
        auto_specialize.
        light_clean_propagate.
        rewrite filter_app.
        split; eauto.
        match goal with 
        | |- context[filter ?a l2] =>
        destruct (filter a l2) eqn:? 
        end; simpl; eauto.
        {
        merge_simpl; simpl.
        merge_simpl.
        light_clean_propagate.
        split; eauto.
        match goal with 
        | |- context[ [?a]]=> change [a] with ([] ++ [a])
        end.
        eapply add_real.
        eauto.
        }
        {
        merge_simpl; simpl.
        merge_simpl.
        light_clean_propagate.
        split; eauto.
        eapply add_real.
        eauto.
        }
        merge_simpl; simpl.
        merge_simpl.
        eauto.
        intros.
        {
          subst.
          rename H into foo.
          match goal with 
          | [Ha: _ = map _ _ ++ map _ _ |- _] => 
            rename Ha into H
          end. 
          erewrite map_app in H. 
          simpl in H.
          merge_simpl.
          (* rewrite app_comm_cons in H. *)
          rewrite <- app_assoc in H.
          simpl in H.
          eapply HB0.
          eauto.
          eauto.
        }
      }
      assert (n0 mod 2 = 0) by blast_arith.
      auto_specialize.
      rewrite map_app.
      simpl.
      merge_simpl.
      simpl in *.
      eapply Forall2_app_inv_l in HA10.
      light_clean_propagate.
      inversion HA10.
      light_clean_propagate.
      rewrite <- app_assoc.
      eapply Forall2_app.
      eauto.
      econstructor; eauto.
      (* eapply Forall2_app; eauto. *)
      (* econstructor;eauto. *)
      intros.
      merge_simpl.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      change irf with (fun x => irf x) in array_ext8; egg_repeat.
      split; eauto; intros.
      change irf with (fun x => irf x) in array_ext8; egg_repeat.
      blast_arith.
    }
    {
      (* Poisoned instruction, nothing to do on spec side *)
      simpl in *.
      light_clean_propagate.
      eexists.
      split.
      eapply existSR_done.
      assert_related simul_implies_indistinguishable.
      rm_existentials.
      split; eauto.
      split; eauto.
      wrapped_arrays_equal 10%nat.
      prove_outside nxt_st; destruct x; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      {
        assert (n0 mod 2 = 0) by blast_arith.
        auto_specialize.
        light_clean_propagate.
        rewrite filter_app.
        simpl.
        merge_simpl.
        simpl.
        rewrite app_nil_r.
        eauto.
      }
      split; eauto.
      split; eauto.
      2:{ 
        split; eauto.
        intros.
        assert (List.length (@nil N) = List.length []) by reflexivity.
        rewrite <- H in H0 at 1.
        rewrite app_length in H0.
        simpl in H0.
        lia.
        split; eauto.
        intros.
        lia.
        split; eauto.
        intros.
        auto_specialize; light_clean_propagate; simpl; eauto.
        split; eauto 7.
        eapply Forall_app.
        split; eauto.
        econstructor; eauto.
        merge_simpl.
        intros.
        blast_arith.
        assert (n0 mod 2 = 0) by blast_arith.
        auto_specialize.
        light_clean_propagate.
        split.
        rewrite filter_app.
        match goal with 
        | |- context[filter ?a l2] =>
        destruct (filter a l2) eqn:? 
        end; simpl; eauto.
        {
        merge_simpl; simpl.
        merge_simpl.
        light_clean_propagate.
        split; eauto.
        eapply add_poison.
        eauto.
        all:merge_simpl; eauto.
        clean_arith.
        rewrite N.eqb_neq.
        eauto.
        }
        {
        merge_simpl; simpl.
        merge_simpl.
        light_clean_propagate.
        split; eauto.
        eapply add_poison.
        eauto.
        all:merge_simpl; eauto.
        rewrite N.eqb_neq.
        eauto.
        }
        merge_simpl; simpl.
        merge_simpl.
        eauto.
        intros.
        {
          subst.
          rename H into foo.
          match goal with 
          | [Ha: _ = map _ _ ++ map _ _ |- _] => 
            rename Ha into H
          end. 
          erewrite map_app in H. 
          simpl in H.
          merge_simpl.
          rewrite <- app_assoc in H.
          simpl in H.
          eapply HB0.
          eauto.
          eauto.
        }
      }
      rewrite map_app.
      simpl.
      merge_simpl.
      simpl in *.
      eapply Forall2_app_inv_l in HA10.
      light_clean_propagate.
      inversion HA10.
      light_clean_propagate.
      assert (n0 mod 2 = 0) by blast_arith.
      auto_specialize.
      light_clean_propagate.
      rewrite <- app_assoc.
      eapply Forall2_app.
      eauto.
      econstructor; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      intros; blast_arith.
    }
  }
  Time Optimize Proof.
  {
    unfold related in *.
    simpl in related_i_s;
    clear indistinguishable_i_s.
    pre_method.
    Time symb_ex_split.
    {
      inversion HA5.
      subst.
      merge_simpl.
      inversion HA10.
      light_clean_propagate.
      repeat auto_specialize.
      light_clean_propagate.
      repeat auto_specialize.
      (* rewrite Heqb in HA14. *)
      simpl in *.
      light_clean_propagate.
      repeat auto_specialize.
      assert (? "ismemory"%string (split1 (split2 (split2 (split2 head)))) mod 2 = 1).
      eapply land_mod2_true in Heqb0.
      eauto.
      assert (? "store"%string (split1 (split2 (split2 (split2 head))))
       mod 2 = 0).
      {
        repeat auto_specialize.
        rewrite N.land_comm in Heqb0.
        eapply land_mod2_true in Heqb0.
        eapply lnot_mod2' in Heqb0.
        eauto.
      }
      auto_specialize.
      rewrite Heqb in HA14.
      rewrite H in HA8.
      rewrite H0 in HA8.
      simpl in HA8.
      inversion HA8.
      simpl in HA14.
      light_clean_propagate.
      rewrite Heqb in H5; simpl in H5; inversion H5; subst.
      assert (processing_st_mmio mod 2 = 1 \/ processing_st_mmio mod 2 = 0) by blast_arith.
      destruct H1.
      {
        repeat auto_specialize.
        light_clean_propagate.
        inversion HA20.
      }
      repeat auto_specialize; light_clean_propagate.
      subst.
      (* rewrite Heqb in H5; simpl in H5; inversion H5. *)
      (* subst. *)
      eexists.
      (* auto_specialize. *)
      light_clean_propagate.
      (* This is a load, so we need to simulate with a NDL *)
      split.
      (* It is a load instruction, we can run it completely *)
      eapply existSR_step with (r:= 1%nat).
      2:eapply existSR_step with (r:= 2%nat).
      3:eapply existSR_step with (r:= 3%nat).
      4:eapply existSR_substep with (instance_i := 8%nat) (r:= 0%nat).
      simpl.
      rm_existentials.
      split; eauto.
      split; eauto.
      split; eauto.
      reconstruct.
      simpl; eauto.
      eapply DIft.
      reconstruct.
      simpl; eauto.
      clean_arith.
      egg_repeat.
      simpl.
      arithmetic_hammer.
      reconstruct.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      unshelve instantiate (1:= _).
      let y := (eexists_st_array 14%nat) in
      exact y.
      apply_log_fn 14%nat.
      simpl.
      rm_existentials.
      split; eauto.
      split; eauto.
      split; eauto.
      reconstruct.
      simpl; eauto.
      split; eauto.
      eapply DIft.
      reconstruct.
      simpl; eauto.
      egg_repeat.
      reconstruct.
      eapply DIff.
      reconstruct.
      simpl.
      egg_repeat.
      reconstruct.
      erewrite HA6.
      simpl.
      subst.
      rewrite H6.
      rewrite HB7.
      rewrite HA15.
      rewrite N.eqb_refl.
      simpl.
      eauto.
      simpl.
      merge_simpl; eauto.
      split; eauto 7.
      split; eauto 7.
      unshelve instantiate (1:= _).
      let y := (eexists_st_array 14%nat) in
      exact y.
      apply_log_fn 14%nat.
      simpl.
      rm_existentials.
      split; eauto.
      split; eauto.
      split; eauto.
      reconstruct.
      simpl; eauto.
      split; eauto.
      split; eauto.
      eapply DIft.
      reconstruct.
      simpl; eauto.
      egg_repeat.
      reconstruct.
      split;eauto.
      eapply DIft.
      reconstruct.
      simpl.
      egg_repeat.
      reconstruct.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      unshelve instantiate (1:= _).
      let y := (eexists_st_array 14%nat) in
      exact y.
      apply_log_fn 14%nat.
      simpl; eauto.
      simpl; eauto.
      unfold lift_to; simpl.
      rm_existentials.
      split; eauto.
      rm_existentials.
      split; eauto.
      rm_existentials.
      simpl.
      split; eauto.
      eapply existSR_done.
      assert_related simul_implies_indistinguishable.
      rm_existentials.
      split; eauto.
      wrapped_arrays_equal 10%nat.
      split; eauto.
      wrapped_arrays_equal 10%nat.
      prove_outside nxt_st; destruct x; eauto.
      merge_simpl.
      split; eauto.
      intros.
      destruct (N.eq_dec _ _); eauto.
      rewrite HA15.
      rewrite e.
      destruct (N.eq_dec _ _).
      2:{ contradiction. }
      intros.
      eauto.

      rewrite HA15.
      destruct (N.eq_dec _ _).
      contradiction. 
      eapply HA4.
      split; eauto.
      (* rewrite Heqb in H5; inversion H5; subst. *)
      split; eauto.
      instantiate (1:= split1 head4).
      2: split;eauto.
      3: split;eauto.
      3: split;eauto.
      intros.
      {
        intros.
        destruct (addr =? _) eqn:?; simpl;eauto.
        erewrite HA6.
        clean_arith.
        rewrite Heqb2.
        rewrite N.eqb_refl.
        simpl.
        eauto.
        erewrite HA6.
        rewrite N.eqb_sym in Heqb2.
        rewrite Heqb2.
        eauto. 
      }
      {
        intros.
        destruct (addr =? _) eqn:?; simpl;eauto.
      }

      intros.
      destruct (addr =? _) eqn:?; simpl;eauto.
      clean_arith.
      light_clean_propagate.
      split; eauto.
      {
      eapply imply_forall2.
      eauto.
      intros.
      repeat auto_specialize.
      eapply in_split in H2.
      light_clean_propagate.
      eapply app_eq_app in H2.
      light_clean_propagate.
      destruct H2.
      {
        light_clean_propagate.
        eapply map_eq_app in HA0.
        light_clean_propagate.
        destruct l2'.
        {
          (* rename HB8 into HB9. *)
          simpl in HB9.
          symmetry in HB9.
          eapply map_eq_cons in HB9.
          light_clean_propagate.
          specialize (HB0 [] (split1 (split2 (split2 (split2 head))))).
          rewrite map_app in HB0. 
          simpl in HB0.
          rewrite app_nil_r in HB0.
          specialize (HB0 (
            map (fun x : N => split1 (split2 (split2 (split2 x)))) l1')). 
          simpl in HB0.
          specialize (HB0 _ _ eq_refl).
          auto_specialize.
          clean_arith.
          light_clean_propagate.
          rewrite HA0 in *.
          rewrite HA15 in *.
          destruct (N.eq_dec _ _); 
          destruct (N.eq_dec _ _);
          destruct (N.eq_dec _ _).
          all:  try match goal with 
            | [ H : ?a = ?b, H' : ?a <> ?b |- _ ] =>
              specialize (H' H); contradiction H' 
            end.
          lia.
          rewrite HA20.
          rewrite HA13.
          split; try reflexivity.
          split; try reflexivity.
          split; try lia.
          split; try lia.
          intros; repeat auto_specialize.
          eauto.
        }
        {
          (* rename HB8 into HB9. *)
          simpl in HB9.
          inversion HB9.
          subst.
          merge_simpl.
          specialize (HB0 [] (split1 (split2 (split2 (split2 head))))).
          rewrite map_app in HB0. 
          simpl in HB0.
          specialize (HB0 (
            map (fun x : N => split1 (split2 (split2 (split2 x)))) l1')). 
          simpl in HB0.
          rewrite <- app_assoc in HB0.
          specialize (HB0 _ _ eq_refl).
          repeat auto_specialize.
          clean_arith.
          light_clean_propagate.
          rewrite HA15 in *.
          repeat auto_specialize.
          simpl in *.
          destruct (N.eq_dec _ _); 
          destruct (N.eq_dec _ _);
          destruct (N.eq_dec _ _). 
          all:  try match goal with 
            | [ H : ?a = ?b, H' : ?a <> ?b |- _ ] =>
              specialize (H' H); contradiction H' 
            end.
          split.
          intros.
          repeat auto_specialize.
          try match goal with 
            | [ H : ?a = ?b, H' : ?a <> ?b |- _ ] =>
              specialize (H' H); contradiction H' 
            end.
          intros.
          repeat auto_specialize.
          light_clean_propagate.
          split; eauto.
          split; eauto.
        }
      }
      {
        light_clean_propagate.
        eapply map_eq_app in HB9.
        light_clean_propagate.
        eapply map_eq_cons in HB9.
        light_clean_propagate.
        specialize (HB0 [] (split1 (split2 (split2 (split2 head))))).
        rewrite map_app in HB0. 
        simpl in HB0.
        specialize (HB0 (map (fun x : N => split1 (split2 (split2 (split2 x)))) l ++
           map (fun x : N => split2 ((split2 (split2 x)))) l1')). 
        simpl in HB0.
        rewrite app_assoc in HB0.
        specialize (HB0 _ _ eq_refl).
        repeat auto_specialize.
        clean_arith.
        light_clean_propagate.
        rewrite HA15 in *.
        rewrite HA20 in *.
        rewrite HA13 in *.
        (* rewrite HA0 in *. *)
        destruct (N.eq_dec _ _); 
        destruct (N.eq_dec _ _);
        destruct (N.eq_dec _ _);
        try match goal with 
            | [ H : ?a = ?b, H' : ?a <> ?b |- _ ] =>
              specialize (H' H); contradiction H' 
            end.
        try lia.
        split; eauto.
      }
    }
    rewrite Heqb in HA8.
    split; eauto.
    intros; light_clean_propagate.
    simpl in HA8.
    inversion HA8.
    subst.
    inversion H12.
    symmetry in H8.
    eapply app_eq_nil in H8.
    light_clean_propagate.
    inversion H4.
    split; eauto.
    split; eauto.
    intros; lia.
    split; eauto.
    split; eauto.
    inversion HB8; eauto.
    split; eauto.
    {
      light_clean_propagate.
      match goal with 
      | |- context[filter ?f ?l] =>
        destruct (filter f l) eqn:?
      end.
      split; eauto.
      2:eapply chain_head; eauto.
      rewrite HA15.
      rewrite <- HA18.
      assert (Forall (fun x => split1 x mod 2 = 0 ) l).
      {
        pose proof @filter_nil_forall.
        specialize (H2 _ _ _ Heql0).
        eapply Forall_forall; intros.
        eapply Forall_forall in H2; eauto.
        clean_arith.
        blast_arith.
      }
      light_clean_propagate.
      eapply chain_head_only_one; eauto.
     
      split; eauto.
      2:eapply chain_head; eauto.
      rewrite HA15.
      rewrite <- HA18.
      assert (exists  pl sl, l = pl ++  [n] ++ sl /\ Forall (fun x => split1 x mod 2 = 0 ) pl /\ split1 n mod 2 = 1).
      {
        pose proof @filter_split.
        specialize (H2 _ _ _ _ _ Heql0).
        light_clean_propagate.
        eexists. eexists.
        simpl.
        split; eauto.
        clean_arith.
        split; eauto.
        eapply Forall_forall.
        intros.
        eapply Forall_forall in HA13; eauto.
        clean_arith.
        blast_arith.
      }
      light_clean_propagate.
      rewrite map_app in H3.
      eapply Forall2_app_inv_l in H3.
      light_clean_propagate.
      eapply Forall2_app_inv_l in HA0.
      light_clean_propagate.
      inversion HA0.
      subst.
      light_clean_propagate.
      repeat auto_specialize.
      light_clean_propagate.
      eapply chain_head_only_two; eauto.
    }
    intros.
    eapply HB0; eauto.
    rewrite <- H2.
    rewrite <- app_comm_cons.
    eauto.
    }
    {
      rewrite Heqb in *.
      simpl in *.
      inversion HA10.
      subst.
      light_clean_propagate.
      repeat auto_specialize.
      light_clean_propagate.
      pose proof load_destination.
      pose proof (land_mod2_true _ _ Heqb0).
      repeat auto_specialize.
      rewrite N.land_comm in Heqb0.
      eapply land_mod2_true in Heqb0.
      eapply lnot_mod2' in Heqb0.
      repeat auto_specialize.
      lia.
    }
    {
      (* mmio load case *)
      simpl in *.
      assert ((? "ismemory"%string (split1 (split2 (split2 (split2 head)))) mod 2 =? 1) &&
           (? "store"%string (split1 (split2 (split2 (split2 head)))) mod 2 =? 0) = false)%bool.
      {
        assert (N.land (? "ismemory"%string (split1 (split2 (split2 (split2 head)))))
          (N.lnot (? "store"%string (split1 (split2 (split2 (split2 head))))) 1) mod 2 = 0) by blast_arith.
        pose proof (land_mod2_false _ _ H).
        destruct H0.
        rewrite H0.
        simpl; eauto.
        eapply lnot_mod2 in H0.
        rewrite H0.
        rewrite Bool.andb_comm.
        simpl; eauto.
      }
      rewrite H in HA8.
      clear HA11.
      auto_specialize.
      light_clean_propagate.
      rewrite Heqb in HA14; simpl in HA14.
      inversion HA14.
      inversion HA16.
      subst.

      merge_simpl.
      simpl in *. 
      inversion HA10.
      subst.
      light_clean_propagate.
      auto_specialize.
      light_clean_propagate.
      auto_specialize.
      eexists.
   
      repeat auto_specialize; light_clean_propagate.
   
      (* This is a load, so we need to simulate with a NDL *)
      split.
      (* It is an mmio instruction, we finish running it completely *)
      eapply existSR_step with (r:= 3%nat).
      (* Invariant on decoded and stuff *)
      simpl.
      rm_existentials.
      split; eauto.
      split; eauto.
      split; eauto.
      reconstruct.
      simpl; eauto.
      split; eauto.
      split; eauto.
      simpl; eauto.
      blast_arith.
      simpl; eauto.
      split; eauto.
      simpl; eauto.
      split; eauto.
      split; eauto.

      unshelve instantiate (1:= _).
      let y := (eexists_st_array 14%nat) in
      exact y.
      apply_log_fn 14%nat.
      eapply existSR_done.

      assert_related simul_implies_indistinguishable.
      Ltac t nxt_st x := 
      rm_existentials;
      [split; eauto| ..];
      [wrapped_arrays_equal 10%nat|..];
      [split; eauto|..];
      [wrapped_arrays_equal 10%nat| ..];
      [prove_outside nxt_st; destruct x; eauto |..].

      t nxt_st x.

      merge_simpl.
      (* clear HA13. *)
      pose proof (land_mod2_true _ _ Heqb2).
      repeat match goal with 
      | [ H : Forall _ [] |- _] => clear H 
      | [ H : Forall2 _ [] [] |- _] => clear H 
      end.

      split; eauto.
      intros.
      destruct (N.eq_dec _ _); eauto.
      eapply HA4.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      simpl; eauto.
      split; eauto.
      simpl; split; eauto.

      {
      eapply imply_forall2.
      eauto.
      intros.
      simpl in *. 
      let Hyp := fresh Hyp in 
      match goal with 
      | [H : In _ (map _ _) |- _] => 
      rename H into Hyp
      end.
      eapply in_split in Hyp.
      light_clean_propagate.
      eapply map_eq_app in Hyp.
      light_clean_propagate.
      repeat (match goal with 
      | [ H : map _ _ = _ :: _ |- _] => 
      eapply map_eq_cons in H
      | [ H : context[map _ ( _ ++ _)] |- _] => 
      rewrite map_app in H
      | [ H : Forall2  _ ( _ ++ _) _ |- _] => 
      eapply Forall2_app_inv_l in H
     | [ H : Forall2  _ ( _ :: _) _ |- _] => 
      inversion H; subst; clear H
      end; light_clean_propagate).
      simpl in *.
      specialize (HB0 [] 
                  (? "decode"%string (split2 y))
                  (map (fun x : N => split2 (split2 (split2 x))) l1') 
                  (split2 (split2 (split2 a)))
                  (map (fun x : N => split2 (split2 (split2 x))) tl) 
                  eq_refl).

      repeat auto_specialize.
      light_clean_propagate.
      repeat clean_arith.
      destruct (N.eq_dec _ _);
      destruct (N.eq_dec _ _);
      destruct (N.eq_dec _ _).
      all:  try match goal with 
            | [ H : ?a = ?b, H' : ?a <> ?b |- _ ] =>
              specialize (H' H); contradiction H' 
            end.
      split; egg_repeat.
      split; egg_repeat.
      split; egg_repeat.
      split; egg_repeat.
      intros.
      repeat auto_specialize.
          try match goal with 
            | [ H : ?a = ?b, H' : ?a <> ?b |- _ ] =>
              specialize (H' H); contradiction H' 
            end.
      split; eauto.
    }
    split; eauto.
    split.
    simpl;intro HH; inversion HH. 
    split; eauto.
    split; eauto.
    {
      light_clean_propagate.
    
      split; eauto.
      2: econstructor.
      pose proof chain_head_only_one.
      specialize (H2) with (1:= HB5).
      merge_simpl.
      cbn in H2.
      specialize (H2 (Forall_nil _) eq_refl).
      eauto.
    }
    intros.
    eapply HB0; eauto.
    rewrite <- H2.
    rewrite <- app_comm_cons.
    eauto.
    }
    {
      rewrite Heqb in *.
      simpl in *.
      inversion HA10.
      subst.
      light_clean_propagate.
      pose proof (land_mod2_true _ _ Heqb2).
      rewrite N.land_comm in Heqb2.
      pose proof (land_mod2_true _ _ Heqb2).
      eapply lnot_mod2' in H0.
      pose proof (mmioload_destination).
      repeat auto_specialize.
      lia.
    }
    {
      (* It is not an MMIO Load, it is not a Load It has a destination but it
      has to be a store or MMIO store, absurd *) 
      exfalso.
      rewrite Heqb in *.
      simpl in *.
      merge_simpl.
      assert ( N.land (? "ismemory"%string (split1 (split2 (split2 (split2 head)))))
          (N.lnot (? "store"%string (split1 (split2 (split2 (split2 head))))) 1) mod 2 = 0) by
           blast_arith.
      assert (N.land (? "ismmio"%string (split1 (split2 (split2 (split2 head)))))
          (N.lnot (? "mmiostore"%string (split1 (split2 (split2 (split2 head))))) 1)
        mod 2  = 0) by blast_arith.
      inversion HA10.
      light_clean_propagate.
      repeat auto_specialize.
      light_clean_propagate.
      inversion HA22; subst.
      merge_simpl.
      destruct HB5.
      {
        eapply land_mod2_false in H.
        eapply land_mod2_false in H0.
        rewrite H1 in H0.
        destruct H0. inversion H0.
        eapply lnot_mod2 in H0.
        pose proof mmiostore_destination.
        auto_specialize.
        auto_specialize.
        lia.
      }
      {
        eapply land_mod2_false in H.
        eapply land_mod2_false in H0.
        light_clean_propagate.
        pose proof store_destination.
        auto_specialize.
        auto_specialize.
        lia.
      }
    }
    {
       (* mmiostore/store case *)
      rewrite Heqb in *.
      simpl in *.
      assert (N.land (? "ismemory"%string (split1 (split2 (split2 (split2 head)))))
          (N.lnot (? "store"%string (split1 (split2 (split2 (split2 head))))) 1) mod 2 = 0) by blast_arith.
      eapply land_mod2_false in H.
      repeat auto_specialize.
      light_clean_propagate.
      (* Look like mmio store or memory store *)
      assert ((? "ismemory"%string (split1 (split2 (split2 (split2 head)))) mod 2 =? 1) &&
           (? "store"%string (split1 (split2 (split2 (split2 head)))) mod 2 =? 0) = false)%bool.
      {
        destruct H.
        rewrite H.
        simpl; eauto.
        eapply lnot_mod2 in H.
        rewrite H.
        rewrite Bool.andb_comm; simpl; eauto.
      }
      rewrite H0 in HA8.
      inversion HA14.
      light_clean_propagate.
      merge_simpl.
      subst.
      inversion HA10.
      light_clean_propagate.
      eexists.
      repeat auto_specialize; light_clean_propagate.
      split.
      eapply existSR_step with (r:= 3%nat).
      (* Invariant on decoded and stuff *)
      simpl.
      rm_existentials.
      split; eauto.
      split; eauto.
      split; eauto.
      reconstruct.
      simpl; eauto.
      split; eauto.
      split; eauto.
      simpl in *.
      eauto.
      simpl; eauto.
      blast_arith.
      simpl; eauto.
      blast_arith.
      simpl; eauto.
      blast_arith.
      split; eauto.

      unshelve instantiate (1:= _).
      let y := (eexists_st_array 14%nat) in
      exact y.
      apply_log_fn 14%nat.
      eapply existSR_done.

      assert_related simul_implies_indistinguishable.
      t nxt_st x.

      merge_simpl.
      repeat auto_specialize.
      simpl in *.
      light_clean_propagate.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      {
        eapply imply_forall2.
        eauto.
        intros.
        destruct x.
        {
          light_clean_propagate.
          eapply in_map_iff in H1.
          light_clean_propagate.
          inversion HA12.
          repeat split;eauto.
          intros.
          rewrite H7 in H1.
          auto_specialize.
          rewrite H7.
          eauto.
        }
        {
          eapply in_map_iff in H1.
          light_clean_propagate.
          inversion HA16.
        }
      }
      split; eauto.
      split; eauto.
      split; eauto.
      inversion H1.
      inversion H1.
      split; eauto.
      split; eauto.
      {
      light_clean_propagate.
      split; eauto.
      2: econstructor.
      pose proof chain_head_only_one.
      specialize (H1) with (1:= HB2).
      merge_simpl.
      cbn in H1.
      specialize (H1 (Forall_nil _) eq_refl).
      eauto.
      }
      intros.
      eapply HB0; eauto.
      rewrite <- H1.
      (* rewrite <- app_assoc. *)
      instantiate (3:=? "decode"%string (split2 y) :: l).
      rewrite <- app_comm_cons at 1.
      eauto.
    }
    {
      (* That's a regular instruction, not a load neither mmio nor store *)
      assert (n mod 2 = 0) by blast_arith.
      repeat auto_specialize.
      light_clean_propagate.
      inversion HB3.
      subst. repeat auto_specialize.
      rewrite Heqb in *.
      simpl in *.
      light_clean_propagate.
      auto_specialize.
      light_clean_propagate.
      inversion HA10.
      light_clean_propagate.
      repeat auto_specialize.
      light_clean_propagate.
      assert (? "ismemory"%string (split1 (split2 (split2 (split2 head)))) mod 2 = 0 
         \/
        (? "ismemory"%string (split1 (split2 (split2 (split2 head)))) mod 2 = 1 
       )) by blast_arith.
      destruct H0.
      2:{
        assert (N.land (? "ismemory"%string (split1 (split2 (split2 (split2 head)))))
          (N.lnot (? "store"%string (split1 (split2 (split2 (split2 head)))))
             1) mod 2 = 0) by blast_arith.
        eapply land_mod2_false in H1.
        destruct H1; try lia; eauto.
        eapply lnot_mod2 in H1.
        repeat auto_specialize.
        lia.
      }
      merge_simpl.
      assert (n mod 2 = 0) by blast_arith.
      inversion HA10.
      subst.
      light_clean_propagate.
      auto_specialize.
      light_clean_propagate.
      repeat auto_specialize.
      rewrite H0 in HA8.
      simpl in *.
      eexists.
      split.
      eapply existSR_step with (r:= 1%nat).
      2:eapply existSR_step with (r:= 2%nat).
      3:eapply existSR_step with (r:= 3%nat).
      simpl.
      rm_existentials.
      split; eauto.
      split; eauto.
      split; eauto.
      reconstruct.
      all: simpl; eauto.
      eapply DIft.
      reconstruct.
      simpl; eauto.
      repeat clean_arith.
      arithmetic_hammer.
      reconstruct.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      unshelve instantiate (1:= _).
      let y := (eexists_st_array 14%nat) in
      exact y.
      apply_log_fn 14%nat.
      simpl.
      rm_existentials.
      split; eauto.
      split; eauto.
      split; eauto.
      reconstruct.
      all: simpl; eauto.
      eapply DIff.
      reconstruct.
      simpl; eauto.
      egg_repeat.
      eapply DIff.
      reconstruct.
      simpl; eauto.
      light_clean_propagate.
      egg_repeat.
      reconstruct.
      split; eauto.
      unshelve instantiate (1:= _).
      let y := (eexists_st_array 14%nat) in
      exact y.
      apply_log_fn 14%nat.
      rm_existentials.
      split; eauto.
      split; eauto.
      split; eauto.
      reconstruct.
      all: simpl; eauto.
      split; eauto.
      eapply DIff.
      reconstruct.
      simpl; eauto.
      egg_repeat; simpl.
      blast_arith.
      eapply DIff.
      reconstruct.
      simpl; eauto.
      egg_repeat; simpl.
      eapply land_mod2_false_rev.
      light_clean_propagate; eauto.
      reconstruct.
      eapply DIft.
      reconstruct.
      simpl; egg_repeat.
      reconstruct.
      all: try solve [simpl;  split; eauto].

      unshelve instantiate (1:= _).
      let y := (eexists_st_array 14%nat) in
      exact y.
      apply_log_fn 14%nat.

      eapply existSR_done.

      assert_related simul_implies_indistinguishable.
      t nxt_st x.
      merge_simpl.
      repeat match goal with 
      | [ H : Forall _ [] |- _] => clear H 
      | [ H : Forall2 _ [] [] |- _] => clear H 
      end.
      split; eauto.
      intros.
      destruct (N.eq_dec _ _); eauto.
      destruct (N.eq_dec _ _); eauto.
      intros. egg_repeat.
      intros. egg_repeat.
      exfalso.
     
      rewrite HA15 in n0.
      lia.

      destruct (N.eq_dec _ _); eauto.
      2: eapply HA4.
      rewrite HA15 in e.
      lia.
 
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      simpl; eauto.
      split; eauto.
      simpl; split; eauto.

      {
      eapply imply_forall2.
      eauto.
      intros.
      simpl in *. 
      let Hyp := fresh Hyp in 
      match goal with 
      | [H : In _ (_ ++ _) |- _] => 
      rename H into Hyp
      end.
      eapply in_split in Hyp.
      light_clean_propagate.
      eapply app_eq_app in Hyp.
      light_clean_propagate.
      destruct Hyp.
      {
        light_clean_propagate.
        repeat (match goal with 
          | [ H : map _ _ = _ :: _ |- _] => 
          eapply map_eq_cons in H
        | [ H : map _ _ = _ ++ _ |- _] => 
          eapply map_eq_app in H
          | [ H : context[map _ ( _ ++ _)] |- _] => 
          rewrite map_app in H
        | [ H : Forall2  _ ( _ :: _) _ |- _] => 
          inversion H; subst; clear H
          end; light_clean_propagate).
          repeat auto_specialize.
          light_clean_propagate.
          destruct x; simpl in *.
          {
            light_clean_propagate.
            repeat auto_specialize.
            light_clean_propagate.
            destruct l2'; simpl in HB4; inversion HB4.
            destruct d2e; simpl in HB4; inversion HB4.
            subst.
            simpl in HB0.
            rewrite app_nil_r in HB0.
            specialize (HB0 [] 
                  (split1 (split2 (split2 (split2 head))))
                  ( map (fun x : N => split1 (split2 (split2 (split2 x)))) l1')
                  (split2 ((split2 (split2 n0))))
                  (map (fun x : N => split2 (split2 (split2 x))) d2e) 
                  ).
            simpl in HB0.
            specialize (HB0 eq_refl).
            light_clean_propagate.
            repeat clean_arith.
            repeat auto_specialize.
            light_clean_propagate.
            rewrite H10, HA15 in *.
            (* inversion HB4.
            rewrite H10 in *.
            split; eauto.
            split; eauto.
            rewrite H9, H14 in *. *)
            destruct (N.eq_dec _ _); 
            destruct (N.eq_dec _ _);
            destruct (N.eq_dec _ _);
               try match goal with 
            | [ H : ?a = ?b, H' : ?a <> ?b |- _ ] =>
              specialize (H' H); contradiction H' 
            end.
            split;eauto.
            split;eauto.
            2:{ split;eauto.  }
            split;eauto.
            split;eauto.
            intros.
            repeat auto_specialize;try match goal with 
            | [ H : ?a = ?b, H' : ?a <> ?b |- _ ] =>
              specialize (H' H); contradiction H' 
            end. 
          }
          {
            light_clean_propagate.
            repeat auto_specialize.
            light_clean_propagate.
            destruct l2'; simpl in HB4; inversion HB4.
            destruct d2e; simpl in HB4; inversion HB4.
            subst.
            merge_simpl.
            simpl in HB0.
            specialize (HB0 [] 
                  (split1 (split2 (split2 (split2 head))))
                  ( map (fun x : N => split1 (split2 (split2 (split2 x)))) l1')
                  (split1 (split2 (split2 (split2 n0))))
                  (map (fun x : N => split1 (split2 (split2 (split2 x)))) l2' ++ map (fun x : N => split2 (split2 (split2 x))) d2e) 
                  ).
            simpl in HB0.
            rewrite <- app_assoc in HB0.
            rewrite <- app_comm_cons in HB0 .
            specialize (HB0 eq_refl).
            light_clean_propagate.
            repeat clean_arith.
            repeat auto_specialize.
            light_clean_propagate.
            rewrite HA15 in *.
            destruct (N.eq_dec _ _); 
            destruct (N.eq_dec _ _);
            destruct (N.eq_dec _ _). 
            (* 1-5: lia. *)
            1-7: try match goal with 
            | [ H : ?a = ?b, H' : ?a <> ?b |- _ ] =>
              specialize (H' H); contradiction H' 
            end.
            split;eauto.
            2:{ split;eauto.  }
            intros.
            repeat auto_specialize;try match goal with 
            | [ H : ?a = ?b, H' : ?a <> ?b |- _ ] =>
              specialize (H' H); contradiction H' 
            end. 
          }
      }{
        light_clean_propagate.
        repeat (match goal with 
        | [ H : map _ _ = _ :: _ |- _] => 
        eapply map_eq_cons in H
      | [ H : map _ _ = _ ++ _ |- _] => 
        eapply map_eq_app in H
        | [ H : context[map _ ( _ ++ _)] |- _] => 
        rewrite map_app in H
      | [ H : Forall2  _ ( _ :: _) _ |- _] => 
        inversion H; subst; clear H
        end; light_clean_propagate).
        repeat auto_specialize.
        light_clean_propagate.
        simpl in *.
        specialize (HB0 [] 
                  (split1 (split2 (split2 (split2 head))))
                  (map (fun x : N => split1 (split2 (split2 (split2 x)))) l ++
         map (fun x : N => split2 (split2 (split2 x))) l1')
                  (split2 (split2 (split2 a)))
                  (map (fun x : N => split2 (split2 (split2 x))) tl) 
                  ).
        rewrite app_assoc in HB0.
        simpl in HB0.
        specialize (HB0 eq_refl).
        light_clean_propagate.
        repeat clean_arith.
        repeat auto_specialize.
        light_clean_propagate.
        rewrite HA15 in *.
        destruct (N.eq_dec _ _); 
        destruct (N.eq_dec _ _);
        destruct (N.eq_dec _ _).
        1-7: try match goal with 
            | [ H : ?a = ?b, H' : ?a <> ?b |- _ ] =>
              specialize (H' H); contradiction H' 
            end.
        split;eauto.
        2:{ split;eauto.  }
        intros.
        repeat auto_specialize;try match goal with 
        | [ H : ?a = ?b, H' : ?a <> ?b |- _ ] =>
          specialize (H' H); contradiction H' 
        end. 
        split; eauto.
        split; eauto.
        split; eauto.
        intros.
        repeat auto_specialize;try match goal with 
        | [ H : ?a = ?b, H' : ?a <> ?b |- _ ] =>
          specialize (H' H); contradiction H' 
        end. 
      }
    }
    split; eauto.
    intros; repeat auto_specialize; light_clean_propagate; eauto.
    simpl in *.
    inversion HA8.
    symmetry in H2.
    eapply app_eq_nil in H2.
    light_clean_propagate.
    inversion HA5; subst.
    split; eauto.
    split; eauto 6.
    simpl;intro HH; lia.
    split; eauto.
    split; eauto.
    {
      light_clean_propagate.
      match goal with 
      | |- context[filter ?f ?l] =>
        destruct (filter f l) eqn:?
      end.
      split; eauto.
      2:eapply chain_head; eauto.
      rewrite HA15.
      rewrite <- HA18.
      assert (Forall (fun x => split1 x mod 2 = 0 ) l) .
      {
        pose proof @filter_nil_forall.
        specialize (H1 _ _ _ Heql0).
        eapply Forall_forall; intros.
        eapply Forall_forall in H2; eauto.
        clean_arith.
        blast_arith.
      }
      light_clean_propagate.
      eapply chain_head_only_one.
      eauto.
      eauto.
      eauto.

      split; eauto.
      2:eapply chain_head; eauto.
      rewrite HA15.
      rewrite <- HA18.
      assert (exists  pl sl, l = pl ++  [n0] ++ sl /\ Forall (fun x => split1 x mod 2 = 0 ) pl /\ split1 n0 mod 2 = 1).
      {
        pose proof @filter_split.
        specialize (H1 _ _ _ _ _ Heql0).
        light_clean_propagate.
        clean_arith.
        eexists. eexists.
        simpl.
        split; eauto.
        split; eauto.
        eapply Forall_forall.
        intros.
        eapply Forall_forall in HA20; eauto.
        clean_arith.
        blast_arith.
      }
      light_clean_propagate.
      rewrite map_app in H5.
      rewrite <- app_assoc in H5.
      eapply Forall2_app_inv_l in H5.
      light_clean_propagate.
      inversion HA21.
      light_clean_propagate.
      subst.
      light_clean_propagate.
      repeat auto_specialize.
      light_clean_propagate.
      eapply chain_head_only_two; eauto.
    }
    intros.
    eapply HB0; eauto.
    rewrite <- H1.
    rewrite <- app_comm_cons.
    eauto.
    }
(*     
    {
      rewrite Heqb in *.
      simpl in *.
      inversion HA10.
      subst.
      light_clean_propagate.
      pose proof (land_mod2_true _ _ Heqb3).
      rewrite N.land_comm in Heqb3.
      pose proof (land_mod2_true _ _ Heqb3).
      eapply lnot_mod2' in H0.
      pose proof (mmioload_destination).
      repeat auto_specialize.
      lia.
    } *)
    
    {
      (* That's a regular instruction, with no destination *)
      assert (n mod 2 = 0) by blast_arith.
      repeat auto_specialize.
      light_clean_propagate.
      inversion HA10.
      inversion HB2.
      subst. 
      light_clean_propagate.
      repeat auto_specialize.
      light_clean_propagate.
      repeat auto_specialize.
      rewrite Heqb in *.
      simpl in *.
      light_clean_propagate.
      assert (? "ismemory"%string (split1 (split2 (split2 (split2 head)))) mod 2 = 1 \/
              ? "ismemory"%string (split1 (split2 (split2 (split2 head)))) mod 2 = 0) by blast_arith.
      destruct H0.
      {
        repeat auto_specialize.
        assert (N.land (? "ismemory"%string (split1 (split2 (split2 (split2 head)))))
          (N.lnot (? "store"%string (split1 (split2 (split2 (split2 head))))) 1) mod 2 = 0 ) by blast_arith.
        eapply land_mod2_false in H1.
        rewrite H0 in H1.
        destruct H1. inversion H1.
        eapply lnot_mod2 in H1.
        lia.
      }
      merge_simpl.
      subst.
      light_clean_propagate.
      auto_specialize.
      light_clean_propagate.
      rewrite H0 in HA8.
      simpl in *.
      eexists.
   
   
      (* This is a load, so we need to simulate with a NDL *)
      split.
      eapply existSR_step with (r:= 1%nat).
      2:eapply existSR_step with (r:= 2%nat).
      3:eapply existSR_step with (r:= 3%nat).
      simpl.
      rm_existentials.
      split; eauto.
      split; eauto.
      split; eauto.
      reconstruct.
      all: simpl; eauto.
      eapply DIft.
      reconstruct.
      simpl; eauto.
      repeat clean_arith.
      arithmetic_hammer.

      reconstruct.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      unshelve instantiate (1:= _).
      let y := (eexists_st_array 14%nat) in
      exact y.
      apply_log_fn 14%nat. 
      rm_existentials.
      split; eauto.
      split; eauto.
      split; eauto.
      reconstruct.
      all: simpl; eauto.
      eapply DIff.
      reconstruct.
      simpl; eauto.
      congruence.
      eapply DIff.
      reconstruct.
      simpl; eauto.
      congruence.
      reconstruct.
      split; eauto.

      unshelve instantiate (1:= _).
      let y := (eexists_st_array 14%nat) in
      exact y.
      apply_log_fn 14%nat.

      rm_existentials.
      split; eauto.
      split; eauto.
      split; eauto.
      reconstruct.
      all: simpl; eauto.
      split; eauto.
      eapply DIff.
      reconstruct.
      eapply land_mod2_false_rev.
      simpl; eauto.
      congruence.
      (* rewrite HA15. *)
      (* blast_arith. *)
      eapply DIff.
      reconstruct.
      simpl; eauto.
      (* rewrite HA15. *)
      eapply land_mod2_false_rev.
      congruence.
      eauto.
      reconstruct.
      eapply DIff.
      reconstruct.
      simpl; egg_repeat.
      reconstruct.
      all: try solve [simpl;  split; eauto].
      rewrite HA15.
      blast_arith.
      reconstruct.
      all: try solve [simpl;  split; eauto].

      unshelve instantiate (1:= _).
      let y := (eexists_st_array 14%nat) in
      exact y.
      apply_log_fn 14%nat.

      eapply existSR_done.

      assert_related simul_implies_indistinguishable.
      t nxt_st x.
      merge_simpl.
      repeat match goal with 
      | [ H : Forall _ [] |- _] => clear H 
      | [ H : Forall2 _ [] [] |- _] => clear H 
      end.


      split; eauto.
      intros.

 
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.  
      split; eauto. 
      split; eauto.
      intros.
      repeat auto_specialize.
      light_clean_propagate.
      repeat auto_specialize.
      inversion HA8.
      symmetry in H2.
      eapply app_eq_nil in H2.
      light_clean_propagate.
      inversion HA5.
      light_clean_propagate.
      split; eauto.
      split; eauto.
      intros; eauto.
      lia.
      split; eauto.
      split; eauto.
      {
      light_clean_propagate.
      match goal with 
      | |- context[filter ?f ?l] =>
        destruct (filter f l) eqn:?
      end.
      split; eauto.
      2:eapply chain_head; eauto.

      rewrite HA15.

      assert (Forall (fun x => split1 x mod 2 = 0 ) l) .
      {
        pose proof @filter_nil_forall.
        specialize (H1 _ _ _ Heql0).
        eapply Forall_forall; intros.
        eapply Forall_forall in H2; eauto.
        clean_arith.
        blast_arith.
      }
      light_clean_propagate.
      rewrite <- HA17.
      eapply chain_head_only_one; eauto.

      split; eauto.
      2:eapply chain_head; eauto.
      rewrite HA15.
      rewrite <- HA17.
      assert (exists  pl sl, l = pl ++  [n0] ++ sl /\ Forall (fun x => split1 x mod 2 = 0 ) pl /\ split1 n0 mod 2 = 1).
      {
        pose proof @filter_split.
        specialize (H1 _ _ _ _ _ Heql0).
        light_clean_propagate.
        clean_arith.
        eexists. eexists.
        simpl.
        split; eauto.
        split; eauto.
        eapply Forall_forall.
        intros.
        eapply Forall_forall in HA20; eauto.
        clean_arith.
        blast_arith.
      }
      light_clean_propagate.
      rewrite map_app in H4.
      eapply Forall2_app_inv_l in H4.
      light_clean_propagate.
      eapply Forall2_app_inv_l in HA14.
      light_clean_propagate.
      inversion HA14.
      subst.
      light_clean_propagate.
      repeat auto_specialize.
      light_clean_propagate.
      eapply chain_head_only_two; eauto.
      }
      intros.
      eapply HB0; eauto.
      rewrite <- H1.
      instantiate (3:= split1 (split2 (split2 (split2 head))) :: l0).
      rewrite <- app_comm_cons.
      eauto.
    }
    {
      (* Poisoned inst *)
      assert (split1 head mod 2 = 0) by blast_arith.
      repeat auto_specialize.
      light_clean_propagate.
      inversion HA10.
      light_clean_propagate.
      repeat auto_specialize.
      light_clean_propagate.
      repeat auto_specialize.
      rewrite H in *.
      simpl in *.
      light_clean_propagate.
      merge_simpl. 
      subst.
      light_clean_propagate.
      eexists. 
   
      (* This is poison taht we need to drop in the spec as well *)
      split.
      eapply existSR_step with (r:= 1%nat).
      simpl.
      rm_existentials.
      autosplit.
      reconstruct.
      all: simpl; eauto.
      eapply DIff.
      reconstruct.
      simpl; eauto.
      repeat clean_arith.
      {
      light_clean_propagate.
      match type of HA14 with 
      | context[filter ?f ?l] =>
        destruct (filter f l) eqn:?
      end;
      light_clean_propagate.

      rewrite N.eqb_neq.
      rewrite HA18.
      eapply chain_head_poisoned .
      eauto.
      eauto.
      assert (Forall (fun x => split1 x mod 2 = 0 ) l).
      {
        pose proof @filter_nil_forall.
        specialize (H0 _ _ _ Heql0).
        eapply Forall_forall; intros.
        eapply Forall_forall in H1; eauto.
        clean_arith.
        blast_arith.
      }
      eauto.

      rewrite N.eqb_neq.
      rewrite HA18.
      assert (exists  pl sl, l = pl ++  [n] ++ sl /\ Forall (fun x => split1 x mod 2 = 0 ) pl /\ split1 n mod 2 = 1).
      {
        pose proof @filter_split.
        specialize (H0 _ _ _ _ _ Heql0).
        light_clean_propagate.
        clean_arith.
        eexists. eexists.
        simpl.
        autosplit.
        eapply Forall_forall.
        intros.
        eapply Forall_forall in HA14; eauto.
        clean_arith.
        blast_arith.
      }
      light_clean_propagate.
      eapply chain_head_poisoned_two; eauto.
      }
      reconstruct.
      split; eauto.
      unshelve instantiate (1:= _).
      let y := (eexists_st_array 14%nat) in
      exact y.
      apply_log_fn 14%nat.
      eapply existSR_done.
      assert_related simul_implies_indistinguishable.
      unfold RfScored.withdraw_write in *.
      light_clean_propagate.
      t nxt_st x.
      merge_simpl.
      autosplit.
      {
      intros.
      subst.
      destruct (N.eq_dec _ _).
      2: eapply HA4.
      specialize (HA4 idx).
      rewrite <- e in *.
      rewrite HA19 in HA4.
      rewrite <- HA4.
      reflexivity.
      }
      {
        eapply imply_forall2.
        eauto.
        intros.
        simpl in *.
        eapply in_app_iff in H0.
        destruct x; eauto.
        {
        light_clean_propagate.
        autosplit.
        intros.
        auto_specialize.
        destruct H0.
        {
          eapply in_map_iff in H0.
          light_clean_propagate.
          inversion HA13.
        }
        {
          eapply in_map_iff in H0.
          light_clean_propagate.
          inversion HA13.
          eapply in_split in HB1.
          light_clean_propagate.
          rewrite map_app in HB0.
          simpl in HB0.
          specialize (HB0 [] (split1 (split2 (split2 (split2 head))))
                      (map (fun x : N => split1 (split2 (split2 (split2 x)))) l ++
                      map (fun x : N => split2 (split2 (split2 x))) l1)
                      (split2 (split2 (split2 x)))
                        (map (fun x : N => split2 (split2 (split2 x))) l2)).
          simpl in HB0.
          rewrite app_assoc in HB0.
          specialize (HB0 eq_refl).
          repeat auto_specialize; light_clean_propagate.
          destruct (N.eq_dec _ _).
          rewrite <- H7 in *.
          auto_specialize.
          repeat clean_arith.
          lia.
          congruence.
        }
        }
        {
        light_clean_propagate.
        autosplit.
        intros.
        auto_specialize.
        destruct H0.
        {
          eapply in_map_iff in H0.
          light_clean_propagate.
          inversion HA17.
          eapply in_split in HB1.
          light_clean_propagate.
          rewrite map_app in HB0.
          simpl in HB0.
          specialize (HB0 [] (split1 (split2 (split2 (split2 head))))
                      ( map (fun x : N => split1 (split2 (split2 (split2 x)))) l1)
                      (split1 (split2 (split2 (split2 x))))
                        (map (fun x : N => split1 (split2 (split2 (split2 x)))) l2 ++ 
                        map (fun x : N => split2 (split2 (split2 x))) d2e
                        )).
          simpl in HB0.
          rewrite <- app_assoc in HB0.
          rewrite <- app_comm_cons in HB0.
          specialize (HB0 eq_refl).
          repeat auto_specialize; light_clean_propagate.
          destruct (N.eq_dec _ _).
          inversion HA22.
          subst.
          (* rewrite <- H7 in *. *)
          auto_specialize.
          repeat clean_arith.
          lia.
          congruence.
        }
        {
          eapply in_map_iff in H0.
          light_clean_propagate.
          inversion HA22.
        }
        }
      }
      intros.
      subst.
      inversion HA8.
      symmetry in H1.
      eapply app_eq_nil in H1.
      light_clean_propagate.
      inversion HA5.
      light_clean_propagate.
      autosplit.
      intros.
      blast_arith.
      autosplit.
      inversion HB4; eauto.
      {
      light_clean_propagate.
      match goal with 
      | |- context[filter ?f ?l] =>
        destruct (filter f l) eqn:?
      end.
      light_clean_propagate.
      split; eauto.
      eapply chain_head; eauto.
      light_clean_propagate.
      split; eauto.
      eapply chain_head; eauto.
      }
      intros; eauto.
      eapply HB0; eauto.
      rewrite <- H0.
      instantiate (3:= split1 (split2 (split2 (split2 head))) :: l0).
      rewrite <- app_comm_cons.
      eauto.
    }
    {
      (* Poisoned inst *)
      assert (split1 head mod 2 = 0) by blast_arith.
      repeat auto_specialize.
      light_clean_propagate.
      inversion HA10.
      light_clean_propagate.
      repeat auto_specialize.
      light_clean_propagate.
      repeat auto_specialize.
      rewrite H in *.
      simpl in *.
      light_clean_propagate.
      merge_simpl. 
      subst.
      light_clean_propagate.
      eexists. 
   
      (* This is poison taht we need to drop in the spec as well *)
      split.
      eapply existSR_step with (r:= 1%nat).
      simpl.
      rm_existentials.
      autosplit.
      
      reconstruct.
      all: simpl; eauto.
      eapply DIff.
      reconstruct.
      simpl; eauto.
      repeat clean_arith.
      {
        light_clean_propagate.
        match type of HA14 with 
        | context[filter ?f ?l] =>
          destruct (filter f l) eqn:?
        end;
        light_clean_propagate.
        rewrite N.eqb_neq.
        rewrite HA18.
        eapply chain_head_poisoned .
        eauto.
        eauto.
        assert (Forall (fun x => split1 x mod 2 = 0 ) l).
        {
          pose proof @filter_nil_forall.
          specialize (H0 _ _ _ Heql0).
          eapply Forall_forall; intros.
          eapply Forall_forall in H1; eauto.
          clean_arith.
          blast_arith.
        }
        eauto.
        rewrite N.eqb_neq.
        rewrite HA18.
        assert (exists  pl sl, l = pl ++  [n] ++ sl /\ Forall (fun x => split1 x mod 2 = 0 ) pl /\ split1 n mod 2 = 1).
        {
          pose proof @filter_split.
          specialize (H0 _ _ _ _ _ Heql0).
          light_clean_propagate.
          clean_arith.
          eexists. eexists.
          simpl.
          split; eauto.
          split; eauto.
          eapply Forall_forall.
          intros.
          eapply Forall_forall in HA14; eauto.
          clean_arith.
          blast_arith.
        }

        light_clean_propagate.
        eapply chain_head_poisoned_two.
        eauto.
        eauto.
        eauto.
        eauto.
      }
      reconstruct.
      split; eauto.
      unshelve instantiate (1:= _).
      let y := (eexists_st_array 14%nat) in
      exact y.
      apply_log_fn 14%nat.
      eapply existSR_done.
      assert_related simul_implies_indistinguishable.
      unfold RfScored.withdraw_write in *.
      light_clean_propagate.
      t nxt_st x.
      merge_simpl.
      autosplit.
      intros.
      repeat auto_specialize.
      light_clean_propagate.
      repeat auto_specialize.
      subst.
      inversion HA8.
      symmetry in H1.
      eapply app_eq_nil in H1.
      light_clean_propagate.
      inversion HA5.
      light_clean_propagate.
      autosplit.
      intros.
      blast_arith.
      inversion HB3; eauto.
      {
      light_clean_propagate.
      match goal with 
      | |- context[filter ?f ?l] =>
        destruct (filter f l) eqn:?
      end.
      light_clean_propagate.
      split; eauto.
      eapply chain_head; eauto.
      light_clean_propagate.
      split; eauto.
      eapply chain_head; eauto.
      }
      intros; eauto.
      eapply HB0; eauto.
      rewrite <- H0.
      instantiate (3:= split1 (split2 (split2 (split2 head))) :: l0).
      rewrite <- app_comm_cons.
      eauto.
    }
  }
  Unshelve.
  Time Qed.
      
