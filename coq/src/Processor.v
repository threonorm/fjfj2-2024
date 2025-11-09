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
Require LoadBuffer.
Require LoadBufferStoresafe.
Require Nondet.
Require Import egg.Loader.
Require Import Tactics.

Open Scope N.

Definition fetch := 0.
Definition decode := 1.
Definition execute := 2.
Definition writeback := 3.

Module SimpleProcessorSpec.
    Local Instance processor_modules : instances :=
      #| 
        reg.mkReg pc;
        RfSpec.mkRf rf; 

        reg.mkReg state_machine;
        reg.mkReg decode_inst;
        reg.mkReg src_val1;
        reg.mkReg src_val2;
        reg.mkReg dest_val;

  (* Interface with inst memory *)
        FifoSpec.Fifo1Spec.mkFifo1 to_imem;
        FifoSpec.Fifo1Spec.mkFifo1 from_imem;

  (* Interface with data memory *)
        FifoSpec.Fifo1Spec.mkFifo1 to_dmem;
        FifoSpec.Fifo1Spec.mkFifo1 from_dmem;

        FifoSpec.FifoSpec.mkFifoSpec to_mmio;
        FifoSpec.FifoSpec.mkFifoSpec from_mmio
      |#.

    Open Scope N.

    Definition do_fetch :=
      (rule
          (if (= {read state_machine} `{fetch})
              (begin 
                  {write state_machine  `{decode}} 
                  (set pc_req {read pc})
                  {enq to_imem (# (* is_write *) 0 (* addr *) pc_req (* data*) 0)})
              abort)).
    Arguments do_fetch /.

    Definition do_decode :=
      (rule
        (if (= {read state_machine} `{decode})
            (begin 
                (set resp {first from_imem})
                (set (addr_resp data_resp) resp)
                (* We check that this is a reponse we asked for *)
                    {write state_machine  `{execute}}
                    (set decoded (decode data_resp))
                    (set src1 {read1 rf (src1 decoded)})
                    (set src2 {read2 rf (src2 decoded)})
                    {write src_val1 src1}
                    {write src_val2 src2}
                    {write decode_inst decoded}
                    {deq from_imem} 
                 )
            abort)).
    Arguments do_decode /.

    Definition do_execute :=
       (rule
        (if (= {read state_machine} `{execute})
            (begin 
                {write state_machine  `{writeback}}
                (set decoded {read decode_inst})
                (set val1 {read src_val1})
                (set val2 {read src_val2})
                (set output_alu (alu (# decoded val1 val2)))
                (set addr_dest (memaddr (# decoded val1)))
                (if (ismemory decoded)
                    (if (store decoded)
                      {enq to_dmem (# 1 addr_dest val2)}
                      {enq to_dmem (# 0 addr_dest 0)})
                    (if (ismmio decoded)
                      {enq to_mmio (# (mmiostore decoded) val1 val2)}
                      pass))
                {write dest_val output_alu})
            abort)).
    Arguments do_execute /.

    Definition do_writeback :=
       (rule
        (if (= {read state_machine} `{writeback})
            (begin 
                {write state_machine `{fetch}}
                (set decoded {read decode_inst})
                (set producedvalue {read dest_val})
                (if (& (ismemory decoded) (~ 1 (store decoded)))
                  (begin 
                    (set (addr data) {first from_dmem})
                    (set producedvalue data)
                    {deq from_dmem})
                  (if (& (ismmio decoded) (~ 1 (mmiostore decoded)))
                    (begin 
                      (set producedvalue {first from_mmio})
                      {deq from_mmio})
                    pass))
                (if (has_destination decoded)
                    {write rf (# (destination decoded) producedvalue)}
                    pass) 
                {write pc (nextpc (# {read pc} {read src_val1}))})
            abort)).
    Arguments do_writeback /.



  Definition enq_iresp :=
      (action_method (el)
              {enq from_imem el}).
  Arguments enq_iresp /.
  Definition first_ireq := 
      (value_method ()
        {first to_imem}).
  Arguments first_ireq /.

  Definition deq_ireq := 
      (action_method ()
        {deq to_imem}).
  Arguments deq_ireq /.

  Definition enq_dresp :=
      (action_method (el)
                {enq from_dmem el}).
  Arguments enq_dresp /.
  Definition first_dreq := 
      (value_method ()
        {first to_dmem}).
  Arguments first_dreq /.

  Definition deq_dreq := 
      (action_method () {deq to_dmem}).
  Arguments deq_dreq /.
  Definition enq_mmio :=
      (action_method (el)
              {enq from_mmio el}).
  Arguments enq_mmio/.

  Definition mmio_req := 
      (value_method ()
        {first to_mmio}).
  Arguments mmio_req /.
  Definition deq_mmio := 
      (action_method ()
        {deq to_mmio}).
  Arguments deq_mmio /.

  Global Instance interface : module _ := 
    module#(rules [do_fetch; do_decode; do_execute; do_writeback]
            vmet [first_ireq; first_dreq; mmio_req] amet [enq_iresp; deq_ireq; enq_dresp; deq_dreq;  enq_mmio; deq_mmio]).
End SimpleProcessorSpec.

Module ProcessorSpec.
    Local Instance processor_modules : instances :=
      #| 
  (* "Architectural state" *)
        reg.mkReg pc;
        RfSpec.mkRf rf;

  (* microarchitectural state *)
        reg.mkReg state_machine;
        reg.mkReg decode_inst;
        reg.mkReg src_val1;
        reg.mkReg src_val2;
        reg.mkReg dest_val;

        LoadBuffer.mkLB ild_buffer;
        LoadBufferStoresafe.mkLB dld_buffer;
  (* Interface with memory *)
        FifoSpec.FifoSpec.mkFifoSpec to_imem;
  (* This spec has at most on "actual" request to memory *)
        FifoSpec.Fifo1Spec.mkFifo1 from_imem;

        FifoSpec.FifoSpec.mkFifoSpec to_dmem;
  (* This spec has at most on "actual" request to memory *)
        FifoSpec.Fifo1Spec.mkFifo1 from_dmem;

        FifoSpec.FifoSpec.mkFifoSpec to_mmio;
        FifoSpec.FifoSpec.mkFifoSpec from_mmio;
  (* Source of nondeterminism  *)
        Nondet.mkND nondet
      |#.

    Definition emit_indl :=
      (rule
        (begin 
          (set addr {choose nondet})
          {enq to_imem (# 0 addr 0)})).
    Arguments emit_indl /.

    Definition emit_dndl :=
      (rule
        (begin 
          (set addr {choose nondet})
          {loadReq dld_buffer addr}
          {enq to_dmem (# 0 addr 0)})).
    Arguments emit_dndl /.

    Definition do_fetch :=
      (rule
          (if (= {read state_machine}  `{fetch})
              (begin 
                  {write state_machine  `{decode}}
                  (set pc_req {read pc})
                  (set buffer_result {lookup ild_buffer pc_req})
                  (set (valid result) buffer_result)
                  (if (= valid 1)
                      (* Directly responding as addr already requested by the random load machine *)
                      {enq from_imem  (# (*addr*) pc_req
                                         (*data*) result)} 
                      (* Need to have a response from memory ! *)
                      abort))
              abort)).
    Arguments do_fetch /.

    Definition do_decode :=
      (rule
        (if (= {read state_machine} `{decode})
            (begin 
                (set resp {first from_imem})
                (set (addr_resp data_resp) resp)
                (* We check that this is a reponse we asked for *)
                    {write state_machine `{execute}}
                    (set decoded (decode data_resp))
                    (set src1 {read1 rf (src1 decoded)})
                    (set src2 {read2 rf (src2 decoded)})
                    {write src_val1 src1}
                    {write src_val2 src2}
                    {write decode_inst decoded}
                    {deq from_imem}) 
            abort)).
    Arguments do_decode /.

    Definition do_execute :=
      (rule
        (if (= {read state_machine} `{execute})
            (begin 
                {write state_machine `{writeback}}
                (set decoded {read decode_inst})
                (set val1 {read src_val1})
                (set val2 {read src_val2})
                (set output_alu (alu (# decoded val1 val2)))
                (if (ismemory decoded)
                  (begin 
                    (set addr_dest (memaddr (# decoded val1)))
                    (if (store decoded)
                      (begin 
                        {storeReq dld_buffer addr_dest}
                        {enq to_dmem (# 1 addr_dest val2)})
                      (begin 
                        (set buffer_result {lookup dld_buffer addr_dest})
                        (set (valid result) buffer_result)
                        (if (= valid 1)
                            {enq from_dmem (# (*addr*) addr_dest 
                                              (*data*) result )} 
                            abort))))
                  (if (ismmio decoded)
                    {enq to_mmio (# (mmiostore decoded) val1 val2)}
                    pass))
                {write dest_val output_alu})
            abort)).
    Arguments do_execute /.

    Definition do_writeback :=
       (rule
        (if (= {read state_machine} `{writeback})
            (begin 
                {write state_machine `{fetch}}
                (set decoded {read decode_inst})
                (set producedvalue {read dest_val})
                (if (& (ismemory decoded) (~ 1 (store decoded)))
                  (begin 
                    (set (addr data) {first from_dmem})
                    (set producedvalue data)
                    {deq from_dmem})
                  (if (& (ismmio decoded) (~ 1 (mmiostore decoded)))
                    (begin 
                      (set producedvalue {first from_mmio})
                      {deq from_mmio})
                    pass))
                (if (has_destination decoded)
                    {write rf (# (destination decoded) producedvalue)}
                    pass) 
                {write pc (nextpc (# {read pc} {read src_val1}))})
            abort)).
  Arguments do_writeback /.

  Definition enq_iresp :=
      (action_method (el)
              {insert ild_buffer el}).
  Arguments enq_iresp /.

  Definition first_ireq := 
      (value_method ()
        {first to_imem}).
  Arguments first_ireq /.

  Definition deq_ireq := 
      (action_method ()
        {deq to_imem}).
  Arguments deq_ireq /.

  Definition enq_dresp :=
      (action_method (el) 
        {loadResp dld_buffer el}).
  Arguments enq_dresp /.

  Definition first_dreq := 
      (value_method ()
        {first to_dmem}).
  Arguments first_dreq /.

  Definition deq_dreq := 
      (action_method ()
        {deq to_dmem}).
  Arguments deq_dreq /.

  Definition enq_mmio :=
      (action_method (el)
              {enq from_mmio el}).
  Arguments enq_mmio /.

  Definition mmio_req := 
      (value_method ()
        {first to_mmio}).
  Arguments mmio_req /.

  Definition deq_mmio := 
      (action_method () 
        {deq to_mmio}).
  Arguments deq_mmio /.

  Global Instance interface : module _ := 
    module#(rules [emit_indl; emit_dndl; do_fetch; do_decode; do_execute; do_writeback]
            vmet [first_ireq; first_dreq; mmio_req] amet [enq_iresp; deq_ireq; enq_dresp; deq_dreq; enq_mmio; deq_mmio]).
End ProcessorSpec.

Module Frontend.
    Local Instance processor_modules : instances :=
      #| 
        Nondet.mkND nondet
      |#.

    Definition first_req := 
        (value_method ()
          (# (* is_write *) 0 (* addr *) {choose nondet} (* data*) 0)).
    Arguments first_req /.

    Definition deq_req := 
        (action_method () pass).
    Arguments deq_req /.

    Definition update_predictors := 
        (action_method (el) pass).
    Arguments update_predictors /.

    Global Instance interface : module _ := 
      module#(vmet [first_req] amet [deq_req; update_predictors]).
End Frontend.

Module Backend.
    Local Instance processor_modules : instances :=
      #| 
  (* Backend execution *)
        reg.mkReg expected_pc;
        RfSpec.mkRf rf; 
        reg.mkReg state_machine;
        reg.mkReg decode_inst;
        reg.mkReg src_val1;
        reg.mkReg src_val2;
        reg.mkReg dest_val;

        Nondet.mkND nondet;
        LoadBufferStoresafe.mkLB dld_buffer;
        FifoSpec.FifoSpec.mkFifoSpec to_dmem;
        FifoSpec.Fifo1Spec.mkFifo1 from_dmem;
        FifoSpec.FifoSpec.mkFifoSpec to_mmio;
        FifoSpec.FifoSpec.mkFifoSpec from_mmio;
        FifoSpec.FifoSpec.mkFifoSpec instr_stream
      |#.
    
    Definition emit_dndl :=
      (rule
        (begin 
          (set addr {choose nondet})
          {loadReq dld_buffer addr}
          (* Note: technically here I would probably want to put data 0 instead of some specific stuff *)
          {enq to_dmem (# 0 (* is_write *) addr 0 (* data *))})).
    Arguments emit_dndl /.

 

    Definition push_instr :=
      (* This is the method one can call *)
      (action_method (resp_from_imem)
        {enq instr_stream resp_from_imem}).
    Arguments push_instr/.

    Definition do_decode :=
      (* This is the method one can call *)
      (rule
        (if (= {read state_machine} `{decode})
            (begin 
                (set (addr_resp data_resp) {first instr_stream})
                (if (= addr_resp {read expected_pc})
                  (begin 
                    {write state_machine `{execute}}
                    (set decoded (decode data_resp))
                    (set src1 {read1 rf (src1 decoded)})
                    (set src2 {read2 rf (src2 decoded)})
                    {write src_val1 src1}
                    {write src_val2 src2}
                    {write decode_inst decoded})
                    (* If instr is not expected just drop the request! *)
                    {deq instr_stream}
                    ))
            abort)).
    Arguments do_decode/.

    Definition do_execute :=
      (rule
        (if (= {read state_machine} `{execute})
            (begin 
                {write state_machine  `{writeback}}
                (set decoded {read decode_inst})
                (set val1 {read src_val1})
                (set val2 {read src_val2})
                (set output_alu (alu (# decoded val1 val2))) 
                (if (ismemory decoded)
                    (begin 
                      (set addr_dest (memaddr (# decoded val1)))
                      (if (store decoded)
                        (begin 
                          {storeReq dld_buffer addr_dest}
                          {enq to_dmem  (# 1 addr_dest val2 )})
                        (begin 
                          (set buffer_result {lookup dld_buffer addr_dest})
                          (set (valid result) buffer_result)
                          (if (= valid 1)
                              {enq from_dmem (# (*addr*) addr_dest (*data*) result )} 
                              abort))))
                    (if (ismmio decoded)
                      {enq to_mmio (# (mmiostore decoded) val1 val2)}
                      pass))
                {write dest_val output_alu})
            abort)).
    Arguments do_execute /.

    Definition do_writeback :=
       (rule
        (if (= {read state_machine} `{writeback})
            (begin 
                {write state_machine `{decode}}
                {deq instr_stream}
                (set decoded ((decode_inst read)))
                (set producedvalue {read dest_val})
                (if (& (ismemory decoded) (~ 1 (store decoded)))
                  (begin 
                    (set (addr data) {first from_dmem})
                    (set producedvalue data)
                    {deq from_dmem})
                (if (& (ismmio decoded) (~ 1 (mmiostore decoded)))
                  (begin 
                    (set producedvalue {first from_mmio})
                    {deq from_mmio})
                  pass))
                (if (has_destination decoded)
                    {write rf (# (destination decoded) producedvalue)}
                    pass) 
                {write expected_pc (nextpc (# {read expected_pc} {read src_val1}))})
            abort)).
  Arguments do_writeback /.

  Definition enq_dresp :=
      (action_method (el)
        {loadResp dld_buffer el}).
  Arguments enq_dresp /.

  Definition first_dreq := 
      (value_method ()
        {first to_dmem}).
  Arguments first_dreq /.

  Definition deq_dreq := 
      (action_method ()
        {deq to_dmem}).
  Arguments deq_dreq /.

  Definition enq_mmio :=
      (action_method (e)
        {enq from_mmio e}).
  Arguments enq_mmio /.
  Definition mmio_req := 
      (value_method ()
        {first to_mmio}).
  Arguments mmio_req /.
  Definition deq_mmio := 
      (action_method ()
        {deq to_mmio}).
  Arguments deq_mmio /.

  Definition redirect :=
      (action_method ()
        pass
        ).
  Arguments redirect /.

  Definition redirectv :=
      (value_method ()
          {choose nondet}).
  Arguments redirectv /.
   
 Global Instance interface : module _ := 
    module#(rules [emit_dndl; do_decode; do_execute; do_writeback]
            vmet [first_dreq; mmio_req; redirectv] amet [push_instr; enq_dresp; deq_dreq; enq_mmio; deq_mmio; redirect]).
End Backend.

Module ProcessorDecomposedSpec.
    Local Instance processor_modules : instances :=
      #| 
        Frontend.interface frontend;
        Backend.interface backend;
        FifoSpec.FifoSpec.mkFifoSpec to_imem
        (* FifoSpec.FifoSpec.mkFifoSpec from_imem *)
      |#.

  Open Scope N.

  Definition first_ireq := 
      (value_method ()
        {first to_imem}).
  Arguments first_ireq /.

  Definition deq_ireq := 
      (action_method ()
        {deq to_imem}).
  Arguments deq_ireq /.

  (* Definition resp_inst :=
    (action_method (el)
      (begin 
          (set req {first from_imem})
          {deq from_imem}
          {push_instr backend req})).
  Arguments resp_inst/. *)

  Definition enq_iresp :=
      (action_method (el)
        {push_instr backend el}).
  Arguments enq_iresp /.

  Definition push_ireq :=
      (action_method ()
              (begin 
              	  {deq_req frontend}
                  (set req {first_req frontend})
                  {enq to_imem req})).
  Arguments push_ireq /.
 
  Definition enq_dresp :=
      (action_method (el)
        {enq_dresp backend el}).
  Arguments enq_dresp /.
  Definition first_dreq := 
      (value_method ()
        {first_dreq backend}).
  Arguments first_dreq /.
  Definition deq_dreq := 
      (action_method ()
        {deq_dreq backend}).
  Arguments deq_dreq /.

  Definition enq_mmio :=
      (action_method (el)
        {enq_mmio backend el}).
  Arguments enq_mmio /.
  Definition mmio_req := 
      (value_method ()
        {mmio_req backend}).
  Arguments mmio_req /.
  Definition deq_mmio := 
      (action_method ()
        {deq_mmio backend}).
  Arguments deq_mmio /.

  Global Instance interface : module _ := 
    module#(rules [push_ireq]
            vmet [first_ireq; first_dreq; mmio_req] amet [enq_iresp; deq_ireq; enq_dresp; deq_dreq; enq_mmio; deq_mmio]).
End ProcessorDecomposedSpec.

Section Correctness.
    Context {uninterp : Uninterpreted_Functions}.
    Definition related (ist : SModule) (sst : SModule) := 
        exists 
            (pc i_state_machine : N)
            (s_state_machine : N) 
            (ild_buffer :  N -> list N)
            ( dld_buffer : N -> LoadBufferStoresafe.Entry)
            (decode_inst src_val1 src_val2 dest_val : N)
            (fifo_to_imem fifo_to_dmem to_mmio from_mmio: list N)
            (fifo_from_imem: list N)
            (* fifo_from_imem  *)
            (fifo_from_dmem : option N)
            (rf : N -> N), 
          sst = *[| pc; rf; s_state_machine; decode_inst; src_val1; src_val2;
                 dest_val; ild_buffer; dld_buffer; fifo_to_imem; @None N;
                 fifo_to_dmem; fifo_from_dmem;
                 (* @None N; *)
                 to_mmio; from_mmio; tt |]* /\
          ist = *[| [| tt |] ;
                     [| pc; rf; i_state_machine; decode_inst; src_val1; src_val2;
                        dest_val; [| tt |]; dld_buffer; fifo_to_dmem; 
                        fifo_from_dmem; 
                        (* @None N; *)
                        to_mmio; from_mmio; fifo_from_imem|]; fifo_to_imem |]* /\ 
            (* The relation is always matching the states! *)
            (i_state_machine <> decode -> i_state_machine = s_state_machine ) /\
            (i_state_machine = decode -> s_state_machine = fetch ) /\
            (forall addr, 
              let load_to_addr :=  List.flat_map 
                      (fun resp => dlet {el_addr el_data} := resp in 
                                   if el_addr =? addr then [el_data] else []) fifo_from_imem in
              ild_buffer addr =  load_to_addr).
    Arguments related / ist sst.


    Ltac eat_eexists :=
       repeat match goal with 
          | [ |- exists t, _] => eexists 
          end.

    Ltac post_rule_state := 
      eat_eexists; 
      split;[ wrapped_arrays_equal 16%nat| ].

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
    time "Indistiguishable searchvar" egg_eexists 4; egg_repeat.


  Ltac substep k:= 
        simpl; unfold lift_to;
   let y := eexists_st_array k in
	eexists y; split;
  [ apply f_equal; reflexivity | ]; simpl;
  eexists;
  split; [reflexivity | ].
 

  Tactic Notation "abstract_commit" tactic(t) := 
  time "Abstract commit" (abstract t).
    (* admit'. *)
    (* abstract t *)
Tactic Notation "abstract_commit2" tactic(t) := 
  time "Abstract commit" (abstract t).

Ltac prove_indistinguishable' := 
  remove_ascii;
  prove_indistinguishable.
(* Ltac destruct_ex n H ::= 
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
Lemma simul_implies_indistinguishable : 
  forall ist sst, related ist sst -> 
      indistinguishable (spec_of ProcessorDecomposedSpec.interface) (spec_of ProcessorSpec.interface) ist sst.
  intros.  cbn in H.  light_clean_propagate.
  prove_indistinguishable'; (try method_indistinguishable).
  Time Qed.

Notation "m1 ';' m2  ';' m3 ';' '...' " := 
    (fun x:nat => match x with 
      | 0%nat => m1
      | S m => match m with 
            | 0%nat => m2
            | S m =>
            match m with 
            | 0%nat => m3
            | S m => _ end end end) ( at level 51,
             m1 constr at level 0,
             m2 constr at level 0,
             m3 constr at level 0,
               only printing).

Notation "'|[' x ']|'" := {| alength := _; default:= _; values := x |} (at level 20, only printing).

Ltac prove_related_and_indist :=
  assert_related simul_implies_indistinguishable;
   [simpl; post_rule_state; split;
   [ wrapped_arrays_equal 3%nat ; wrapped_arrays_equal 14%nat ; merge_simpl; eauto 6
   | 
   split; simpl;eauto;
   split; simpl;eauto;
   let newH := fresh in intro newH; inversion newH ]  | .. ].

Theorem correct' : refines (spec_of ProcessorDecomposedSpec.interface) (spec_of ProcessorSpec.interface) related.
  prove_refinement.
  {
    (* Time abstract_commit ( *)
      pre_method related_i_s indistinguishable_i_s; eauto;
      assert_related simul_implies_indistinguishable.
      (* idtac;[ *)
      (* Establishing the invariant hold on new st *)
      (* abstract  *)
      (* ( *)
        simpl;
      post_rule_state;
      split;
      [
        wrapped_arrays_equal 3%nat
      |
      split; eauto;
      split; eauto ];
      intros;
      merge_simpl.
      wrapped_arrays_equal 14%nat.
      destruct (addr =? split1 arg_method) eqn:?.
      (* [ *)
        rewrite List.flat_map_app;
        specialize (HB1 (split1 arg_method));
        repeat clean_arith;
        light_clean_propagate;
        rewrite <- HB1;
        simpl;
        rewrite N.eqb_refl;
        rewrite app_nil_r;
        eauto.
      (* |  *)
        rewrite List.flat_map_app;
        simpl;
        rewrite N.eqb_sym in Heqb;
        rewrite Heqb;
        specialize (HB1 addr);
        rewrite HB1;
        rewrite !app_nil_r;
        eauto.
      (* ]) *)
    (* | ..] *)
    (* . *)
   (* ). *)
  }
  {
    (* abstract_commit ( *)
    pre_method related_i_s indistinguishable_i_s; eauto;
    prove_related_and_indist.
    (* ). *)
  }
  {
    (* abstract_commit ( *)
    pre_method related_i_s indistinguishable_i_s. 
    lia.
    prove_related_and_indist.
      (* ). *)
  }
  {
    (* abstract_commit ( *)
    pre_method related_i_s indistinguishable_i_s; try lia.
    prove_related_and_indist.
      (* ). *)
  }
  {
    (* abstract_commit ( *)
    pre_method related_i_s indistinguishable_i_s; try lia;
    prove_related_and_indist.
  }
  {
    (* abstract_commit ( *)
    pre_method related_i_s indistinguishable_i_s; try lia;
    prove_related_and_indist.
      (* ). *)
  }
  {
    (* Time abstract_commit ( *)
    (* ( *)
    simpl in related_i_s; light_clean_propagate; eauto; clear indistinguishable_i_s;
    simpl in * |-; min_straight_line;
    light_clean_propagate;
    repeat simpl_applylog; min_straight_line; simpl in * |- .
    (* We need to do fetch; decode; drop from ild_buffer to simulate that on the spec side *)
    eexists; split.
    (* Emit ndl *)
      eapply existSR_step with (r:= 0%nat); simpl in *.
      step_method_spec; instantiate (1:= 1); try lia.
      eapply existSR_done.
    unfold state_t in *;
    assert_related simul_implies_indistinguishable.
      simpl; post_rule_state; split.
          wrapped_arrays_equal 3%nat.
          wrapped_arrays_equal 1%nat.
          merge_simpl; eauto.
  } 
  {
    (* emit ndnl *)
    (* Time abstract_commit ( *)
    simpl in related_i_s; light_clean_propagate; clear indistinguishable_i_s;
    simpl in * |-; min_straight_line;
      unfold lift_to in *;
    light_clean_propagate;
    simpl in * |-; min_straight_line; repeat simpl_applylog; min_straight_line; simpl in * |- ;
    eexists; split;
    (* Emit ndl *)
    idtac; [ eapply existSR_step with (r:= 1%nat); [ step_method_spec; instantiate (1:= n0); try lia| ..] | ..];
    [ eapply existSR_done|..];
    prove_related_and_indist.
      (* ). *)
  }
   {
    (* Case Push iresp *)
    (* Time abstract_commit ( *)
    unfold lift_to in *;
      simpl in related_i_s; light_clean_propagate; clear indistinguishable_i_s;
    simpl in * |-; min_straight_line; repeat simpl_applylog; min_straight_line.
    (* This leads to decoding so there are two cases *)
    let case1 := fresh "casesplit" in
    destruct ( _ =? _) eqn:case1 in HB2.
    repeat (first [ straight_line_step | straight_line_wpa ]; simpl in * |- ).
    simpl in *|-.
    
        repeat clean_arith; light_clean_propagate.
      (* auto_specialize; *)
      light_clean_propagate;
      eexists.
        split.
          eapply existSR_step with (r:= 2%nat).
        step_method_spec; simpl; merge_simpl; eauto.
        rewrite HA7; eauto.
         autorewrite with fwd_rewrites in *; eauto.
        specialize (HB1 (split1 head)).
        rewrite HB1. 
        rewrite N.eqb_refl; simpl. 
         reflexivity.
         reflexivity.
     
        (* Do decode *)
        eapply existSR_step with (r:= 3%nat); 
        [
        step_method_spec;
        simpl; merge_simpl; eauto 
        | ..].
        eapply existSR_done.
        prove_related_and_indist.
       
          prove_outside nxt_st; eauto.
          prove_outside nxt_st; eauto.
         
        repeat clean_arith; light_clean_propagate;
        min_straight_line.
        simpl in *|-.
        light_clean_propagate.
      eexists;

      split.
      eapply existSR_substep with (instance_i := 7%nat) (r:= 0%nat).
      simpl; eauto.
      simpl; eauto.
      unfold lift_to.
      substep 16%nat.
      eexists; eexists ( split1 head) ; split; eauto .
      (* Need to kill on the ild side *)
      eapply existSR_done.
      prove_related_and_indist.

      all:  intros;  specialize (HB1 H); rewrite HB1;
        destruct (H=? split1 head) eqn:?;
        rewrite N.eqb_sym in  Heqb;
        rewrite Heqb; simpl; eauto.
  }
  {
      time light_clean_propagate. 
  
      clear indistinguishable_i_s;
      unfold lift_to in *;
      simpl in related_i_s; light_clean_propagate.
      simpl in * |-.

      time (eapply wpa_to_cps in HA3;
      repeat (hnf in HA3;light_clean_propagate); simpl in *|-).
      destruct HB2.
      light_clean_propagate.
      destruct HB0.
      light_clean_propagate.

      repeat simpl_applylog.

    time (eexists;
      split; 
      [ eapply existSR_step with (r:= 4%nat); simpl | ..]).
  time (eexists;
   let y := eexists_st_array 16%nat in
	eexists y; do 3 eexists; split; [ eauto |  ]; split; [ eauto |  ]; split).

      time eapply wpa_to_cps.
      time simpl.
    
      time repeat prove_post.
      repeat clean_arith; autorewrite with fwd_rewrites in *. 
      unfold decode in *.
      try lia.

      prove_post.
      eapply existSR_done. 

      prove_related_and_indist.
      light_clean_propagate.

      repeat clean_arith.
      repeat simpl_applylog.
      time (eexists;
       split; 
      [ eapply existSR_step with (r:= 4%nat); simpl | ..]).

    time (eexists;
     let y := eexists_st_array 16%nat in
	  eexists y; do 3 eexists; split; [ eauto |  ]; split; [ eauto |  ]; split).


      eapply wpa_to_cps.
      simpl.
      light_clean_propagate.
      repeat prove_post.
      5: eapply existSR_done.


      unfold decode in *.
      clean_arith;
      autorewrite with fwd_rewrites in *; eauto.
      try lia.
      repeat clean_arith.
      destruct (LoadBufferStoresafe.res _).
      subst; merge_simpl; try lia.
      eauto.
      clean_arith; autorewrite with fwd_rewrites in *; eauto.
      prove_post.
      prove_related_and_indist.
   


      light_clean_propagate.
      destruct HB0;
      light_clean_propagate;
      repeat simpl_applylog;
      repeat clean_arith.

      eexists;
      split; (* Do execute*)
      idtac; [ eapply existSR_step with (r:= 4%nat) ;
      (* hnf; set ProcessorSpec.do_execute as prog; simpl in prog; subst prog; *)
      simpl; repeat clean_arith; subst | ..].


      time (eexists;
      let y := eexists_st_array 16%nat in
	    eexists y; do 3 eexists; split; [ eauto |  ]; split; [ eauto |  ]; split).
      eapply wpa_to_cps.
      time simpl.
      repeat prove_post.

      unfold decode in *.
       repeat clean_arith;
       autorewrite with fwd_rewrites in *; eauto; eauto; cbv; try lia.
       prove_post.
       eapply existSR_done.
       prove_related_and_indist.
     
      eexists;
      split; (* Do execute*)
      idtac; [ eapply existSR_step with (r:= 4%nat) ;
      (* hnf; set ProcessorSpec.do_execute as prog; simpl in prog; subst prog; *)
      simpl; repeat clean_arith; subst | ..].
      time (eexists;
      let y := eexists_st_array 16%nat in
	    eexists y; do 3 eexists; split; [ eauto |  ]; split; [ eauto |  ]; split).
      eapply wpa_to_cps.
      time simpl.
      repeat prove_post.
      unfold decode in *.
       repeat clean_arith;
       autorewrite with fwd_rewrites in *; eauto;
       eauto; cbv; try lia.
       prove_post.
       eapply existSR_done.
       prove_related_and_indist.
  }
  {
    (* Writeback *)
      Ltac local_aux HA6 head0 HB1 addr Heqb:= 
          light_clean_propagate;
          eexists;
          split; (* Do execute*)
          [ eapply existSR_step with (r:= 5%nat);simpl; repeat clean_arith; subst |..];
           [ step_method_spec; simpl;
           repeat clean_arith;
           repeat blast_arith;
           autorewrite with fwd_rewrites in *; eauto;
           erewrite HA6; eauto; cbv; try lia 
           (* Empty ildbuffer *)
            | ..];
          [ 
            eapply existSR_substep with (instance_i := 7%nat) (r:= 0%nat);
            [simpl;eauto |..];
            [simpl; reflexivity |..];
            [substep 16%nat ; eexists; eexists ( split1 head0) ; split; eauto |..];
            [eapply existSR_done |..] 
          |..];
          [assert_related simul_implies_indistinguishable;
          simpl; post_rule_state; split;
          [
               wrapped_arrays_equal 3%nat
              ; wrapped_arrays_equal 14%nat
              ; merge_simpl; eauto 6
          | ..];
          idtac;[split; simpl;eauto;
          let newH := fresh in try (intro newH; cbv in newH); try lia |..];
          [split; simpl;eauto | ..];
          [autorewrite with fwd_rewrites in *; eauto; clean_arith;
            intros;  specialize (HB1 addr); rewrite HB1;
            destruct (addr =? split1 head0) eqn:?;
            rewrite N.eqb_sym in  Heqb;
            rewrite Heqb; simpl; eauto | ..] |..].
    time (unfold lift_to in *;
    clear indistinguishable_i_s;
    simpl in related_i_s; light_clean_propagate).
    eapply wpa_to_cps in HA3.
    simpl_in HA3.
    light_clean_propagate;
    destruct HB2;
    light_clean_propagate.
    destruct HB0;
    light_clean_propagate.
    simpl in * |- .
    light_clean_propagate.
    repeat simpl_applylog.
    simpl in * |- .
    light_clean_propagate.
    repeat clean_arith.
    repeat merge_simpl.

          local_aux HA6 head HB1 addr Heqb.
  
    light_clean_propagate.
    simpl in * |- .
    light_clean_propagate.
    repeat simpl_applylog.
    simpl in * |- .
    light_clean_propagate.
    repeat clean_arith.
    repeat merge_simpl.

          local_aux HA6 head HB1 addr Heqb.

    destruct HB0;
    light_clean_propagate;
    destruct HB0;
    light_clean_propagate;
    simpl in * |- ;
    light_clean_propagate;
    repeat simpl_applylog;
    simpl in * |- ;
    light_clean_propagate;
    repeat clean_arith;
    repeat merge_simpl.
          local_aux HA6 head HB1 addr Heqb.
          local_aux HA6 head HB1 addr Heqb.
          local_aux HA6 head HB1 addr Heqb.
          local_aux HA6 head HB1 addr Heqb.
  }
  {
    unfold lift_to in *;
    simpl in related_i_s; light_clean_propagate; clear indistinguishable_i_s;
    simpl in * |-; min_straight_line; repeat simpl_applylog; min_straight_line;
      light_clean_propagate; simpl in * |- ; light_clean_propagate.

    (* characterize_arrays; light_clean_propagate. *)
     (* try abstract (idtac; [( *)
      eexists;
      split. 

    eapply existSR_substep with (instance_i := 8%nat) (r:= 0%nat); simpl; repeat clean_arith; subst;
      [ simpl; eauto | simpl; eauto | substep 16%nat ; eexists; eexists addr_killed; split; eauto |..];
      [eapply existSR_done | ..].

      assert_related simul_implies_indistinguishable;
      [simpl; post_rule_state; split; 
      [
           wrapped_arrays_equal 14%nat
          ; wrapped_arrays_equal 14%nat
          ; merge_simpl; eauto 6
      | 
      split; simpl;eauto
      ] | ..].
  }
  Unshelve.
  eauto.
  eauto.
  eauto.
  eauto.
  Unshelve.
  Time Qed.
End Correctness.
