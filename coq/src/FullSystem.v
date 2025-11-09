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

Require Import FunctionalExtensionality.

Require Processor.
Require MemoryUntagged.

Require Import egg.Loader.
Require Import Tactics.
Open Scope N.

Module FullSystemSpec.
    Local Instance system_modules : instances :=
        #| 
        Processor.SimpleProcessorSpec.interface proc;
        MemoryUntagged.mkMem imem;
        MemoryUntagged.mkMem dmem
        |#.

    Definition enq_mmio :=
        (action_method (d)
             ((proc enq_mmio) d)).
    Arguments enq_mmio /.

    Definition mmio_req := 
        (value_method ()
            ((proc mmio_req))).
    Arguments mmio_req /.

    Definition deq_mmio := 
        (action_method ()
            ((proc deq_mmio))).
    Arguments deq_mmio /.

    Definition send_ireq :=
        (rule 
            (begin 
                (set cur ((proc first_ireq)))
                ((proc deq_ireq))
                ((imem enq_req) cur)
                )).
    Arguments send_ireq /.

    Definition send_iresp :=
        (rule
            (begin 
                (set cur ((imem resp)))
                ((imem deq_resp))
                ((proc enq_iresp) cur))).
    Arguments send_iresp /.
    Definition send_dreq :=
        (rule 
            (begin 
                (set cur ((proc first_dreq)))
                ((proc deq_dreq))
                ((dmem enq_req) cur)
                )).
    Arguments send_dreq /.

    Definition send_dresp :=
        (rule
            (begin 
                (set cur ((dmem resp)))
                ((dmem deq_resp))
                ((proc enq_dresp) cur)
                )).
    Arguments send_dresp /.
  
  Global Instance interface : module _ := 
    module#(rules [send_ireq; send_iresp; send_dreq; send_dresp]
            vmet [mmio_req] amet [ enq_mmio; deq_mmio]).
End FullSystemSpec.

Module FullSystemGeneralSpec.
    Local Instance system_modules : instances :=
      #| 
        Processor.ProcessorSpec.interface proc;
        MemoryUntagged.mkMem imem;
        MemoryUntagged.mkMem dmem
      |#.
    Definition enq_mmio :=
        (action_method (d)
            (begin 
                ((proc enq_mmio) d)
                )).
    Arguments enq_mmio /.

    Definition mmio_req := 
        (value_method ()
            ((proc mmio_req))).
    Arguments mmio_req /.

    Definition deq_mmio := 
        (action_method ()
            ((proc deq_mmio))).
    Arguments deq_mmio /.

    Definition send_ireq :=
        (rule 
            (begin 
                (set cur ((proc first_ireq)))
                ((proc deq_ireq))
                ((imem enq_req) cur)
                )).
    Arguments send_ireq /.

    Definition send_iresp :=
        (rule
            (begin 
                (set cur ((imem resp)))
                ((imem deq_resp))
                ((proc enq_iresp) cur))).
    Arguments send_iresp /.
    Definition send_dreq :=
        (rule 
            (begin 
                (set cur ((proc first_dreq)))
                ((proc deq_dreq))
                ((dmem enq_req) cur)
                )).
    Arguments send_dreq /.

    Definition send_dresp :=
        (rule
            (begin 
                (set cur ((dmem resp)))
                ((dmem deq_resp))
                ((proc enq_dresp) cur)
                )).
    Arguments send_dresp /.
  
  Global Instance interface : module _ := 
    module#(rules [send_ireq; send_iresp; send_dreq; send_dresp]
            vmet [mmio_req] amet [ enq_mmio; deq_mmio]).
End FullSystemGeneralSpec.
(* We now need to state the theorem with the notion of flushing? *)


Section Correctness.
    Context {uninterp : Uninterpreted_Functions}.

    Import LoadBufferStoresafe.
    Inductive mem_flushes : 
      (* dmem_i and dmem_s  *)
        MemoryUntagged.memory_state -> 
        MemoryUntagged.memory_state -> 
        (* requests in implementation fifo_to_dmem_i *)
        list N ->
        (* dlb *)
        (N -> LoadBufferStoresafe.Entry) ->
       Prop := 
      | mem_flushed : forall (m : N -> N) (dld_buffer : N -> Entry),
          (forall addr observed , 
          outI (dld_buffer addr) = O /\ 
          outV (dld_buffer addr) = O /\ 
          (In observed (res (dld_buffer addr)) ->
          m addr =  observed)) ->
          mem_flushes 
              {| MemoryUntagged.mem := m; MemoryUntagged.resps := [] |}
              {| MemoryUntagged.mem := m; MemoryUntagged.resps := [] |}
              [] dld_buffer
      | do_addreq_st :
        forall mi ms req reqs dlb,
        dlet {iswrite addr data} := req in 
        iswrite = 1 ->
        mem_flushes mi ms reqs dlb  ->
        mem_flushes mi
            {| MemoryUntagged.mem := 
              (fun a => if addr =? a then data else (MemoryUntagged.mem ms a)); 
              MemoryUntagged.resps := MemoryUntagged.resps ms |}
            (reqs ++ [req]) 
            (fun a => if addr =? a then storeReq' (dlb addr) else dlb a) 
      | do_addreq_ld :
        forall mi ms req reqs dlb,
        dlet {iswrite addr data} := req in 
        iswrite = 0 ->
        mem_flushes mi ms reqs dlb  ->
        mem_flushes mi ms (reqs++ [req]) 
        (* No need to update  *)
            (fun a => if addr =? a then loadReq' (dlb addr) else dlb a)
      | do_process_ldreq :
        forall mem resps ms req reqs dlb,
        dlet {iswrite addr data} := req in 
        iswrite = 0 ->
        mem_flushes {| MemoryUntagged.mem := mem; 
                       MemoryUntagged.resps := resps |} ms (req::reqs) dlb  ->
        mem_flushes {| MemoryUntagged.mem := mem;
                       MemoryUntagged.resps := resps ++ [{# addr (mem addr)}] |} 
                    ms reqs dlb
      | do_process_streq :
        forall mem resps ms req reqs dlb,
        dlet {iswrite addr data} := req in 
        iswrite = 1 ->
        mem_flushes {| MemoryUntagged.mem := mem; 
                       MemoryUntagged.resps := resps |} ms (req::reqs) dlb  ->
        mem_flushes {| MemoryUntagged.mem := (fun a => if addr =? a then data else mem a);
                       MemoryUntagged.resps := resps |} 
                    ms reqs dlb    
    | do_resp_ld :
        forall mem resps ms resp reqs dlb,
        dlet {addr data} := resp in 
        mem_flushes {| MemoryUntagged.mem := mem; 
                       MemoryUntagged.resps := resp :: resps |} ms reqs dlb  ->
        mem_flushes {| MemoryUntagged.mem := mem;
                       MemoryUntagged.resps := resps |} 
                    ms reqs 
                    (fun a => if addr =? a then loadResp' (dlb addr) data else dlb a)
   | do_invalidate :
        forall mi ms reqs dlb addr,
        mem_flushes mi ms reqs dlb  ->
        mem_flushes mi ms reqs 
                    (fun a => if addr =? a then invalidate' (dlb addr) else dlb a)
      .



    Lemma flushes_empty_resp :  forall mi ms reqs dlb, mem_flushes mi ms reqs dlb ->  MemoryUntagged.resps ms = [].
      induction 1; eauto.
      Qed.


    Definition count_addr_resp (resps : list N) (addr : N) : nat:=
      List.length (List.filter (fun resp => 
                                    dlet {addr_resp data} := resp in 
                                    addr_resp =? addr) resps).
    Arguments count_addr_resp  !resps addr /.


      Definition count_addr_reqs (resps : list N) (addr : N) : nat:=
      List.length (List.filter (fun resp => 
                                    dlet {iswrite addr_resp data} := resp in 
                                    andb (addr_resp =? addr) (iswrite =? 0)) resps).
      Arguments count_addr_reqs  !resps addr /.

      Lemma countreqs_app : 
        forall  a b addr, 
          count_addr_reqs  (a++b) addr = (count_addr_reqs a addr + count_addr_reqs b addr)%nat.
          induction a.
          {
            simpl; eauto.
          }
          {
            simpl.
            intros.
            destruct (_ =? _) eqn:?.
            simpl.
            destruct (split1 a =? _) eqn:?.
            simpl.
            change (Datatypes.length (filter (fun resp : N =>  ((split1 (split2 resp) =? addr) && (split1 resp =? 0))%bool) (a0 ++ b))) with  (count_addr_reqs (a0 ++ b) addr).
            change (Datatypes.length (filter (fun resp : N => ((split1 (split2 resp) =? addr) && (split1 resp =? 0))%bool) (a0 ))) with  (count_addr_reqs (a0) addr).
            erewrite IHa; eauto.
            change (Datatypes.length (filter (fun resp : N =>  ((split1 (split2 resp) =? addr) && (split1 resp =? 0))%bool) (a0 ++ b))) with  (count_addr_reqs (a0 ++ b) addr).
            change (Datatypes.length (filter (fun resp : N => ((split1 (split2 resp) =? addr) && (split1 resp =? 0))%bool) (a0 ))) with  (count_addr_reqs (a0) addr).
            eauto.
            simpl.
            change (Datatypes.length (filter (fun resp : N =>  ((split1 (split2 resp) =? addr) && (split1 resp =? 0))%bool) (a0 ++ b))) with  (count_addr_reqs (a0 ++ b) addr).
            change (Datatypes.length (filter (fun resp : N => ((split1 (split2 resp) =? addr) && (split1 resp =? 0))%bool) (a0 ))) with  (count_addr_reqs (a0) addr).
            eauto.
          }
          Qed.
          
      Lemma countresp_app : 
        forall  a b addr, 
          count_addr_resp  (a++b) addr = (count_addr_resp a addr + count_addr_resp b addr)%nat.
          induction a.
          {
            simpl; eauto.
          }
          {
            simpl.
            intros.
            destruct (_ =? _) eqn:?.
            simpl.
            change (Datatypes.length (filter (fun resp : N => split1 (resp) =? addr) (a0 ++ b))) with  (count_addr_resp (a0 ++ b) addr).
            change (Datatypes.length (filter (fun resp : N => split1 (resp) =? addr) (a0 ))) with  (count_addr_resp (a0) addr).
            erewrite IHa; eauto.
            change (Datatypes.length (filter (fun resp : N => split1 (resp) =? addr) (a0 ++ b))) with  (count_addr_resp (a0 ++ b) addr).
            change (Datatypes.length (filter (fun resp : N => split1 (resp) =? addr) (a0 ))) with  (count_addr_resp (a0) addr).
            eauto.
          }
          Qed.

    Lemma out_bounds:  
      forall mi ms l dlb, mem_flushes mi ms l dlb -> 
        forall addr, 
        (outI (dlb addr) + outV (dlb addr) = count_addr_resp (MemoryUntagged.resps mi) addr + count_addr_reqs l addr )%nat.
        induction 1; simpl; eauto.
        {
          intros.
          cbn.
          specialize (H addr 0).
          lia.
        }
        {
          intros.
          destruct (addr =? _) eqn:?.
          simpl in *.
          clean_arith; subst.
          rewrite PeanoNat.Nat.add_0_r.
          rewrite countreqs_app.
          simpl.
          subst iswrite.
          rewrite H.
          rewrite Bool.andb_comm.
          simpl.
          rewrite PeanoNat.Nat.add_0_r.
          eapply IHmem_flushes.
          rewrite countreqs_app.
          simpl.
          subst iswrite.
          rewrite H.
          rewrite Bool.andb_comm.
          simpl.
          rewrite PeanoNat.Nat.add_0_r.
          eapply IHmem_flushes.
        }
        {
          intros.
          destruct (addr =? _) eqn:?.
          simpl in *.
          clean_arith; subst.
          rewrite countreqs_app.
          simpl.
          subst iswrite.
          rewrite H.
          rewrite Bool.andb_comm.
          simpl.
          destruct (_ =? addr) eqn:?; simpl;
          try clean_arith; subst.
          specialize (IHmem_flushes addr);
          lia.
          specialize (IHmem_flushes addr);
          lia.
          rewrite countreqs_app.
          simpl.
          subst iswrite.
          rewrite H.
          rewrite Bool.andb_comm.
          simpl.
          destruct (_ =? addr0) eqn:?; simpl;
          specialize (IHmem_flushes addr0);
          lia.
        }
        {
          intros.
          rewrite countresp_app.
          simpl.
          merge_simpl.
          simpl in IHmem_flushes.
                destruct (_ =? addr0) eqn:?; simpl.
          specialize (IHmem_flushes (split1 (split2 req)) ).
          subst addr.
          clean_arith; light_clean_propagate.
          rewrite N.eqb_refl in IHmem_flushes.
          subst data; rewrite H in IHmem_flushes; simpl in IHmem_flushes.
          fold (count_addr_reqs reqs (split1 (split2 req))) in IHmem_flushes.
          lia.
          specialize (IHmem_flushes addr0).
          clean_arith.
          eapply N.eqb_neq in Heqb.
          subst addr.
          rewrite Heqb in IHmem_flushes.
          simpl in IHmem_flushes.
          fold (count_addr_reqs reqs addr0) in IHmem_flushes.
          lia.
        }
        {
          intros.
          simpl in *.
          subst iswrite.
          specialize (IHmem_flushes addr0).
          rewrite H in IHmem_flushes.
          rewrite Bool.andb_comm in IHmem_flushes.
          simpl in IHmem_flushes.
          fold (count_addr_reqs reqs addr0) in IHmem_flushes.
          lia.
        }
        {
          intros.
          destruct (_ =? _) eqn:?.
          clean_arith; subst.
          simpl in *.
          destruct (dlb addr) eqn:?; simpl.
          destruct outI; destruct outV; simpl in *.
          specialize (IHmem_flushes addr).
          rewrite Heqe in IHmem_flushes.
          simpl in IHmem_flushes.
          subst addr.
          rewrite N.eqb_refl in IHmem_flushes.
          simpl in IHmem_flushes.
          inversion IHmem_flushes.
          specialize (IHmem_flushes addr).
          rewrite Heqe in IHmem_flushes.
          simpl in IHmem_flushes.
          subst addr.
          rewrite N.eqb_refl in IHmem_flushes.
          simpl in IHmem_flushes.
          fold (count_addr_resp resps (split1 resp)) in IHmem_flushes.
          lia.
          specialize (IHmem_flushes addr).
          rewrite Heqe in IHmem_flushes.
          simpl in IHmem_flushes.
          subst addr.
          rewrite N.eqb_refl in IHmem_flushes.
          simpl in IHmem_flushes.
          fold (count_addr_resp resps (split1 resp)) in IHmem_flushes.
          lia.
          specialize (IHmem_flushes addr).
          rewrite Heqe in IHmem_flushes.
          simpl in IHmem_flushes.
          subst addr.
          rewrite N.eqb_refl in IHmem_flushes.
          simpl in IHmem_flushes.
          fold (count_addr_resp resps (split1 resp)) in IHmem_flushes.
          lia.
          specialize (IHmem_flushes addr0).
          simpl in *.
          subst addr.
          rewrite Heqb in IHmem_flushes.
          fold (count_addr_resp resps addr0) in IHmem_flushes.
          lia.
        }
        {
          intros. 
          destruct ( _=?_) eqn:?; simpl; eauto.
          clean_arith; subst.
          eapply IHmem_flushes.
        }
        Qed.

   Lemma out_upper:  
      forall mi ms l dlb, mem_flushes mi ms l dlb -> 
        forall pre req post,
        l = pre ++ [req] ++ post ->
       dlet {iswrite addr data} := req in 
        iswrite = 1 ->
        (outV (dlb addr) <= count_addr_reqs post addr)%nat.
      induction 1; simpl; eauto.
      {
        intros.
        destruct pre; inversion H0.
      }
      {
        intros.
        destruct (addr =? _) eqn:?.
        subst addr.
        simpl in *.
        lia.
         destruct post using List.rev_ind.
        2:{
          simpl in *.
          rewrite app_comm_cons in H1.
          rewrite app_assoc in H1.
          eapply app_inj_tail in H1.
          light_clean_propagate.
          clear IHpost.
          rewrite countreqs_app.
          simpl.
          subst addr.
          rewrite Heqb.
          subst data; rewrite H;
          simpl.
          rewrite PeanoNat.Nat.add_0_r.
          eapply IHmem_flushes.
          eauto.
          eauto.
        }
        eapply app_inj_tail in H1.
        light_clean_propagate.
        subst addr.
        simpl in Heqb; rewrite N.eqb_refl in Heqb; inversion Heqb.
      }
      {
        intros.
        destruct (addr =? _) eqn:?;simpl in *.
        {
          clean_arith.
          subst addr.
          rewrite Heqb.
         destruct post using List.rev_ind.
        2:{
          simpl in *.
          rewrite app_comm_cons in H1.
          rewrite app_assoc in H1.
          eapply app_inj_tail in H1.
          light_clean_propagate.
          clear IHpost.
          rewrite countreqs_app.
          simpl.
          rewrite Heqb.
          subst data; rewrite H;
          simpl.
          rewrite N.eqb_refl.
          simpl.
          specialize (IHmem_flushes) with (1:= eq_refl).
          specialize (IHmem_flushes H2).
          lia.
        }
        eapply app_inj_tail in H1.
        light_clean_propagate.
        subst data.
        rewrite H in H2.
        inversion H2.
        }
        {
          light_clean_propagate.
          clean_arith.
          subst addr.
         destruct post using List.rev_ind.
        2:{
          simpl in *.
          rewrite app_comm_cons in H1.
          rewrite app_assoc in H1.
          eapply app_inj_tail in H1.
          light_clean_propagate.
          clear IHpost.
          rewrite countreqs_app.
          simpl.
          eapply N.eqb_neq in Heqb.
          rewrite Heqb.
          simpl.
          rewrite PeanoNat.Nat.add_0_r.
          eapply IHmem_flushes; eauto.
        }
         eapply app_inj_tail in H1.
        light_clean_propagate.
        subst data.
        rewrite H in H2.
        inversion H2.
      }
    }
    {
        intros.
        eapply (IHmem_flushes (req::pre) req0 post).
        simpl.
        rewrite H1.
        eauto.
        eauto.
    }
    {
        intros.
        eapply (IHmem_flushes (req::pre) req0 post).
        simpl.
        rewrite H1.
        eauto.
        eauto.
    }
    {
        intros.
        light_clean_propagate.
        simpl in *.
        specialize (IHmem_flushes) with (1:= eq_refl).
        specialize (IHmem_flushes H1) .
        destruct (addr =? _) eqn:?;simpl in *.
        {
          destruct (dlb addr) eqn:?; simpl in *.
          destruct outV; destruct outI.
          simpl; lia.
          simpl; lia.
          simpl.
          clean_arith.
          subst addr.
          rewrite Heqb in *.
          rewrite Heqe in IHmem_flushes; simpl in *.
          lia.
          simpl.
          clean_arith.
          subst addr.
          rewrite Heqb in *.
          rewrite Heqe in IHmem_flushes; simpl in *.
          lia.
        }
        {
          eauto.
        }
      }
      {
        intros.
        destruct (_ =? _) eqn:?; simpl; eauto. 
        clean_arith; subst; eauto.
      }
      Qed.

   Lemma out_upper_aux:  
      forall mi ms l dlb, mem_flushes mi ms l dlb -> 
        forall pre req post,
        l = pre ++ [req] ++ post ->
       dlet {iswrite addr data} := req in 
        iswrite = 1 ->
        (outI (dlb addr) >= count_addr_reqs pre addr + count_addr_resp (MemoryUntagged.resps mi) addr)%nat.
        pose proof out_bounds.
        intros.
        specialize (H) with (1:= H0).
        specialize (H addr).
        assert (outI (dlb addr) =(count_addr_resp (MemoryUntagged.resps mi)
          addr + count_addr_reqs l addr)%nat -outV (dlb addr))%nat.
        lia.
        rewrite H3.
        rewrite H1.
        rewrite countreqs_app.
        rewrite countreqs_app.
        pose proof out_upper.
        specialize (H4) with (1:= H0).
        specialize (H4 _ _ _ H1 H2).
        clear H3.
        subst addr.
        lia.
      Qed.


   Lemma store_or_no_store : forall l addr,
    (Forall (fun e => dlet {iswrite add data} := e in add = addr -> iswrite = 0) l)
     \/ 
     (* Or there is at least one store to that address *)
     exists e, (In e l /\ 
     dlet {iswrite add data} := e in add = addr /\ iswrite <> 0
     ).
     induction l.
     {
      eauto.
     }
     {
      simpl in *.
      intros; eauto.
      specialize (IHl addr).
      destruct IHl.
      2:{
        light_clean_propagate.  right.  eexists.  repeat split; eauto.
      }
      {
      destruct ((split1 (split2 a)) =? addr) eqn:?.
      {
        clean_arith.
        destruct (split1 a =? 0) eqn:?.
        left; eauto.
        clean_arith;  eauto.
        clean_arith.
        right.
        eexists.
        eauto.
      }
      {
        clean_arith.
        left;eauto.
        econstructor.
        intros; contradiction.
        eauto.
      }
     }
     }
   Qed.


  Lemma flushes_writeOrNot:  
  (* None of the request in the queue are store to an address that is available in the load buffer *)
  forall mi ms reqs dlb, mem_flushes mi ms reqs dlb -> 
      forall req, 
       In req reqs ->
        dlet {iswrite addr2 data} := req in 
        (iswrite = 0 \/ iswrite = 1).
      induction 1; simpl; eauto.
      {
        intros; contradiction. 
      }
      {
        intros.
        eapply in_app_iff in H1.
        destruct H1.
        eapply IHmem_flushes; eauto.
        inversion H1.
        2:{ inversion H2. }
        subst.
        right; eauto.
      }
      {
        intros.
        eapply in_app_iff in H1.
        destruct H1.
        eapply IHmem_flushes; eauto.
        inversion H1.
        2:{ inversion H2. }
        subst.
        left; eauto.
      }
      {
        simpl in *.
        intros.
        eapply IHmem_flushes; eauto.
      }
      {
        simpl in *.
        intros.
        eapply IHmem_flushes; eauto.
      }
      Qed.

      Lemma no_store_easy:  
      forall l mi ms dlb, 
      mem_flushes mi ms l dlb ->
      forall req pre post,
      l = pre ++ [req] ++ post ->
      dlet {iswrite addr data} := req in 
      iswrite = 1 -> 
      Forall (fun req => 
       dlet {iswrite addr_r data} := req in 
        addr_r = addr ->
        iswrite = 0) post ->
      (MemoryUntagged.mem ms addr = data ).
      induction 1.
      {
        simpl; eauto.
        intros.
        destruct pre; inversion H0.
      }
      {
        intros.
        simpl in *.
        destruct post using List.rev_ind.
        2:{
          simpl in *.
          rewrite app_comm_cons in H1.
          rewrite app_assoc in H1.
          eapply app_inj_tail in H1.
          light_clean_propagate.
          clear IHpost.
          eapply Forall_app in H3.
          light_clean_propagate.
          inversion HB.
          subst.
          clear H5.
          destruct (_ =? _) eqn:?.
          clean_arith.
          subst addr addr0.
          subst data .
          erewrite H4 in H.
          inversion H.
          eauto.
          eapply IHmem_flushes.
          eauto.
          eauto.
          eauto.
        }
        eapply app_inj_tail in H1.
        light_clean_propagate.
        merge_simpl.
        clear H3.
        subst addr addr0 data0.
        rewrite N.eqb_refl.
        eauto.
      }
      {
        intros.
        simpl in *.
        destruct post using List.rev_ind.
        2:{
          simpl in *.
          rewrite app_comm_cons in H1.
          rewrite app_assoc in H1.
          eapply app_inj_tail in H1.
          light_clean_propagate.
          clear IHpost.
          eapply IHmem_flushes; eauto.
          eapply Forall_app in H3.
          light_clean_propagate.
          eauto.
        }
        eapply app_inj_tail in H1.
        light_clean_propagate.
        merge_simpl.
        clear H3.
        subst data addr addr0 data0.
        rewrite H2 in H; inversion H.
      }
      {
        intros.
        specialize (IHmem_flushes req0 (req::pre) post).
        rewrite H1 in IHmem_flushes.
        simpl in *.
        specialize (IHmem_flushes eq_refl H2).
        subst addr0.
        auto_specialize.
        eauto.
      }
      {
        intros.
        specialize (IHmem_flushes req0 (req::pre) post).
        rewrite H1 in IHmem_flushes.
        simpl in *.
        specialize (IHmem_flushes eq_refl H2).
        subst addr0.
        auto_specialize.
        eauto.
      }
      {
        intros.
        specialize (IHmem_flushes req (pre) post).
        simpl in *.
        specialize (IHmem_flushes H0 H1 H2).
        eauto.
      }
      {
        intros.
        eauto.
      }
      Qed.

    Lemma no_store_easy2:  
      forall l mi ms dlb, 
      mem_flushes mi ms l dlb ->
      (* If there is not store to that address *)
      forall addr,
      Forall (fun req => 
       dlet {iswrite addr_r data} := req in 
        addr_r = addr ->
        iswrite = 0) l ->
      (MemoryUntagged.mem ms addr = MemoryUntagged.mem mi addr).
      induction 1.
      {
        simpl; eauto.
      }
      {
        intros.
        eapply Forall_app in H1.
        light_clean_propagate.
        inversion HB.
        auto_specialize.
        subst.
        subst data addr.
        simpl in *.
        clear H4.
        destruct (_ =? _) eqn:?.
        {
          simpl in *.
          clean_arith.
          subst.
          auto_specialize.
          rewrite H3 in H.
          inversion H.
        }
        eapply IHmem_flushes; eauto.
      }
      {
        intros.
        eapply Forall_app in H1.
        light_clean_propagate.
        inversion HB.
        auto_specialize.
        subst.
        eauto.
      }
      {
        intros.
        simpl in *.
        eapply IHmem_flushes.
        simpl; eauto.
      }
      {
        intros.
        simpl in *.
        destruct (_ =? _) eqn:?.
        {
          simpl in *.
          clean_arith.
          subst.
          subst addr. 
          pose proof no_store_easy.
          specialize H2 with (1:= H0).
          specialize (H2 req [] reqs eq_refl).
          simpl in *.
          auto_specialize.
          auto_specialize.
          eauto.
        }
        eapply IHmem_flushes; eauto.
        econstructor; eauto.
        intros.
        rewrite <- H2 in Heqb.
        subst addr.
        rewrite N.eqb_refl in Heqb.
        inversion Heqb.
      }
      {
        intros.
        simpl in *.
        eauto.
      }
      {
        intros.
        simpl in *.
        eauto.
      }
      Qed.

   Lemma flushes_noOutdated:  
    forall mi ms reqs dlb, mem_flushes mi ms reqs dlb -> 
      forall pre resp post , 
       (MemoryUntagged.resps mi) = pre ++ [resp] ++ post ->
       dlet {addr data} := resp in 
       (outI (dlb addr) <= count_addr_resp pre addr)%nat ->
       data = MemoryUntagged.mem ms addr /\
       data = MemoryUntagged.mem mi addr
       .
      induction 1; simpl; eauto.
      {
        intros.
        destruct pre; inversion H0.
      }
      {
        intros.
        destruct (addr =? _) eqn:?.
        simpl in *.
        pose proof out_bounds.
        specialize H3 with (1:= H0).
        specialize (H3 addr).
        rewrite H3 in H2.
        light_clean_propagate.
        rewrite H1 in *.
        rewrite countresp_app in H3.
        simpl in  H3.
        rewrite N.eqb_sym in Heqb.
        rewrite Heqb in H3.
        simpl in H3.
        2:{ eapply IHmem_flushes; eauto.
            simpl. eapply H1. }
        clean_arith.
        rewrite Heqb in H2.
        rewrite countresp_app in H2.
        simpl in H2.
        rewrite Heqb in H2.
        rewrite N.eqb_refl in H2.
        simpl in H2.
        fold (count_addr_resp post addr) in H2.
        lia.
      }
      {
        intros.
        destruct (addr =? _) eqn:?;simpl in *.
        {
          clean_arith.
          light_clean_propagate.
          (* subst addr. *)
          eapply IHmem_flushes; eauto.
          rewrite <- Heqb in *; eauto.
        }
        {
          light_clean_propagate.
          eapply IHmem_flushes; eauto.
        }
      }
      {
        intros.
        simpl in *.
        destruct post using List.rev_ind.
        2:{
          simpl in *.
          rewrite app_comm_cons in H1.
          rewrite app_assoc in H1.
          eapply app_inj_tail in H1.
          light_clean_propagate.
          clear IHpost.
          eapply IHmem_flushes.
          eauto.
          eauto.
        }
        eapply app_inj_tail in H1.
        light_clean_propagate.
        merge_simpl.
        split; eauto.
        pose proof (store_or_no_store reqs addr).
        destruct H1.
        2:{
          light_clean_propagate.
          pose proof flushes_writeOrNot.
          specialize (H1) with (1:= H0).
          simpl in H1.
          assert (split1 e = 1).
          epose proof (or_intror (A:= (req=e)) HA).
          specialize (H1) with (1:=H3).
          destruct H1; lia.
          (* clear H4 H5. *)

          eapply in_split in HA.
          light_clean_propagate.

          pose proof out_upper_aux.
          specialize (H4) with (1:= H0).
          specialize (H4 (req::l1) e l2 eq_refl H3).
          simpl in H1.
          rewrite H3 in *.
          (* subst iswrite. *)
          simpl in *.
          rewrite HA0 in H4.
          rewrite N.eqb_refl in H4.
          rewrite H in H4.
          simpl in H4.
          lia.
        }
        {
          pose proof no_store_easy2.
          specialize (H3) with (1:= H0).
          assert ( Forall (fun e : N => dlet {iswrite add data}:= e in add = addr -> iswrite = 0) (req::reqs)).
          {
            econstructor; eauto.
          }
          auto_specialize.
          eauto.
       
        }

      }
      {
        intros.
        destruct (addr =? _) eqn:?;simpl in *.
        {
          clean_arith.
          light_clean_propagate.
          (* subst addr. *)
          pose proof out_upper.
          specialize (H1) with (1:= H0).
          specialize (H1 [] req reqs eq_refl).
          simpl in *. 
          (* subst iswrite. *)
          specialize (H1 H).

          pose proof out_bounds.
          specialize (H3) with (1:= H0).
          specialize (H3 (split1 (split2 req))).
          simpl in *.
          rewrite H in H3.

          rewrite Bool.andb_comm in H3.
          simpl in H3.
          fold (count_addr_reqs reqs (split1 (split2 req))) in H3.
          rewrite countresp_app in H3.
          simpl in H3.
          rewrite Heqb in H3.
          rewrite N.eqb_refl in H3.
          simpl in H3.

          fold (count_addr_resp post (split1 resp)) in H3.
          rewrite <- Heqb in H3.
          rewrite <- Heqb in H2.
          lia.
        }
        {
          light_clean_propagate.
          eapply IHmem_flushes.
          instantiate (1:= post).
          instantiate (1:= pre).
          reflexivity.
          simpl.
          eauto.
        }
      }
      {
        intros.
        destruct (addr =? _) eqn:?;simpl in *.
        {
          clean_arith.
          light_clean_propagate.
          (* subst addr. *)
          destruct (dlb (split1 resp)) eqn:?.
          simpl in *.
          destruct outI; destruct outV.
          simpl in *.
          pose proof out_bounds.
          specialize (H0) with (1:= H).
          specialize (H0 (split1 resp)).
          rewrite Heqe in H0.
          simpl in *.
          rewrite N.eqb_refl in H0.
          simpl in *.
          lia.
          simpl in *.
          eapply (IHmem_flushes (resp:: pre) resp0 post).
          eauto.
          rewrite <- Heqb.
          rewrite Heqe.
          simpl.
          lia.
          simpl in *.
          eapply (IHmem_flushes (resp:: pre) resp0 post).
          eauto.
          simpl.
          rewrite <- Heqb.
          rewrite N.eqb_refl.
          simpl.
          fold (count_addr_resp pre (split1 resp)) .
          rewrite Heqe.
          simpl.
          rewrite Heqb.
          lia.
          simpl in *.
          eapply (IHmem_flushes (resp:: pre) resp0 post).
          eauto.
          simpl.
          rewrite <- Heqb.
          rewrite N.eqb_refl.
          simpl.
          fold (count_addr_resp pre (split1 resp)) .
          rewrite Heqe.
          simpl.
          rewrite Heqb.
          lia.
        }
        eapply (IHmem_flushes (resp:: pre) resp0 post).
        rewrite H0.
        eauto.
        simpl.
        subst addr.
        rewrite Heqb.
        fold (count_addr_resp pre (split1 resp0)) .
        eauto.
      }
      {
        intros.
        destruct (_ =? _) eqn:?; simpl in *; try clean_arith; subst; eauto.
      }
      Qed.

    Lemma flushes_readdlb:  forall mi ms reqs dlb, mem_flushes mi ms reqs dlb -> 
      (* This theorem is false *)
      forall addr hd, 
       In hd (res (dlb addr)) -> MemoryUntagged.mem ms addr = hd.
       (* Si res est some, il y a pas de store dans la queue *)
      induction 1; simpl; eauto.
      {
        intros.
        eapply H; eauto.
      }
      {
        intros.
        destruct (addr =? addr0) eqn:?.
        inversion H1.
        eapply IHmem_flushes;  eauto.
      }
      {
        intros.
        destruct (addr =? addr0) eqn:?;simpl in *.
        {
          clean_arith.
          light_clean_propagate.
          eapply IHmem_flushes; eauto.
        }
        {
          light_clean_propagate.
          eapply IHmem_flushes; eauto.
        }
      }
      {
        intros.
        destruct (addr =? addr0) eqn:?;simpl in *.
        {
          clean_arith.
          light_clean_propagate.
          simpl in *.
          destruct (dlb (split1 resp)) eqn:?.
          simpl in *.
          destruct outI eqn:?;
          destruct outV eqn:?;
          simpl in *.
          {light_clean_propagate.
          eapply IHmem_flushes; eauto.
          rewrite Heqe. 
          simpl. eauto.
          }
          2:{
            subst.
            eapply IHmem_flushes.
            rewrite Heqe; eauto.
          }
          2:{
            subst.
            eapply IHmem_flushes.
            rewrite Heqe; eauto.
          }
          eapply in_app_iff in H0.
          destruct H0.
          eapply IHmem_flushes.
          rewrite Heqe; eauto.

          inversion H0; subst.
          2:{ inversion H1. }
          symmetry.
          pose proof flushes_noOutdated.
          specialize (H1 ) with (1:= H).
          simpl in *.
          clear H0.
          specialize (H1 [] resp resps eq_refl) . 
          (* subst addr. *)
          rewrite Heqe in H1.
          simpl in *.
          assert( 0<=0)%nat by lia.
          auto_specialize.
          light_clean_propagate.
          subst data.
          (* induction res. *)
          destruct (res) eqn:?.
          {
            simpl in *.
            lia.
          }
          {
            rewrite HA.
            eauto.
            (* (* erewrite IHmem_flushes; eauto.
            rewrite Heqe.
            simpl.
            simpl in *. *)
            eauto. *)
          }
        }
        {
          light_clean_propagate.
          eapply IHmem_flushes; eauto.
        }
      }
      {
        intros.
        destruct (_ =? _) eqn:?; simpl in *; try clean_arith; subst; eauto.
        destruct (res (dlb addr0)) eqn:?.
        inversion H0.
        simpl in *.
        assert (In hd (res (dlb addr0))).
        rewrite Heql.
        simpl.
        right; eauto.
        eauto.
      }
      Qed.

    Definition related (ist : SModule) (sst : SModule) := 
        exists 
            (pc : N)
            (s_state_machine : N) 
            (ild_buffer :  N -> list N)
            (dld_buffer :  N -> Entry)
            (decode_inst src_val1 src_val2 dest_val : N)
            (fifo_to_imem_i  fifo_to_dmem_i to_mmio from_mmio: list N)
            (imem_i imem_s : MemoryUntagged.memory_state)
            (dmem_i dmem_s : MemoryUntagged.memory_state)
            (fifo_from_imem fifo_to_imem_s: option N)
            (fifo_from_dmem fifo_to_dmem_s: option N)
            (rf : N -> N), 

            MemoryUntagged.mem imem_i = MemoryUntagged.mem imem_s /\
            sst = *[| [| pc; rf; s_state_machine; decode_inst; src_val1; src_val2;
                    dest_val; 
                    fifo_to_imem_s; fifo_from_imem; 
                    fifo_to_dmem_s; fifo_from_dmem; 
                    to_mmio; from_mmio |]; imem_s; dmem_s|]* /\ 
            ist = *[| [| pc; rf; s_state_machine; decode_inst; src_val1; src_val2;
                    dest_val; 
                    ild_buffer;
                    dld_buffer;
                    fifo_to_imem_i; fifo_from_imem; 
                    fifo_to_dmem_i; fifo_from_dmem; 
                     to_mmio; from_mmio; tt|]; imem_i; dmem_i|]*
            /\
            (* no write in IMem *)
            (forall e, In e fifo_to_imem_i -> split1 e = 0) /\
            (forall addr, 
                (* Ld_buffer is reflecting what's in the memory *)
            List.Forall (fun x => MemoryUntagged.mem imem_i addr = x) (ild_buffer addr)) /\
            (* Responses are faithful *)
            List.Forall (fun x => dlet { addr data} := x in 
                                    MemoryUntagged.mem imem_i addr = data) (MemoryUntagged.resps imem_i) /\
              (* Add invariant for the ilb? *)
            fifo_to_imem_s = None /\
            fifo_to_dmem_s = None /\
            MemoryUntagged.resps imem_s = nil /\
            MemoryUntagged.resps dmem_s = nil /\
            mem_flushes dmem_i dmem_s fifo_to_dmem_i dld_buffer .
    Arguments related / ist sst.


    Ltac post_rule_state := 
      repeat match goal with 
        | [ |- exists t, _] => eexists 
      end.


    Ltac symb_ex_met :=
              light_clean_propagate;
              straight_line.
    Ltac peel_of :=
            do 2 eexists;
            let y := (eexists_st_array 3%nat) in
            eexists y;
            unshelve instantiate (5:= _);
            [ let y := (eexists_st_array 13%nat) in
            exact y| ..];
            do 3 eexists.
    Ltac constraint_evars_before_wpa :=
            split; eauto;
            split; eauto.

    Ltac solve_evars := unfold state_t in *; PropLemmas.pose_lemmas; egg_eexists 4;  egg_repeat.
              (* Symbex *)
    Ltac match_refine :=
            unshelve instantiate (1:= _);
            [let y := (eexists_st_array 13%nat) in
            exact y |..];
             simpl;
            match goal with 
              | |- forall i, _ => 
              array_case_indexes i 13%nat; 
              simpl;eauto
              end .

    Ltac second_aux := 
          repeat match goal with 
              | [H: context[MemoryUntagged.mem] |- _] => clear H
              end;
          symb_ex_met; 
          peel_of;
          constraint_evars_before_wpa;
          split; [ reconstruct_wpa | ];
          idtac; [try solve [solve_evars]|..];
          idtac; [match_refine | ..];
          idtac; [try solve [intros; do 2 eexists; split; solve_evars; simpl;  eauto]| ..];
          simpl; eauto;
          [match goal with 
              | |- forall x, _ => 
                array_case_indexes  x 16%nat; try lia; eauto
              end | ..];
          apply_log_fn 3%nat;
            intros; eexists; let y := (eexists_st_array 13%nat) in eexists y; do 3 eexists;
            split ; [ eauto | ];
            split ; [ eauto | ];
            [ reflexivity | ..];
            split; [reconstruct_wpa|..];
            [try solve [solve_evars] | ..];
             [apply_log_fn 13%nat;
                intro;
                do 2 eexists;
                split;solve_evars | ..].
     

    Ltac indi_vm :=
       idtac; repeat match goal with 
                        | [H: context[MemoryUntagged.mem] |- _] => clear H
                        end;
      light_clean_propagate;
      straight_line; simpl;
      repeat econstructor;
      simpl;
      unfold state_t in *;
      PropLemmas.pose_lemmas; egg_eexists 4;
      egg_repeat.

    Ltac seq_eexists_prim k := 
            idtac; [eexists;
            let y := (eexists_st_array k) in
            eexists y;
            do 3 eexists| ..].


    Lemma simul_implies_indistinguishable : 
      forall ist sst, related ist sst -> 
          indistinguishable (spec_of  FullSystemGeneralSpec.interface) (spec_of FullSystemSpec.interface) ist sst.
      intros.  simpl in H.  light_clean_propagate.
      prove_indistinguishable'. 
      idtac;[ indi_vm | ..]. 
      idtac; [ second_aux | ..]. 
      idtac; repeat match goal with 
                        | [H: context[MemoryUntagged.mem] |- _] => clear H
                        end;
                         symb_ex_met; 
      simpl_applylog;
      peel_of; constraint_evars_before_wpa; 
      simpl in *|-.
      split;
      [reconstruct_wpa | ..].
      idtac; [unshelve instantiate (1:= _);
      [let y := (eexists_st_array 13%nat) in
      exact y | ..] | ..];
      simpl.
      idtac;[match goal with 
        | |- forall i, _ => 
        array_case_indexes i 13%nat; 
        simpl;eauto
        end ;
      intros;
      do 2 eexists| ..];
      simpl; eauto.
      2:{ simpl; eauto. }
      2:{ simpl; eauto. }
      idtac; [ match goal with 
      | |- forall x, _ => 
        array_case_indexes  x 15%nat; try lia; eauto
      end|..].
      idtac; [apply_log_fn 3%nat | ..].
      intros.
      seq_eexists_prim 13%nat.
      idtac; [split ; [ eauto | ] | ..].
      idtac; [split ; [ eauto | ] | ..].
      simpl; eauto.
      split;
      [reconstruct_wpa|..].
      apply_log_fn 13%nat.
      Qed.
     
    
    Theorem correct' : refines (spec_of  FullSystemGeneralSpec.interface) (spec_of FullSystemSpec.interface) related.
    Time prove_refinement.
    (* { admit. } *)
    {
        simpl in related_i_s.
        light_clean_propagate.
        min_straight_line.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        min_straight_line.
        repeat clean_arith.
        do 2 eexists.
        split.
        {
            eexists.
            let y := (eexists_st_array 3%nat) in
            eexists y.
            
            do 3 eexists.
            split.  { eauto.  }
            split; [ eauto | ].
            simpl.
            split.
            reconstruct.
            split;eauto.
            post_rule_state.
            unshelve instantiate (1:= _).
            let y := (eexists_st_array 13%nat) in
            exact y.
            split;eauto.
            split;eauto.
            split.
            reconstruct.
            split;eauto.
            apply_log_fn 13%nat.
            apply_log_fn 3%nat.
            intros.
            eexists.
            let y := (eexists_st_array 13%nat) in
            eexists y.
            do 3 eexists.
            split.  { eauto.  }
            split; [ eauto | ].
            simpl.
            split.
            reconstruct.
            split;eauto.
            apply_log_fn 13%nat.
        }
        split.
        {
        (* Nothing more to do  on the spec side *)
            eapply existSR_done.
        }
        assert_related simul_implies_indistinguishable.
        {
            simpl in *|-.
            light_clean_propagate.
            remove_ascii.
            simpl.
            post_rule_state. 
            split.  shelve.  split.  simpl.  apply f_equal. eapply ext_array; simpl; eauto.
            split. 
            wrapped_arrays_equal 3%nat.
            wrapped_arrays_equal 16%nat.
            split; eauto.
            split; eauto.
            split; eauto.
        }
    }
    (* { admit. } *)
    { 
        simpl in related_i_s.
        light_clean_propagate.
        min_straight_line.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        min_straight_line.
        repeat clean_arith.
        do 2 eexists.
        split.
        {
          simpl in *|-.
          light_clean_propagate.
          seq_eexists_prim 3%nat.
          simpl; split; eauto.
          simpl; split; eauto.
          simpl; split; eauto.
          reconstruct.
          simpl; split; eauto.
          eexists.
          seq_eexists_prim 13%nat.
          simpl; split; eauto.
          simpl; split; eauto.
          simpl; split; eauto.
          reconstruct.
          simpl; split; eauto.
          apply_log_fn 16%nat.
          apply_log_fn 3%nat.
         
            intros.
          seq_eexists_prim 13%nat.
          simpl; split; eauto.
          simpl; split; eauto.
          simpl; split; eauto.
          reconstruct.
          simpl; split; eauto.
          apply_log_fn 16%nat.
        }
        split.
        {
        (* Nothing more to do  on the spec side *)
            eapply existSR_done.
        }
        assert_related simul_implies_indistinguishable.
        {
          simpl in *|-.
          light_clean_propagate.
          simpl.
          post_rule_state. 
          split.
          shelve.
          split.
          wrapped_arrays_equal 3%nat.
          split.
          wrapped_arrays_equal 3%nat.
          wrapped_arrays_equal 16%nat.
          simpl; split; eauto.
          simpl; split; eauto.
          simpl; split; eauto.
        }
    }
    (* { admit. } *)
    {
        simpl in related_i_s.
        light_clean_propagate.
        min_straight_line.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        min_straight_line.
        repeat clean_arith.
        simpl in *|-.
        destruct (_ =? _) eqn:?.
        {
         (* The apply_alog are guards. *)
          repeat clean_arith;
          min_straight_line.
          repeat clean_arith.
          repeat simpl_applylog.
          light_clean_propagate.
          specialize (HA5 head).
          light_clean_propagate.
          assert (head = head \/ In head l ) as precond by eauto.
          specialize (HA5 precond).
          rewrite HA5 in Heqb; simpl in Heqb.
          inversion Heqb.
        }
        {
        eexists.
        split.
        {
          eapply existSR_done.
        }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            light_clean_propagate.
            post_rule_state. 
            split.
            shelve.
            split.
            simpl.
            wrapped_arrays_equal 3%nat.
            split.
            wrapped_arrays_equal 3%nat.
            match goal with 
            | |- _ = ?a => set a 
            end.
            change (MemoryUntagged.mem mem_st0 = MemoryUntagged.mem imem_s) 
              with ((fun x => MemoryUntagged.mem mem_st0 x) = (fun y => MemoryUntagged.mem imem_s y)) in HA2.
            change (MemoryUntagged.mem mem_st0 ) 
              with ((fun x => MemoryUntagged.mem mem_st0 x) ) in HB5.
           
            egg_simpl 4 nxt_st.
            simpl; subst s.
            wrapped_arrays_equal 16%nat.
       
            prove_outside nxt_st; eauto.
            prove_outside nxt_st; eauto.
            simpl; split; eauto.
            simpl; split; eauto.
            simpl; split; eauto.
            eapply Forall_app; split; eauto.
            econstructor; eauto.
            merge_simpl.
            eauto.
        }
      }
    } 
    Optimize Proof.
    (* { admit. } *)
    {
        simpl in related_i_s.
        light_clean_propagate.
        min_straight_line.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        min_straight_line.
        repeat clean_arith.
        simpl in *|-.
        eexists.
        split.
        {
          eapply existSR_done.
        }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            light_clean_propagate.
            change (MemoryUntagged.mem mem_st = MemoryUntagged.mem imem_s) 
              with ((fun x => MemoryUntagged.mem mem_st x) = (fun y => MemoryUntagged.mem imem_s y)) in HA2.
            post_rule_state. 
            split.
            shelve.
            split.
            simpl.  eauto.
            split.
            wrapped_arrays_equal 3%nat.
            wrapped_arrays_equal 16%nat.
            split; simpl; eauto.
            split; simpl; eauto.
        
            intros.
            destruct (_ =? _) eqn:?.
            2:{ eauto. }
            eapply Forall_app; merge_simpl; eauto.
            clean_arith; subst.
            split; eauto.
            econstructor; eauto.
            2:{ 
              split;eauto.
              rewrite HA4 in HA7 |- *.
              inversion HA7; eauto.
            }
            rewrite HA4 in HA7 .
            inversion HA7; eauto.
        }
    }
    (* Optimize Proof. *)
    {
        simpl in related_i_s.
        light_clean_propagate.
        min_straight_line.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        min_straight_line.
        repeat clean_arith.
        simpl in *|-.
        destruct (_ =? _) eqn:?.
        {
          eexists.
          split.
          {
            eapply existSR_done.
          }
          assert_related simul_implies_indistinguishable.
          {
              simpl.
              light_clean_propagate.
              post_rule_state. 
              split.
              shelve.
              split.
              simpl.
              eauto.
              split.
              wrapped_arrays_equal 3%nat.
              wrapped_arrays_equal 16%nat.
              split;simpl;eauto.
              split;simpl;eauto.
              split;simpl;eauto.
              split;simpl;eauto.
              split;simpl;eauto.
              split;simpl;eauto.
              split;simpl;eauto.
             
              pose proof do_process_streq.
              destruct mem_st0.
              specialize H with (2 := HB1).
              simpl in H.
              clean_arith.
              specialize (H Heqb).
              simpl.
              (* Stupid commutativity under binder, I should have been more
              careful when I defined my inductive *) 
              match goal with 
              | [H : mem_flushes ?a ?b ?c ?d |- mem_flushes ?a2 ?b ?c ?d] =>
              assert (a = a2) as lol
              end.
              {
                f_equal.
                eapply functional_extensionality.
                intros.
                rewrite N.eqb_sym.
                reflexivity.
              }
              rewrite <- lol.
              eauto.
          }
        }
        {
        eexists.
        split.
        {
          eapply existSR_done.
        }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            light_clean_propagate.
            change (MemoryUntagged.mem imem_i = MemoryUntagged.mem imem_s) 
              with ((fun x => MemoryUntagged.mem imem_i x) = (fun y => MemoryUntagged.mem imem_s y)) in HA2.
            change (MemoryUntagged.mem mem_st0) 
              with ((fun x => MemoryUntagged.mem mem_st0 x) ) in HB5.
            post_rule_state. 
            split.
            shelve.
            split.  simpl. eauto.
            split.
            wrapped_arrays_equal 3%nat.
            wrapped_arrays_equal 16%nat.
            split; simpl; eauto.
            split; simpl; eauto.
            split; simpl; eauto.
            split; simpl; eauto.
            split; simpl; eauto.
            split; simpl; eauto.
            split; simpl; eauto.
            pose proof do_process_ldreq.
            destruct mem_st0.
            specialize H with (2 := HB1).
            simpl in H.
            clean_arith.
            pose proof flushes_writeOrNot.
            specialize H0 with (1:= HB1).
            specialize (H0 head).
            simpl in H0.
            specialize (H0 (or_introl eq_refl)).
            destruct H0; try lia.
            specialize (H H0).
            simpl.
            eauto.
        }
      }
    } 
    {
        simpl in related_i_s.
        light_clean_propagate.
        min_straight_line.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        min_straight_line.
        repeat clean_arith.
        simpl in *|-.
        eexists.
        split.
        { eapply existSR_done.  }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            light_clean_propagate.
            post_rule_state. 
            split.
            shelve.
            split;  simpl; eauto.
            split.
            wrapped_arrays_equal 3%nat.
            rewrite HA15.
            wrapped_arrays_equal 16%nat.
            prove_outside nxt_st1; eauto.
            prove_outside nxt_st1; eauto.
            prove_outside nxt_st; eauto.
            prove_outside nxt_st; eauto.
            split; simpl; eauto.
            split; simpl; eauto.
            split; simpl; eauto.
            split; simpl; eauto.
            split; simpl; eauto.
            split; simpl; eauto.
            split; simpl; eauto.
            merge_simpl.
            simpl in *.
            subst.
            pose proof do_resp_ld.
            destruct mem_st.
            simpl in *.
            subst.
            specialize (H) with (1:= HB1).
            simpl in H.
            (* Again stupid commutativity ... *)
            match goal with 
            | [H : mem_flushes ?a ?b ?c ?d |- mem_flushes ?a ?b ?c ?d2] =>
            assert (d = d2) as lol
            end.
            {
              eapply functional_extensionality.
              intros.
              rewrite N.eqb_sym.
              reflexivity.
            }
            rewrite <- lol.
            eauto.
        }
    }
    Optimize Proof.
    (* { admit. } *)
    {
       (* emit_ndl *)
       (* Nothing to do on the original spec side !*)
        unfold lift_to in *.
        simpl in related_i_s.
        light_clean_propagate.
        min_straight_line.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        min_straight_line.
        repeat clean_arith.
        simpl in *|-.
        light_clean_propagate.
        repeat simpl_applylog.
        simpl in *|-.
        light_clean_propagate.
        eexists.
        split.
        {
          eapply existSR_done.
        }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            post_rule_state. 
            split.
            shelve.
            split; eauto.
            split; eauto.
            wrapped_arrays_equal 3%nat.
            wrapped_arrays_equal 16%nat.
            split; eauto.
            intros.
            eapply in_app_iff in H.
            destruct H.
            eauto.
            rpn In hyp.
            inversion hyp.
            subst.
            merge_simpl.
            split; eauto.
            rpn In empty.
            inversion empty.
            split; eauto.
            split; eauto.
        }
    }

    {
      (* emit_ndl *)
      (* Nothing to do on the original spec side !*)
        simpl in related_i_s.
        unfold lift_to in *.
        light_clean_propagate.
        min_straight_line.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        min_straight_line.
        repeat clean_arith.
        simpl in *|-.
        light_clean_propagate.
        repeat simpl_applylog.
        simpl in *|-.
        light_clean_propagate.

        eexists.
        split.
        {
          eapply existSR_done.
        }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            light_clean_propagate.
            post_rule_state. 
            split.
            shelve.
            split; eauto.
            split; eauto.
            wrapped_arrays_equal 3%nat.
            wrapped_arrays_equal 16%nat.
            split; simpl; eauto.
            split; simpl; eauto.
            split; simpl; eauto.
            split; simpl; eauto.
            split; simpl; eauto.
            split; simpl; eauto.
            split; simpl; eauto.
           
            pose proof do_addreq_ld.
            specialize (H) with (2:= HB1).
            specialize (H {#0 n 0}).
            simpl in H.
            merge_simpl.
            specialize (H eq_refl).
            match goal with 
            | [H : mem_flushes ?a ?b ?c ?d |- mem_flushes ?a ?b ?c ?d2] =>
            assert (d = d2) as lol
            end.
            {
              eapply functional_extensionality.
              intros.
              rewrite N.eqb_sym.
              reflexivity.
            }
            rewrite <- lol.
            eauto.
        }
    }
    (* { admit. } *)
    {
        simpl in related_i_s.
        unfold lift_to in *.
        light_clean_propagate.
        min_straight_line.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        min_straight_line.
        repeat clean_arith.
        simpl in *|-.
        light_clean_propagate.
        repeat simpl_applylog.
        simpl in *|-.
        light_clean_propagate.

        eexists.
        split.
        {
          (* DO fetch *)
          eapply existSR_substep with (instance_i := 0%nat) (r:= 0%nat).
          simpl.
          eauto.
          simpl.
          eauto.
          unfold lift_to in *.
          let y := (eexists_st_array 3%nat) in
          eexists y.
          unshelve instantiate (5:= _).
          let y := (eexists_st_array 13%nat) in
          exact y.
          split.
          eapply f_equal.
          eapply ext_array; simpl; eauto.
          eexists.
          split.
          2:{
              eexists.
              let y := (eexists_st_array 13%nat) in
              eexists y.
              do 3 eexists.
              split.
              simpl.
              eauto.
              split; eauto.
              split.
              {
                repeat (econstructor; simpl).
              }
              apply_log_fn 13%nat.
           }
          eauto.

          (* push request to memory *)
          eapply existSR_step with (r:= 0%nat).
          simpl.
          eexists. 
          let y := (eexists_st_array 3%nat) in
          eexists y.
          unshelve instantiate (5:= _).
          let y := (eexists_st_array 13%nat) in
          exact y.
          do 3 eexists.
          split.
          eapply f_equal.
          eapply ext_array; simpl; eauto.
          simpl; eauto.
          simpl; eauto.
          split.
          eauto.
          split.
          {
            repeat (econstructor; simpl).
            unshelve instantiate (1:= _).
            let y := (eexists_st_array 13%nat) in
            exact y.

            array_case_indexes i 15%nat; try lia; eauto.
            array_case_indexes x 15%nat; try lia; eauto.
            simpl; eauto.
            simpl; eauto.
            rewrite merge_split1.
            simpl.
            eauto.
          }
          apply_log_fn 3%nat.
          {
            intros.
            eexists.
            let y := (eexists_st_array 13%nat) in
            eexists y.
            do 3 eexists.
            split.
            eauto.
            split.
            eapply f_equal.
            eapply ext_array; simpl; eauto.
            repeat (econstructor; simpl).
            array_case_indexes i 15%nat; try lia; eauto.
            array_case_indexes x 15%nat; try lia; eauto.
          }
          {
            intros.
            eexists.
            split.
            eauto.
            rewrite merge_split1.
            simpl. 
            eauto.
          }

          (* Get response from memory *)
          eapply existSR_step with (r:= 1%nat).
          simpl.
          eexists. 
          let y := (eexists_st_array 3%nat) in
          eexists y.
          unshelve instantiate (5:= _).
          let y := (eexists_st_array 13%nat) in
          exact y.
          do 3 eexists.
          split.
          eapply f_equal.
          eapply ext_array; simpl; eauto.
          simpl; eauto.
          simpl; eauto.
          split.
          eauto.
          split.
          {
            repeat (econstructor; simpl).
            merge_simpl.
            rewrite HA12.
            simpl.
            eauto.
            unshelve instantiate (1:= _).
            let y := (eexists_st_array 13%nat) in
            exact y.
            array_case_indexes i 15%nat; try lia; eauto.
            array_case_indexes x 15%nat; try lia; eauto.
            simpl; eauto.
            simpl; eauto.
          }
          apply_log_fn 3%nat.
          {
            intros.
            eexists.
            let y := (eexists_st_array 13%nat) in
            eexists y.
            do 3 eexists.
            split.
            eauto.
            split.
            eapply f_equal.
            eapply ext_array; simpl; eauto.
            repeat (econstructor; simpl).
            array_case_indexes i 15%nat; try lia; eauto.
            array_case_indexes x 15%nat; try lia; eauto.
          }
          eapply existSR_done. 
        }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            post_rule_state. 
            simpl.
            split.
            shelve.
            split.
            simpl.
            wrapped_arrays_equal 3%nat.
            split.
            wrapped_arrays_equal 3%nat.

            change (MemoryUntagged.mem imem_i = MemoryUntagged.mem imem_s) 
              with ((fun x => MemoryUntagged.mem imem_i x) = (fun y => MemoryUntagged.mem imem_s y)) in HA4.
            wrapped_arrays_equal 16%nat.

            destruct (map_st n0) eqn:?.
            (* Absurd case *)
            { rewrite HB3 in HA3. merge_simpl. inversion HA3. }
            subst.
            (* rewrite H12. *)
            merge_simpl.
            change (fun x => ?a x) with a in HA4.
            (* inversion H11; clear H11; subst.  *)
            rewrite <- HA4.
            specialize (HA8 n0).
            erewrite Heql in HA8.
            inversion HA8; subst;eauto.
            split; eauto.
            split; eauto.
            split; eauto.
            split; eauto.
            split; eauto.
            split; eauto.
            simpl.
            rewrite HA12.
            simpl.
            reflexivity.
        }
    }

    (* { admit. } *)
    {
        simpl in related_i_s.
        unfold lift_to in *.
        light_clean_propagate.
        min_straight_line.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        min_straight_line.
        repeat clean_arith.
        simpl in *|-.
        light_clean_propagate.
        repeat simpl_applylog.
        simpl in *|-.
        light_clean_propagate.
       
        eexists.
        split.
        {
          eapply existSR_substep with (instance_i := 0%nat) (r:= 1%nat).
          simpl.
          eauto.
          simpl.
          eauto.
          unfold lift_to in *.
          let y := (eexists_st_array 3%nat) in
          eexists y.
          unshelve instantiate (5:= _).
          let y := (eexists_st_array 13%nat) in
          exact y.
          split.
          eapply f_equal.
          eapply ext_array; simpl; eauto.
          eexists.
          split.
          2:{
              eexists.
              let y := (eexists_st_array 13%nat) in
              eexists y.
              do 3 eexists.
              split.
              simpl.
              eauto.
              split; eauto.
              split.
              {
                repeat (econstructor; simpl).
              }
              apply_log_fn 13%nat.
           }
          eauto.
          eapply existSR_done. 
        }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            post_rule_state. 
            split.
            shelve.
            split.
            wrapped_arrays_equal 3%nat.
            split.
            wrapped_arrays_equal 3%nat.
            wrapped_arrays_equal 16%nat.
            prove_outside nxt_st; eauto.
            prove_outside nxt_st; eauto.
            split; eauto.
            split; eauto.
            split; eauto.
        }
    }
    Optimize Proof.
    (* { admit. } *)
    {
        simpl in related_i_s.
        unfold lift_to in *.
        light_clean_propagate.
        min_straight_line.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        min_straight_line.
        repeat clean_arith.
        simpl in *|-.
        light_clean_propagate.
        repeat simpl_applylog.
        simpl in *|-.
        light_clean_propagate.
      
        destruct (_ =? _) eqn:? in HB0.
        min_straight_line.
        destruct (_ =? _) eqn:? in HB0.
        {
        min_straight_line.
        simpl in *|-.
        light_clean_propagate.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        repeat clean_arith.

        eexists.
        split.
        {
          eapply existSR_substep with (instance_i := 0%nat) (r:= 2%nat).
          simpl.
          eauto.
          simpl.
          eauto.
          unfold lift_to in *.
          let y := (eexists_st_array 3%nat) in
          eexists y.
          unshelve instantiate (5:= _).
          let y := (eexists_st_array 13%nat) in
          exact y.
          split.
          eapply f_equal.
          eapply ext_array; simpl; eauto.
          eexists.
          split.
          2:{
              eexists.
              let y := (eexists_st_array 13%nat) in
              eexists y.
              do 3 eexists.
              split.
              simpl.
              eauto.
              split; eauto.
              split.
              {
                reconstruct; simpl; eauto.
              }
              apply_log_fn 13%nat.
           }
          eauto.

          eapply existSR_step with (r:= 2%nat).
          simpl.
          eexists. 
          let y := (eexists_st_array 3%nat) in
          eexists y.
          unshelve instantiate (5:= _).
          let y := (eexists_st_array 13%nat) in
          exact y.
          do 3 eexists.
          split.
          simpl; eauto.
          split; eauto.
          split; eauto.
          {
            reconstruct; eauto 6.
            split;eauto.
            eexists.
            seq_eexists_prim 13%nat.
            split;eauto.
            split;eauto.
            split;eauto.
            reconstruct.
            split;eauto.
            apply_log_fn 13%nat.
            split;eauto.
            simpl.
            merge_simpl.
            repeat (econstructor; simpl).
          }
          apply_log_fn 3%nat.
          {
            intros.
            eexists.
            let y := (eexists_st_array 13%nat) in
            eexists y.
            do 3 eexists.
            split.
            eauto.
            split.
            eapply f_equal.
            eapply ext_array; simpl; eauto.
            repeat (econstructor; simpl).
            array_case_indexes i 15%nat; try lia; eauto.
            array_case_indexes x 15%nat; try lia; eauto.
          }
          {
            intros.
            eexists.
            split.
            eauto.
            rewrite merge_split1.
            simpl. 
            eauto.
          }

          eapply existSR_done. 
        }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            post_rule_state. 
            simpl.
            split.
            shelve.
            split.
            wrapped_arrays_equal 3%nat.
            split.
            wrapped_arrays_equal 3%nat.
            wrapped_arrays_equal 16%nat.
            simpl; split; eauto.
            simpl; split; eauto.
            simpl; split; eauto.
            simpl; split; eauto.
            simpl; split; eauto.
            simpl; split; eauto.
            simpl; split; eauto.
            pose proof do_addreq_st.
            specialize H with (2:= HB1).
            merge_simpl.
            match type of HB0 with 
            | context[ _ ++ [ ?req ]] =>
            specialize (H req)
            end.
            simpl in H.
            merge_simpl.
            specialize (H eq_refl).
            match goal with 
            | [H : mem_flushes ?a ?b ?c ?d |- mem_flushes ?a ?b2 ?c ?d2] =>
            assert (d = d2 /\ b = b2) as lol
            end.
            {
              split.
              eapply functional_extensionality;
              intros;
              rewrite N.eqb_sym;
              reflexivity.
              f_equal.
              eapply functional_extensionality;
              intros.
              rewrite N.eqb_sym.
              reflexivity.
            }
            light_clean_propagate.
            rewrite <- HB3.
            rewrite <- HA.
            eauto.
        }
      }
      {
        (* It is not a store (it is a load) *)
        light_clean_propagate.
        min_straight_line.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        min_straight_line.
        repeat clean_arith.
        simpl in *|-.
        light_clean_propagate.
        eexists.
        split.
        {
          eapply existSR_substep with (instance_i := 0%nat) (r:= 2%nat).
          simpl.
          eauto.
          simpl.
          eauto.
          unfold lift_to in *.
          let y := (eexists_st_array 3%nat) in
          eexists y.
          unshelve instantiate (5:= _).
          let y := (eexists_st_array 13%nat) in
          exact y.
          split.
          eapply f_equal.
          eapply ext_array; simpl; eauto.
          eexists.
          split.
          2:{
              eexists.
              let y := (eexists_st_array 13%nat) in
              eexists y.
              do 3 eexists.
              split.
              simpl.
              eauto.
              split; eauto.
              split.
              {
                reconstruct;
                simpl in *; eauto.
                blast_arith.
              }
              apply_log_fn 13%nat.
           }
          eauto.

          eapply existSR_step with (r:= 2%nat).
          simpl.
          eexists. 
          let y := (eexists_st_array 3%nat) in
          eexists y.
          unshelve instantiate (5:= _).
          let y := (eexists_st_array 13%nat) in
          exact y.
          do 3 eexists.
          split.
          eapply f_equal.
          eapply ext_array; simpl; eauto.
          simpl; eauto.
          simpl; eauto.
          split.
          eauto.
          split.
          {
            reconstruct; simpl; eauto 6.
            simpl; eauto.
            split; eauto.
            eexists.
            seq_eexists_prim 13%nat.
            split; eauto.
            split; eauto.
            split; eauto.
            reconstruct; simpl; eauto.
            apply_log_fn 16%nat.
            split; eauto.
            rewrite merge_split1.
            simpl.
            eauto.
          }
          apply_log_fn 3%nat.
          {
            intros.
            eexists.
            let y := (eexists_st_array 13%nat) in
            eexists y.
            do 3 eexists.
            split.
            eauto.
            split.
            eapply f_equal.
            eapply ext_array; simpl; eauto.
            repeat (econstructor; simpl).
            array_case_indexes i 15%nat; try lia; eauto.
            array_case_indexes x 15%nat; try lia; eauto.
          }
          {
            intros.
            eexists.
            split.
            eauto.
            rewrite merge_split1.
            simpl. 
            eauto.
          }

          (* It is a store so no response returns! *)
        (*Get response from memory*)
          eapply existSR_step with (r:= 3%nat).
          simpl.
          eexists. 
          let y := (eexists_st_array 3%nat) in
          eexists y.
          unshelve instantiate (5:= _).
          let y := (eexists_st_array 13%nat) in
          exact y.
          do 3 eexists.
          split.
          eapply f_equal.
          eapply ext_array; simpl; eauto.
          simpl; eauto.
          simpl; eauto.
          split.
          eauto.
          split.
          {
            reconstruct; simpl; eauto.
            merge_simpl.
            rewrite HA13.
            simpl.
            eauto.
            split; simpl; eauto.
            eexists.
            seq_eexists_prim 13%nat.
            split; eauto.
            split; eauto.
            split; eauto.
            reconstruct.
            split; eauto.
            apply_log_fn 16%nat.
          }
          apply_log_fn 3%nat.
          {
            intros.
            eexists.
            let y := (eexists_st_array 13%nat) in
            eexists y.
            do 3 eexists.
            split.
            eauto.
            split.
            eapply f_equal.
            eapply ext_array; simpl; eauto.
            repeat (econstructor; simpl).
            array_case_indexes i 15%nat; try lia; eauto.
            array_case_indexes x 15%nat; try lia; eauto.
          } 
          eapply existSR_done. 
        }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            light_clean_propagate.
            destruct (res _) eqn:?.
            light_clean_propagate; merge_simpl.
            inversion HA2.
            rewrite HB3 in HA2; merge_simpl; inversion HA2.
            light_clean_propagate.
            merge_simpl.
            light_clean_propagate.
            post_rule_state.
            inversion HA2.
            simpl.
            split.
            shelve.

            pose proof  flushes_readdlb.
            print_arrays.
            specialize H with (1:= HB1).
            (* inversion HA2. *)
            match type of Heql with 
            | res (map_st ?a) = n::_ => 
              specialize (H a n)
            end.
            rewrite Heql in H.
            simpl in H.
            specialize (H (or_introl eq_refl)).
            subst.
            split; eauto.
            split; eauto.
            wrapped_arrays_equal 3%nat.
            wrapped_arrays_equal 15%nat.
            prove_outside nxt_st;
            destruct x; eauto.
            split; eauto.
            split; eauto.
            split; eauto.
            split; eauto.
            split; eauto.
            split; eauto.
            split; eauto.
            simpl.
            rewrite HA13.
            reflexivity.

            rewrite HA13.
            simpl.
            rewrite <- HA13.
            destruct dmem_s.
            simpl in *.
            eauto. 
        }
      }
      min_straight_line.
      destruct (_ =? _) eqn:? in HB.
      {
        min_straight_line.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        min_straight_line.
        repeat clean_arith.
        simpl in *|-.
        light_clean_propagate.
        eexists.
        split.
        {
          eapply existSR_substep with (instance_i := 0%nat) (r:= 2%nat).
          simpl.
          eauto.
          simpl.
          eauto.
          unfold lift_to in *.
          let y := (eexists_st_array 3%nat) in
          eexists y.
          unshelve instantiate (5:= _).
          let y := (eexists_st_array 13%nat) in
          exact y.
          split.
          eapply f_equal.
          eapply ext_array; simpl; eauto.
          eexists.
          split.
          2:{
              eexists.
              let y := (eexists_st_array 13%nat) in
              eexists y.
              do 3 eexists.
              split.
              simpl.
              eauto.
              split; eauto.
              split.
              {
                reconstruct; simpl; eauto.
                blast_arith.
              }
              apply_log_fn 13%nat.
           }
          eauto.

          eapply existSR_done. 
        }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            post_rule_state. 
            simpl.
            split.
            shelve.
            split.
            wrapped_arrays_equal 3%nat.
            split.
            wrapped_arrays_equal 3%nat.
            wrapped_arrays_equal 16%nat.
            split; eauto.
            split; eauto.
            split; eauto.
        }
      }
      {
        min_straight_line.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        repeat clean_arith.
        simpl in *|-.
        eexists.
        split.
        {
          eapply existSR_substep with (instance_i := 0%nat) (r:= 2%nat).
          simpl.
          eauto.
          simpl.
          eauto.
          unfold lift_to in *.
          let y := (eexists_st_array 3%nat) in
          eexists y.
          unshelve instantiate (5:= _).
          let y := (eexists_st_array 13%nat) in
          exact y.
          split.
          eapply f_equal.
          eapply ext_array; simpl; eauto.
          eexists.
          split.
          2:{
            seq_eexists_prim 13%nat.
            split;simpl;eauto.
            split;simpl;eauto.
            split;simpl;eauto.
            reconstruct; simpl; eauto; blast_arith.
            simpl.
            apply_log_fn 13%nat.
           }
          eauto.
          eapply existSR_done. 
        }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            post_rule_state. 
            simpl.
            split.
            shelve.
            split.
            wrapped_arrays_equal 3%nat.
            split.
            wrapped_arrays_equal 3%nat.
            wrapped_arrays_equal 16%nat.
            split; eauto.
            split; eauto.
            split; eauto.
        }
      }
    }
    {
        simpl in related_i_s.
        unfold lift_to in *.
        light_clean_propagate.
        min_straight_line.
        destruct (_ =? _) eqn:? in HB2.
        destruct (_ =? _) eqn:? in HB0.
        {
        min_straight_line.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        Time straight_line.
        light_clean_propagate.
        simpl in *|-.
        light_clean_propagate.
        repeat simpl_applylog.
        repeat clean_arith.
        merge_simpl.
        eexists.
        split.
        {
          eapply existSR_substep with (instance_i := 0%nat) (r:= 3%nat).
          simpl.
          eauto.
          simpl.
          eauto.
          unfold lift_to in *.
          let y := (eexists_st_array 3%nat) in
          eexists y.
          unshelve instantiate (5:= _).
          let y := (eexists_st_array 13%nat) in
          exact y.
          split; simpl; eauto.
        
          eexists.
          split.
          eauto.
          seq_eexists_prim 13%nat.
          split; eauto.
          split; eauto.
          split; eauto.
          reconstruct; simpl; eauto; try blast_arith; subst; eauto.
          apply_log_fn 13%nat.
          eapply existSR_done. 
        }
        assert_related simul_implies_indistinguishable.
        {
            post_rule_state. 
            simpl.
            split.
            shelve.
            split.
            wrapped_arrays_equal 3%nat.
            merge_simpl.
            split.
            wrapped_arrays_equal 3%nat.
            wrapped_arrays_equal 16%nat.
            split; eauto.
            split; eauto.
            split; eauto.
        }
        }
        {
        min_straight_line.
        simpl in *|-.
        light_clean_propagate.
        simpl in *|-.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        repeat clean_arith.
        eexists.
        split.
        {
          eapply existSR_substep with (instance_i := 0%nat) (r:= 3%nat).
          simpl.
          eauto.
          simpl.
          eauto.
          unfold lift_to in *.
          let y := (eexists_st_array 3%nat) in
          eexists y.
          unshelve instantiate (5:= _).
          let y := (eexists_st_array 13%nat) in
          exact y.
          split.
          eapply f_equal.
          eapply ext_array; simpl; eauto.
          eexists.
          split.
          2:{
              eexists.
              let y := (eexists_st_array 13%nat) in
              eexists y.
              do 3 eexists.
              split.
              simpl.
              eauto.
              split; eauto.
              split.
              {
                reconstruct; simpl; eauto; subst; eauto; blast_arith.
              }
              apply_log_fn 13%nat.
           }
          eauto.
          eapply existSR_done. 
        }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            post_rule_state. 
            simpl.
            split.
            shelve.
            split.
            wrapped_arrays_equal 3%nat.
            split.
            wrapped_arrays_equal 3%nat.
            wrapped_arrays_equal 16%nat.
            split; eauto.
            split; eauto.
            split; eauto.
        }
        }
        destruct (_ =? _) eqn:? in HB0.
        {
        min_straight_line.
        destruct (_ =? _) eqn:? in HB0.
        {
        min_straight_line.
        light_clean_propagate.
        simpl in *|-.
        (* The apply_alog are guards. *)
        light_clean_propagate.
        simpl in *|-.
        light_clean_propagate.
        repeat simpl_applylog.
        repeat clean_arith.
        eexists.
        split.
        {
          eapply existSR_substep with (instance_i := 0%nat) (r:= 3%nat).
          simpl.
          eauto.
          simpl.
          eauto.
          unfold lift_to in *.
          let y := (eexists_st_array 3%nat) in
          eexists y.
          unshelve instantiate (5:= _).
          let y := (eexists_st_array 13%nat) in
          exact y.
          split.
          eapply f_equal.
          eapply ext_array; simpl; eauto.
          eexists.
          split.
          2:{
              eexists.
              let y := (eexists_st_array 13%nat) in
              eexists y.
              do 3 eexists.
              split.
              simpl.
              eauto.
              split; eauto.
              split.
              {
                reconstruct; simpl; eauto; subst; try blast_arith; eauto.
                split; simpl; eauto.
              }
              apply_log_fn 13%nat.
           }
          eauto.
          eapply existSR_done. 
        }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            post_rule_state. 
            simpl.
            split.
            shelve.
            split.
            wrapped_arrays_equal 3%nat.
            split.
            wrapped_arrays_equal 3%nat.
            wrapped_arrays_equal 16%nat.
            split; eauto.
            split; eauto.
            split; eauto.
            (* Issue to check here *)
        }
        }
        {
        min_straight_line.
        simpl in * |-.
        light_clean_propagate.
        simpl in * |-.
        light_clean_propagate.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        repeat clean_arith.
        eexists.
        split.
        {
          eapply existSR_substep with (instance_i := 0%nat) (r:= 3%nat).
          simpl.
          eauto.
          simpl.
          eauto.
          unfold lift_to in *.
          let y := (eexists_st_array 3%nat) in
          eexists y.
          unshelve instantiate (5:= _).
          let y := (eexists_st_array 13%nat) in
          exact y.
          split.
          eapply f_equal.
          eapply ext_array; simpl; eauto.
          eexists.
          split.
          2:{
              eexists.
              let y := (eexists_st_array 13%nat) in
              eexists y.
              do 3 eexists.
              split.
              simpl.
              eauto.
              split; eauto.
              split.
              {
                reconstruct; simpl; subst; eauto; blast_arith.
              }
              apply_log_fn 13%nat.
           }
          eauto.
          eapply existSR_done. 
        }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            post_rule_state. 
            simpl.  split.  shelve.
            split.
            wrapped_arrays_equal 3%nat.
            split.
            wrapped_arrays_equal 3%nat.
            wrapped_arrays_equal 16%nat.
            split; eauto.
            split; eauto.
            split; eauto.
        }
        }
        }
        {
        min_straight_line.
        destruct (_ =? _) eqn:? in HB0.
        {
        min_straight_line.
        simpl in *|-.
        light_clean_propagate.
        simpl in *|-.
        light_clean_propagate.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        repeat clean_arith.
        light_clean_propagate.
        eexists.
        split.
        {
          eapply existSR_substep with (instance_i := 0%nat) (r:= 3%nat).
          simpl.
          eauto.
          simpl.
          eauto.
          unfold lift_to in *.
          let y := (eexists_st_array 3%nat) in
          eexists y.
          unshelve instantiate (5:= _).
          let y := (eexists_st_array 13%nat) in
          exact y.
          split.
          eapply f_equal.
          eapply ext_array; simpl; eauto.
          eexists.
          split.
          2:{
              eexists.
              let y := (eexists_st_array 13%nat) in
              eexists y.
              do 3 eexists.
              split.
              simpl.
              eauto.
              split; eauto.
              split.
              reconstruct; simpl; subst; eauto 6; try blast_arith.
              apply_log_fn 13%nat.
           }
          eauto.
          eapply existSR_done. 
        }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            post_rule_state. 
            simpl.
            split.
            shelve.
            split.
            wrapped_arrays_equal 3%nat.
            split.
            wrapped_arrays_equal 3%nat.
            wrapped_arrays_equal 16%nat.
            split; eauto.
            split; eauto.
            split; eauto.
            (* Issue to check here *)
        }
        }
        {
        min_straight_line.
        simpl in * |-.
        light_clean_propagate.
        simpl in * |-.
        light_clean_propagate.
        (* The apply_alog are guards. *)
        repeat simpl_applylog.
        repeat clean_arith.
        light_clean_propagate.
        eexists.
        split.
        {
          eapply existSR_substep with (instance_i := 0%nat) (r:= 3%nat).
          simpl.
          eauto.
          simpl.
          eauto.
          unfold lift_to in *.
          let y := (eexists_st_array 3%nat) in
          eexists y.
          unshelve instantiate (5:= _).
          let y := (eexists_st_array 13%nat) in
          exact y.
          split.
          eapply f_equal.
          eapply ext_array; simpl; eauto.
          eexists.
          split.
          2:{
              eexists.
              let y := (eexists_st_array 13%nat) in
              eexists y.
              do 3 eexists.
              split.
              simpl.
              eauto.
              split; eauto.
              split. 
              reconstruct; simpl; subst; eauto 6; try blast_arith.
              apply_log_fn 13%nat.
           }
          eauto.
          eapply existSR_done. 
        }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            post_rule_state. 
            simpl.
            split.
            shelve.
            split.
            wrapped_arrays_equal 3%nat.
            split.
            wrapped_arrays_equal 3%nat.
            wrapped_arrays_equal 16%nat.
            split; eauto.
            split; eauto.
            split; eauto.
        }
        }
    }
    }
    {
        simpl in related_i_s.
        unfold lift_to in *.
        light_clean_propagate.
        simpl in *|-.
        light_clean_propagate.
        simpl in *|-.
        light_clean_propagate.
        eexists.
        split.
        {
          eapply existSR_done.
        }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            post_rule_state. 
            simpl.
            split.
            shelve.
            split.
            wrapped_arrays_equal 3%nat.
            split.
            wrapped_arrays_equal 3%nat.
            wrapped_arrays_equal 16%nat.
            split; eauto.
            split; eauto.
            2:{ split; eauto. }

            intros.
            destruct ( _ =? _) eqn:?.
            2:{
              clean_arith.
              light_clean_propagate.
              specialize (HA8 addr).
              eauto.
            }
            {
              clean_arith.
              light_clean_propagate.
              specialize (HA8 addr_killed).
              destruct (map_st addr_killed); simpl; eauto.
              inversion HA8; eauto.
            }
        }
    }
    {
        simpl in related_i_s.
        unfold lift_to in *.
        light_clean_propagate.
        simpl in *|-.
        light_clean_propagate.
        simpl in *|-.
        light_clean_propagate.
        eexists.
        split.  { eapply existSR_done.  }
        assert_related simul_implies_indistinguishable.
        {
            simpl.
            post_rule_state. 
            simpl.
            split.
            shelve.
            split.
            wrapped_arrays_equal 3%nat.
            split.
            wrapped_arrays_equal 3%nat.
            wrapped_arrays_equal 16%nat.
            split; eauto.
            split; eauto.
            split; eauto.
            split; eauto.
            split; eauto.
            split; eauto.
            split; eauto.
            pose proof do_invalidate.
            specialize (H) with (1:= HB1).
            specialize (H addr_killed).
            match goal with 
            | [H : mem_flushes ?a ?b ?c ?d |- mem_flushes ?a ?b ?c ?d2] =>
            assert (d = d2) as lol
            end.
            {
              eapply functional_extensionality.
              intros.
              rewrite N.eqb_sym.
              simpl.
              light_clean_propagate.
              simpl in *.
              light_clean_propagate.
              destruct (_ =? _) eqn:?; clean_arith; subst.
              reflexivity.
              reflexivity.
            }
            rewrite <- lol.
            eauto.
        }
    }
    Unshelve.
    all: eauto.
    Time Qed.
    
  End Correctness.