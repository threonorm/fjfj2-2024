Require Import Lia.
Require Import String.
Require Import NArith.

Require ZArith.

Require Import LangFjfj2.
Require Import Indexification.
Require Import FjfjParsing.
Require Import Ltac2.Ltac2.
Require Import List.
Import ListNotations.
Require Import SopProp.

Local Set Universe Polymorphism.
Unset Universe Minimization ToSet.
(* TODO Investigate why hypothesis get duplicated in the flow *)

Set Default Proof Mode "Classic".
Require reg. 
Require Import Rf.
Require Import BaseTactics.

Context {uninterp : Uninterpreted_Functions}.
Open Scope N.
 

Section RFCorrect.
  Context (idx_wf : forall x,  sem_uninterp "unpack_idx" x < 32).

  Ltac idx_t := match goal with 
            | [H : sem_uninterp "unpack_idx" _ = _ |- _] =>
              rewrite H in *
            end.

  Ltac get_setalog := repeat match goal with 
              | [ H : _ |- _] => rewrite get_setalog_neq in H; [|solve [eauto]]
              end.
  Lemma get_setalog_eq : forall l x y z , (setalog l x y z) x = Some (y,z). 
    intros.
    unfold setalog.
    destruct (PeanoNat.Nat.eqb _ _) eqn:?.
    eauto.
    eapply EqNat.beq_nat_false in Heqb.
    congruence.
  Qed.

  Lemma yo: forall (A B C:Prop), (A -> B/\C) <-> (A -> B) /\ (A -> C).
  intros.
  split.
  intro; firstorder.
  intro; firstorder.
  Qed.
  Ltac flatten := repeat match goal with 
          | [H : context[?a -> ?b /\ ?c] |- _] => 
          idtac H b c;
            rewrite yo in H; decompose' H
          end.
  Ltac prune_path := repeat match goal with 
  | [H : context[_ == ?a] |- _ ] =>
    match type of H with 
    | context[_ == ?b] => 
      assert_fails(constr_eq a b);
      idtac a b;
      clear H
    end
  end.

Ltac reduce_carefully_fjfj := 
 match goal with 
| [H : context[wpa ?st ?called_args ?axiom ?binders ?alog ?vlog ?action ?p] |- _] =>
idtac H;
  simplify_branch' H; flatten; prune_path
| [H : context[wp ?st ?called_args ?axiom ?binders  ?vlog ?action ?p] |- _] =>
  simplify_branch' H; flatten; prune_path
end.

Ltac create_context_aux step_implem c f :=
  let a := fresh "SimplifiedProp" in 
  evar (a : Prop);
  let newterm := context c[a] in 
  eassert newterm as f;[subst a|]; try subst a.

Ltac open_branch' step_implem f := 
  match type of step_implem with
  | context c[wpa ?st ?called_args ?axiom ?binders ?alog ?vlog ?action ?p] =>
  create_context_aux step_implem c f
  | context c[wp ?st ?called_args ?axiom ?binders  ?vlog ?action ?p] =>
  create_context_aux step_implem c f
  end.
  Lemma onestepwrite_rf_symb' :
    forall called_args st B A i b j post,
        i < 32 ->
        A (rf i) = None ->
        B 1%nat = j ->
        j <> i ->
 wpa st called_args module_axiom B A empty_Vlog
            (Seq (onestepwrite i) b)
            post ->
        wpa st called_args module_axiom B A empty_Vlog b post 
    .
    pose proof amjoin as aj.
    pose proof vmweakening as vw.
    pose proof vmjoin as vj.
    pose proof amweakening as aw.
    intros.
    prim_invert H3.
    prim_invert H3.
    prim_invert H3.
    prim_invert H3.
    prim_invert H3.
    cbn in H3.
    rewrite H1 in H3.
    clean_arith.
    destruct H3.
    auto_specialize.
    prim_invert H4.
    eapply H4.
    all: eauto.
  Qed.
  Lemma onestepwrite_rf_symb_base :
    forall called_args st B A i j post,
        i < 32 ->
        A (rf i) = None ->
        B 1%nat = j ->
        j <> i ->
 wpa st called_args module_axiom B A empty_Vlog
            ((onestepwrite i))
            post ->
        wpa st called_args module_axiom B A empty_Vlog (Skip) post 
    .
    pose proof amjoin as aj.
    pose proof vmweakening as vw.
    pose proof vmjoin as vj.
    pose proof amweakening as aw.
    intros.
    prim_invert H3.
    prim_invert H3.
    prim_invert H3.
    prim_invert H3.
    cbn in H3.
    rewrite H1 in H3.
    clean_arith.
    destruct H3.
    auto_specialize.
    eapply H4.
    all: eauto.
  Qed.
  Lemma onestepwrite_rf_symb_eq :
      forall called_args st B A i b j post,
          i < 32 ->
          A (rf i) = None ->
          B 1%nat = j ->
          j <> i ->
   wpa st called_args module_axiom B A empty_Vlog
            (Seq (onestepwrite i) b)
            post <->
        wpa st called_args module_axiom B A empty_Vlog b post 
    .
    intros; split.
    eapply onestepwrite_rf_symb'; eauto.
    eapply onestepwrite_rf_symb; eauto.
  Qed.
 
  Lemma impl_correct : 
    refines rf_impl spec_rf
       (fun impl_st spec_st => 
         exists (l: array SModule) (fn : N -> N),
         impl_st = {| T:= _ ; state := l |} /\
         spec_st = {| T:= _ ; state := fn |} /\
         alength l = 32%nat /\
         (forall (i:nat), (i < 32)%nat ->  
              exists vreg, 
                aget l i  = {| T := _ ; state := vreg |} /\
                fn (N.of_nat i) = vreg)).
      pose proof amjoin as aj.
      pose proof vmweakening as vw.
      pose proof vmjoin as vj.
      pose proof amweakening as aw.
      unfold refines.
      intros.
      cleanup.
      split.
      {
        unfold apply_alog in *.
        intros.
        destruct method_id.
        {
          cbn in H3.
          cbn.
          cleanup.
          eapply wpa_direct in H5.
          cleanup.
          pose proof idx_wf as idx_wf'.
          specialize (idx_wf arg).
          pose proof (projT2 (write_rf_symb_compact arg x1 idx_wf)).
          cbn beta in H11.
          join H12 H5.

          assert (forall i, (i<32)%nat -> aget module_axiom i = reg.spec_reg) as specmod.
          {
             do 32 (try destruct i); cbn in *; intros; eauto.
             lia.
          }
          assert (forall i, (i<32)%nat -> exists vreg, aget x6 i = {| T:=N; state := vreg|}) as newexists.
          {
            intros.
            eapply Forall_forall with (x := i) in H9.
            destruct H9.
            destruct (x4 i).
            {
              auto_specialize.
              destruct p.
              specialize (H9 _ _ eq_refl).
              replace (aget module_axiom i) with reg.spec_reg in H9.
              destruct n.
              cbn in H9.
              unfold reg.write_method' in H9.
              eexists; eauto.
              cbn in H9.
              contradiction H9.
            }
            {
              repeat auto_specialize.
              cleanup.
              eexists.
              rewrite <- H12.
              subst.
              inverseS H4.
              cbn in H4.
              subst.
              eauto.
            }
            rewrite H7.
            rewrite in_seq.
            subst.
            inverseS H4.
            cbn in H4.
            subst.
            lia.
          }
          eapply wpa_direct in H13.
          Ltac ds := repeat match goal with 
          | [ H: _ /\ _ |- _] => destruct H 
          | [ H: exists _, _|- _] => destruct H 
          end.
          ds.
          clear H5.
          subst.
          inverseS H4.
          cbn in H4.
          subst.
          all: try first [eapply amweakening |eapply vmweakening | eapply amdirect | eapply vmdirect].
          cleanup.
          subst.

          eexists.
          split;[repeat eexists|econstructor].
          split.
          repeat eexists; try congruence.
          eapply Forall_forall with (x:= i) in H9.
          unfold setalog in H9.
          destruct (N.eq_dec _ _) as [e | n].
          {
            rewrite e in H9;
            rewrite Nat2N.id in H9;
            rewrite <- EqNat.beq_nat_refl in H9;
            cleanup;
            repeat auto_specialize;
            rewrite specmod in H1;
            cbn in H1;
            cleanup;
            unfold reg.write_method' in H1;
            rewrite H1; eauto.
          }
          {
            n_to_nat;
            eapply PeanoNat.Nat.eqb_neq in n;
            rewrite n in *;
            repeat auto_specialize;
            cleanup;
            repeat auto_specialize;
            congruence.
          }
          rewrite in_seq.
          lia.
          split.
          intros.
          pose proof (projT2 (read_rf_symb_compact arg0 _ (idx_wf' arg0) newexists)).
          cbn beta in H1.
          destruct method_id.
          {
            cbn.
            unfold read_method'.
            repeat eexists.
            cbn.
            pose proof wp_join as join. 
            specialize (join) with (1:= vmjoin) (2:= vmweakening) (3:=H1).
            cbn in H.
            cleanup.
            cbn in H.
            inverseS H.
            cbn in H.
            subst.
            specialize (join) with (1:= H4).
            clear H4 H1.
            eapply wp_direct in join.
            cleanup.
            clear H.
            subst.
            destruct (N.eq_dec _ _).
            {
              rewrite e in *.
              eapply Forall_forall with (x := N.to_nat (sem_uninterp "unpack_idx" arg0)) in H9.
              unfold setalog in H9.
              rewrite <- EqNat.beq_nat_refl in H9.
              cleanup.
              repeat auto_specialize.
              rewrite specmod in H.
              cbn in H.
              unfold reg.write_method' in H.
              rewrite H in H6.
              inverseS H6.
              cbn in H6; subst; eauto.
              lia.
              erewrite in_seq.
              lia.
            }
            {
              assert (N.to_nat (sem_uninterp "unpack_idx" arg0) < 32)%nat by lia.
              repeat auto_specialize.
              eapply Forall_forall with (x := N.to_nat (sem_uninterp "unpack_idx" arg0)) in H9.
              unfold setalog in H9.
              eapply lift_inequality in n. 
              eapply PeanoNat.Nat.eqb_neq in n.
              rewrite n in H9.
              cleanup.
              repeat auto_specialize;
              cleanup.
              rewrite <- H9 in H6.
              rewrite H3 in H6.
              inverseS H6.
              cbn in H6.
              subst.
              rewrite N2Nat.id in H4.
              eauto.
              rewrite in_seq.
              lia.
            }
            all: try first [eapply amweakening |eapply vmweakening | eapply amdirect | eapply vmdirect].
          }
          contradiction H.
          intros.
          destruct method_id.
          {
            cbn in H.
            unfold apply_alog in *.
            cleanup.
            pose proof (projT2 (write_rf_symb_compact arg0 x (idx_wf' arg0))).
            cbn beta in H4.
            join H1 H4.
            eapply wpa_direct in H5.
            cleanup.
            subst.
            unfold write_method'.
            repeat eexists.
            eauto.
            all: try first [eapply amweakening |eapply vmweakening | eapply amdirect | eapply vmdirect].
          }
          {
            contradiction H.
          }
        }
        {
          contradiction H4.
        }
      }
      split.
      {
        intros.
        destruct r; cbn in *; cbv in H4; cleanup; contradiction H4.
      }
      {
        destruct r; cbn in *;
        do 33 (try destruct sm); cbn in *; intros.
        all: try (cbv in H4;
                  cleanup;
                  easy).
      }
      Qed.

End RFCorrect.


(* Alternative nicer version? WIP 

 Lemma impl_correct : 
    refines rf_impl spec_rf
       (fun impl_st spec_st => 
         exists (l: array SModule) (fn : N -> N),
         impl_st = {| T:= _ ; state := l |} /\
         spec_st = {| T:= _ ; state := fn |} /\
         alength l = 32%nat /\
         (forall (i:nat), (i < 32)%nat ->  
              exists vreg, 
                aget l i  = {| T := _ ; state := vreg |} /\
                fn (N.of_nat i) = vreg)).
      pose proof amjoin as aj.
      pose proof vmweakening as vw.
      pose proof vmjoin as vj.
      pose proof amweakening as aw.
      prove_refinement.
      {
        clear indistinguishable_i_s.
        case_methods.
        {
            (* We do an enqueue in the implementation *)
            connect_impl_spec step_implem related_i_s init_i.
            
            repeat saturate.
            set write_rf in step_implem.
            unfold write_rf in *.
            repeat match goal with 
            | [ H := Seq ?a _ |- _] =>
            assert_fails(is_var a);
            set a in H
            | [ H := Seq _ ?a |- _] =>
            assert_fails(is_var a);
            set a in H
            end.

            Ltac t' step_impleml := 
              let old := fresh step_impleml in
              rename step_impleml into old;
              open_branch' old step_impleml;
              [ repeat (seq_specialize old);
              first [ eapply onestepwrite_rf_symb' with (5:= old) | 
                      eapply onestepwrite_rf_symb_base with  (5:= old)]; eauto; cbn; lia|clear old]. 
            Ltac r H := 
              simplify_branch' H; flatten; prune_path.

            Ltac handle_one_case step_impleml what_happened_step_implem :=
              r step_impleml;
              goto_n step_impleml;
              repeat (t' step_impleml);
              r step_impleml;
            repeat match goal with 
              | [H :context[ _ = None] |- _] => clear H 
              | [H :context[ what_happened_step_implem = setalog _ _ _ _] |- _] => clear H 
            end.
            Ltac s what_happened_step_implem :=
              reduce_carefully_fjfj;
              match goal with 
              | [ step_impleml : context[ _ == _] |- _ ] =>
                handle_one_case step_impleml what_happened_step_implem
              end.

            Time s what_happened_step_implem.
            Time assert (sem_uninterp "unpack_idx" arg_method = 0 \/ sem_uninterp "unpack_idx" arg_method <> 0) by lia. 
            destruct H.
            clear step_implem.
            repeat match goal with 
            | [ H := _ |- _] => clear H
            end.

            Time auto_specialize.

            unfold apply_alog in *.
            cleanup.
            rename x into new_st.
            eexists.
            repeat eexists.
            econstructor.
            split.
            repeat eexists; eauto.
            lia.
            repeat saturate.
            eq_commit_actions i.
            cleanup.
            repeat saturate.
            unfold setalog in *.
            rewrite H.
            rewrite <- H3; eauto.
            rewrite H6.

            repeat saturate.
            subst.
            2:{
              cbn.

            }
            
            exists (generic_embed (Some arg_method)).
            split; eauto.

            (* We don't need to do any rule on the side of the spec *)
            econstructor.
            split.
            eexists 1, arg_method, (Some arg_method).
            repeat split; try intuition congruence.
            equality_hold new_st.
            finish x H5.
  
            split.
            eq_commit_actions 0%nat.
            eq_commit_actions 1%nat.
            eq_commit_actions 2%nat.
            repeat saturate.
            (* Show Ltac Profile.
            Unset Ltac Profiling.   *)



            Time reduce_carefully_fjfj.
            clear step_implemll.
            Time reduce_carefully_fjfj.

simplify_branch' step_impleml0.
            flatten.
            clear step_impleml0l.
            goto_n step_impleml0.
            repeat (t step_impleml0).

            Time reduce_carefully_fjfj.
            T
            rename step_impleml into case0.
              rename step_impleml0 into step_impleml.
             let old := fresh step_impleml in
              rename step_impleml into old;
             let step_impleml := fresh step_impleml in 
              open_branch' old step_impleml;
              [repeat (seq_specialize old)
              (* first [ eapply onestepwrite_rf_symb' with (5:= old) | 
                      eapply onestepwrite_rf_symb_base with  (5:= old)] *)
              |].
eapply onestepwrite_rf_symb' with (5:= step_impleml0).
            first [  | 
                      eapply onestepwrite_rf_symb_base with  (5:= old)]

              [ repeat (seq_specialize old);
              first [ eapply onestepwrite_rf_symb' with (5:= old) | 
                      eapply onestepwrite_rf_symb_base with  (5:= old)]; eauto; cbn; lia|clear old]. 
              goto_n step_impleml.
              repeat (t step_impleml)
               (t step_impleml0).


            Time reduce_carefully_fjfj.
            Time reduce_carefully_fjfj.
            Time reduce_carefully_fjfj.
            Time reduce_carefully_fjfj.
            Time simplify_branch' step_implem.
            rewrite  yo in step_implem.
            decompose' step_implem.
            reduce_carefully_fjfj.
          

            Time simplify_branch' step_implem.
            flatten.
            prune_path.
            (* reduce_carefully_fjfj. *)
            Time simplify_branch' step_impleml.
            flatten.
            Time simplify_branch' step_impleml.
            Time simplify_branch' step_impleml.
            flatten; prune_path.

            eapply yo in step_impleml.
            cleanup.
            eapply yo in H0.
            cleanup.
            clear H0.
            match goal with 
            | [H :   |- _] => 
    
          cbn in H3.
          cbn.
          cleanup.
          eapply wpa_direct in H5.
          cleanup.
          pose proof idx_wf as idx_wf'.
          specialize (idx_wf arg).
          pose proof (projT2 (write_rf_symb_compact arg x1 idx_wf)).
          cbn beta in H11.
          join H12 H5.

          assert (forall i, (i<32)%nat -> aget module_axiom i = reg.spec_reg) as specmod.
          {
             do 32 (try destruct i); cbn in *; intros; eauto.
             lia.
          }
          assert (forall i, (i<32)%nat -> exists vreg, aget x6 i = {| T:=N; state := vreg|}) as newexists.
          {
            intros.
            eapply Forall_forall with (x := i) in H9.
            destruct H9.
            destruct (x4 i).
            {
              auto_specialize.
              destruct p.
              specialize (H9 _ _ eq_refl).
              replace (aget module_axiom i) with reg.spec_reg in H9.
              destruct n.
              cbn in H9.
              unfold reg.write_method' in H9.
              eexists; eauto.
              cbn in H9.
              contradiction H9.
            }
            {
              repeat auto_specialize.
              cleanup.
              eexists.
              rewrite <- H12.
              subst.
              inverseS H4.
              cbn in H4.
              subst.
              eauto.
            }
            rewrite H7.
            rewrite in_seq.
            subst.
            inverseS H4.
            cbn in H4.
            subst.
            lia.
          }
          eapply wpa_direct in H13.
          Ltac ds := repeat match goal with 
          | [ H: _ /\ _ |- _] => destruct H 
          | [ H: exists _, _|- _] => destruct H 
          end.
          ds.
          clear H5.
          subst.
          inverseS H4.
          cbn in H4.
          subst.
          all: try first [eapply amweakening |eapply vmweakening | eapply amdirect | eapply vmdirect].
          cleanup.
          subst.

          eexists.
          split;[repeat eexists|econstructor].
          split.
          repeat eexists; try congruence.
          eapply Forall_forall with (x:= i) in H9.
          unfold setalog in H9.
          destruct (N.eq_dec _ _) as [e | n].
          {
            rewrite e in H9;
            rewrite Nat2N.id in H9;
            rewrite <- EqNat.beq_nat_refl in H9;
            cleanup;
            repeat auto_specialize;
            rewrite specmod in H1;
            cbn in H1;
            cleanup;
            unfold reg.write_method' in H1;
            rewrite H1; eauto.
          }
          {
            n_to_nat;
            eapply PeanoNat.Nat.eqb_neq in n;
            rewrite n in *;
            repeat auto_specialize;
            cleanup;
            repeat auto_specialize;
            congruence.
          }
          rewrite in_seq.
          lia.
          split.
          intros.
          pose proof (projT2 (read_rf_symb_compact arg0 _ (idx_wf' arg0) newexists)).
          cbn beta in H1.
          destruct method_id.
          {
            cbn.
            unfold read_method'.
            repeat eexists.
            cbn.
            pose proof wp_join as join. 
            specialize (join) with (1:= vmjoin) (2:= vmweakening) (3:=H1).
            cbn in H.
            cleanup.
            cbn in H.
            inverseS H.
            cbn in H.
            subst.
            specialize (join) with (1:= H4).
            clear H4 H1.
            eapply wp_direct in join.
            cleanup.
            clear H.
            subst.
            destruct (N.eq_dec _ _).
            {
              rewrite e in *.
              eapply Forall_forall with (x := N.to_nat (sem_uninterp "unpack_idx" arg0)) in H9.
              unfold setalog in H9.
              rewrite <- EqNat.beq_nat_refl in H9.
              cleanup.
              repeat auto_specialize.
              rewrite specmod in H.
              cbn in H.
              unfold reg.write_method' in H.
              rewrite H in H6.
              inverseS H6.
              cbn in H6; subst; eauto.
              lia.
              erewrite in_seq.
              lia.
            }
            {
              assert (N.to_nat (sem_uninterp "unpack_idx" arg0) < 32)%nat by lia.
              repeat auto_specialize.
              eapply Forall_forall with (x := N.to_nat (sem_uninterp "unpack_idx" arg0)) in H9.
              unfold setalog in H9.
              eapply lift_inequality in n. 
              eapply PeanoNat.Nat.eqb_neq in n.
              rewrite n in H9.
              cleanup.
              repeat auto_specialize;
              cleanup.
              rewrite <- H9 in H6.
              rewrite H3 in H6.
              inverseS H6.
              cbn in H6.
              subst.
              rewrite N2Nat.id in H4.
              eauto.
              rewrite in_seq.
              lia.
            }
            all: try first [eapply amweakening |eapply vmweakening | eapply amdirect | eapply vmdirect].
          }
          contradiction H.
          intros.
          destruct method_id.
          {
            cbn in H.
            unfold apply_alog in *.
            cleanup.
            pose proof (projT2 (write_rf_symb_compact arg0 x (idx_wf' arg0))).
            cbn beta in H4.
            join H1 H4.
            eapply wpa_direct in H5.
            cleanup.
            subst.
            unfold write_method'.
            repeat eexists.
            eauto.
            all: try first [eapply amweakening |eapply vmweakening | eapply amdirect | eapply vmdirect].
          }
          {
            contradiction H.
          }
        }
        {
          contradiction H4.
        }
      }
      split.
      {
        intros.
        destruct r; cbn in *; cbv in H4; cleanup; contradiction H4.
      }
      {
        destruct r; cbn in *;
        do 33 (try destruct sm); cbn in *; intros.
        all: try (cbv in H4;
                  cleanup;
                  easy).
      }
      Qed.
*)
