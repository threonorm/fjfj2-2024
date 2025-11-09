    Require Import NArith.
Require Import Lia.
    Open Scope N.
    Lemma land_mod2 : forall a b, (N.land a b) mod 2 = (N.land (a mod 2) b) mod 2.
      intros.
      eapply Nbit_faithful_iff.
      unfold eqf.
      erewrite <- N.land_ones with (n:= 1).
      erewrite <- N.land_ones with (n:= 1).
      erewrite <- N.land_ones with (n:= 1).
      intros.
      erewrite !Nand_semantics.
      assert ( n < 2 \/ n >= 2)%nat by lia.
      destruct H.
      2:{
        rewrite Bool.andb_comm.
        destruct n; try lia.
        destruct n; try lia.
        simpl.
        rewrite Bool.andb_comm.
        simpl; eauto.
      }
      destruct n; try destruct n; try lia.
      simpl.

        rewrite Bool.andb_comm.
        simpl.
        set (N.testbit_nat a 0 && N.testbit_nat b 0)%bool.
        rewrite Bool.andb_comm .
        simpl.
        rewrite <- Bool.andb_assoc .
        rewrite Bool.andb_comm .
        rewrite <- Bool.andb_assoc .
        simpl.
        rewrite Bool.andb_comm .
        eauto.
        simpl.
        rewrite Bool.andb_comm.
        simpl.
        rewrite Bool.andb_comm .
        simpl.
        eauto.
    Qed.

    Lemma land_mod2_true : forall a b, (N.land a b) mod 2 = 1 -> a mod 2 = 1.
      intros.
      eapply Nbit_faithful_iff.
      unfold eqf.
      erewrite <- N.land_ones with (n:= 1).
      intros.
      erewrite !Nand_semantics.
      eapply Nbit_faithful_iff in H.
      assert ( n < 2 \/ n >= 2)%nat by lia.
      destruct H0.
      2:{
        rewrite Bool.andb_comm.
        destruct n; try lia.
        destruct n; try lia.
        simpl.
        eauto.
      }
      erewrite <- N.land_ones with (n:= 1) in H.
      destruct n; try destruct n; try lia.
      {
        simpl.
        specialize (H 0%nat).
        erewrite !Nand_semantics in H.
        simpl in *.
        eapply Bool.andb_true_iff in H.
        destruct H.
        eapply Bool.andb_true_iff in H.
        destruct H.
        eapply Bool.andb_true_iff; eauto.
      }
      {
        simpl.
        rewrite Bool.andb_comm.
        simpl; eauto.
      }
    Qed.

    Lemma land_mod2_false : forall a b, (N.land a b) mod 2 = 0 -> a mod 2 = 0 \/ b mod 2 = 0.
      intros.
      eapply Nbit_faithful_iff in H.
      unfold eqf in *.
      specialize (H 0%nat).
      erewrite <- N.land_ones with (n:= 1) in H.
      rewrite Nand_semantics in H.
      simpl in H.
      rewrite Bool.andb_comm in H.
      simpl in H.
      erewrite <- N.land_ones with (n:= 1).
      erewrite <- N.land_ones with (n:= 1).
      destruct a; simpl in *.
      left; eauto.
      destruct b; simpl in *.
      right; eauto.
      rewrite Pand_semantics in H.
      eapply Bool.andb_false_iff in H.
      destruct p;
      destruct p0; simpl in *; eauto.
      destruct H; inversion H.
      destruct H; inversion H.
      destruct H; inversion H.
      destruct H; inversion H.
    Qed.

    Lemma land_mod2_false_rev : forall a b,  a mod 2 = 0 ->(N.land a b) mod 2 = 0.
      intros.
      eapply Nbit_faithful_iff .
      eapply Nbit_faithful_iff in H.
      unfold eqf in *.
      intros.
      (* specialize (H 0%nat). *)
      erewrite <- N.land_ones with (n:= 1) in H.
      erewrite <- N.land_ones with (n:= 1).
      rewrite Nand_semantics .
      rewrite Bool.andb_comm .
      simpl in H.
      specialize (H 0%nat).
      rewrite Nand_semantics in H.
      simpl in H.
      rewrite Bool.andb_comm in H.
      simpl in H.
      destruct n; simpl; eauto.
      rewrite Nand_semantics .
      rewrite H.
      simpl; eauto.
    Qed.

    Lemma lnot_mod2: forall a, (N.lnot a 1) mod 2 = 0 -> a mod 2 = 1.
      intros.
      eapply Nbit_faithful_iff .
      eapply Nbit_faithful_iff in H.
      unfold eqf in *.
      intros.
      (* specialize (H 0%nat). *)
      erewrite <- N.land_ones with (n:= 1) in H.
      erewrite <- N.land_ones with (n:= 1).
      rewrite Nand_semantics .
      specialize (H 0%nat).
      rewrite Nand_semantics in H.
      destruct n.
      2:{ simpl in *.
      rewrite Bool.andb_comm. eauto. }
      simpl in *.
      simpl; eauto.
      rewrite Bool.andb_true_r in *.
      erewrite <- Ntestbit_Nbit in H.
      erewrite N.lnot_spec_low in H; try lia.
      eapply Bool.negb_false_iff in H.
      erewrite Ntestbit_Nbit in H.
      eauto.
    Qed.

    Lemma lnot_mod2': forall a, (N.lnot a 1) mod 2 = 1 -> a mod 2 = 0.
      intros.
      eapply Nbit_faithful_iff .
      eapply Nbit_faithful_iff in H.
      unfold eqf in *.
      intros.
      (* specialize (H 0%nat). *)
      erewrite <- N.land_ones with (n:= 1) in H.
      erewrite <- N.land_ones with (n:= 1).
      rewrite Nand_semantics .
      specialize (H 0%nat).
      rewrite Nand_semantics in H.
      destruct n.
      2:{ simpl in *.
      rewrite Bool.andb_comm. eauto. }
      simpl in *.
      simpl; eauto.
      rewrite Bool.andb_true_r in *.
      erewrite <- Ntestbit_Nbit in H.
      erewrite N.lnot_spec_low in H; try lia.
      eapply Bool.negb_false_iff in H.
      erewrite Ntestbit_Nbit in H.
      destruct (N.testbit_nat a 0); simpl in *; eauto.
    Qed.

    Lemma lor_mod2_true_r : forall a, (N.lor a 0) mod 2 = 1 -> a mod 2 = 1.
      intros.
      eapply Nbit_faithful_iff.
      eapply Nbit_faithful_iff in H.
      unfold eqf in *.
      intros.
      erewrite <- N.land_ones with (n := 1).
      erewrite <- N.land_ones with (n := 1) in H.
      destruct n eqn:?;
      specialize H with (n := n);
      rewrite !Nand_semantics;
      rewrite !Nand_semantics in H;
      rewrite !Nor_semantics in H;
      rewrite Bool.andb_orb_distrib_l in H;
      rewrite Bool.orb_false_r in H;
      rewrite Heqn0 in H;
      simpl in *;
      eauto.
    Qed.

    Lemma lor_mod2_true : forall a b, (N.lor a b) mod 2 = 1 -> a mod 2 = 1 \/ b mod 2 = 1.
      intros.
      eapply Nbit_faithful_iff in H.
      assert (a mod 2 = 1 \/ a mod 2 = 0) by (Zify.zify; PreOmega.Z.quot_rem_to_equations;lia).
      destruct H0.
      {
        left.
        eauto.
      }
      {
        right.
        eapply Nbit_faithful_iff.
        eapply Nbit_faithful_iff in H0.
        unfold eqf in *.
        intros.
        erewrite <- N.land_ones with (n := 1).
        erewrite <- N.land_ones with (n := 1) in H.
        rewrite <- N.land_ones with (n := 1) in H0.
        destruct n eqn:?.
        {
          specialize (H n).
          specialize (H0 n).
          rewrite !Nand_semantics.
          rewrite !Nand_semantics in H.
          rewrite !Nor_semantics in H.
          rewrite Bool.andb_orb_distrib_l in H.
          subst.
          do 2 (simpl in H; erewrite Bool.andb_comm in H).
          simpl.
          rewrite !Nand_semantics in H0.
          simpl in H0.
          rewrite Bool.andb_comm in H0.
          simpl in H0.
          rewrite H0 in H.
          simpl in H.
          rewrite H.
          eauto.
        }
        {
          rewrite Nand_semantics.
          simpl.
          rewrite Bool.andb_comm.
          eauto.
        }
      }
    Qed.

    Ltac simplify_N_logic :=
      (* TODO complete *)
        repeat match goal with 
        | [ H : N.land ?a ?b mod 2 = 1 |- _] => 
          pose proof (land_mod2_true _ _ H);
          rewrite N.land_comm in H;
          eapply land_mod2_true in H
        | [ H : N.land ?a ?b mod 2 = 0 |- _] => 
          eapply (land_mod2_false _ _ H)
        | [ H : N.lor ?a 0 mod 2 = 1 |- _] =>
          eapply lor_mod2_true_r in H
        | [ H : N.lor 0 ?a mod 2 = 1 |- _] =>
          rewrite N.lor_comm in H;
          eapply lor_mod2_true_r
        | [ H : N.lor ?a ?b mod 2 = 1 |- _] =>
          eapply lor_mod2_true in H
        | [ H : N.lnot ?a 1 mod 2 = 1 |- _] =>
          eapply lnot_mod2' in H
        end.

