
Add LoadPath "~/coq/coq".
Require Export Field.
Require Export Coq.Init.Nat.

Definition excluded_middle := forall P : Prop,
  P \/ ~P.

Section RealFieldDef.



Variable U : Type.
Variable ApartZero : U -> Prop.
Variable FO : @FieldOps U ApartZero.
Variable FT : @FieldTheory U ApartZero FO.
Variable O : @Order U.
Variable OF : @OrderedField U ApartZero FO O.
Variable sup : (U -> Prop) -> U.
Variable LUB : lub_property U O sup.




Open Scope ord_scope.
Open Scope F_scope.

(*Theorem 1.20*)
Fixpoint natmul (n: nat) (x : U) : U :=
  match n with
  | 0 => 0
  | S n' => x + (natmul n' x)
  end.

Notation "n ** x" := (natmul n x) (at level 40) : F_scope.

Lemma Th1_20_lemma : forall n x,
  0 < x -> 0 ≤ n ** x.
Proof.
  intros.
  induction n.
  - right. reflexivity.
  - destruct (IHn).
    + rewrite <- (F_add_0 0).
      left. eapply O_prop2.
      apply ordered_field_add.
      apply OF. apply H.
      rewrite F_add_comm.
      apply ordered_field_add.
      apply OF. apply H0.
    + simpl. rewrite <- H0.
      rewrite F_add_comm.
      rewrite F_add_0.
      left. apply H.
Qed.

Definition Th1_20: forall x y,
  excluded_middle -> 0 < x -> exists n, y < n ** x.
Proof.
  intros.
  destruct (H (exists n, y < n ** x)).
  apply H1.
  assert (forall n, n ** x ≤ y).
  { intros. destruct (O_prop1 (n**x) y) as [H2 | [H2 | H2]].
    - left. apply H2.
    - right. apply H2.
    - assert False. apply H1. exists n. apply H2. 
      destruct H3. }
  pose (fun t => exists n, t = n ** x) as A.
  assert (least_upper_bound U O A (sup A)).
  { eapply (LUB A 0 y).
    exists Nat.zero. simpl. reflexivity.
    unfold upper_bound. intros.
    destruct H3.
    rewrite H3.
    apply H2. }
  assert (~(upper_bound U O A ((sup A)-x))).
  { unfold not. intros. apply H3 in H4. apply H4.
    rewrite <- F_add_0. rewrite (F_add_comm 0).
    apply ordered_field_add. apply OF.
    apply (Prop1_18_a FT OF). apply H0. }
  destruct (H (exists a, A a /\ (sup A) - x < a)).
  - destruct H5. destruct H5. destruct H5.
    rewrite H5 in H6.
    assert False.
    destruct H3.
    apply (order_trich_contr U O (x + (x1**x)) (sup A)).
    split.
    apply H3. exists (S x1). reflexivity.
    replace (sup A) with (x + ((sup A) - x)).
    2:{ rewrite F_add_comm. rewrite F_add_assoc. rewrite (F_add_comm (-x)).
        rewrite F_add_opp_0. rewrite F_add_comm. apply F_add_0. }
    apply ordered_field_add. apply OF. apply H6.
    destruct H7.
  - assert False. apply H4.
    unfold upper_bound. intros. destruct H6.
    destruct (order_trich_split U O x0 (sup A - x)).
    apply H7.
    assert False. apply H5. exists x0.
    split. exists x1. apply H6. apply H7.
    destruct H8.
    destruct H6.
Qed.