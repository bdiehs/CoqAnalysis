Add LoadPath "~/coq/coq".
Require Export Order.

Set Implicit Arguments.
Section FieldDef.

Context `{U : Type}.

(*An element of type U is either 0 or something with an inverse*)

Context `{ApartZero : U -> Prop}.
Definition Nonzero := sig (ApartZero).

Class FieldOps : Type :=
  {
    F_add : U -> U -> U;
    F_opp : U -> U;
    F_mul : U -> U -> U;
    F_inv : Nonzero -> U;
    F_0 : U;
    F_nonzero : ApartZero F_0 -> False;
    F_1 : Nonzero;
  }.

Context `{F : FieldOps}.


End FieldDef.

Delimit Scope F_scope with field.
Local Open Scope F_scope.

Notation "a + b" := (F_add a b) : F_scope.
Notation "a * b" := (F_mul a b) : F_scope.
Notation "- a" := (F_opp a) : F_scope.
Notation "/ a" := (F_inv a) : F_scope.
Notation "a - b" := (F_add a (F_opp b)) : F_scope.
Notation "a / b" := (F_mul a (F_inv b)) : F_scope.
(*`x will be the projection of a nonzero type to a U type*)
Notation "` a" := (proj1_sig a) (at level 40) : F_scope.
(*In this case, (x†Px) would be a nonzero element such that 
  x is the element in U and Px is the proof that x is nonzero. *)
Notation "x † Px" := (exist _ x Px) (at level 40) : F_scope.
Notation "0" := (F_0) : F_scope.
Notation "1" := (`F_1) : F_scope.


Section FieldDef.

Class FieldTheory (U : Type) (ApartZero : U -> Prop) (F : @FieldOps U ApartZero)
 : Type :=
  {
    F_add_comm : forall x y, x + y = y + x;
    F_add_assoc : forall x y z, x + y + z = x + (y + z);
    F_add_0 : forall x, 0 + x = x;
    F_add_opp_0 : forall x, x + (-x) = 0;
    F_mul_comm : forall x y, x * y = y * x;
    F_mul_assoc : forall x y z, x * y * z = x * (y * z);
    F_mul_1 : forall x, 1 * x = x;
    F_mul_inv_1 : forall x, `x / x = 1;
    F_distr : forall x y z, x * (y + z) = (x * y) + (x * z);
  }.


Class Field (U : Type) : Type :=
  {
    field_apart_zero : U -> Prop;
    field_ops : @FieldOps U field_apart_zero;
    field_theory : @FieldTheory U field_apart_zero field_ops;
  }.


End FieldDef.

Section Props.

Variable U : Type.
Variable ApartZero : U -> Prop.
Variable FO : @FieldOps U ApartZero.
Variable FT : @FieldTheory U ApartZero FO.

Definition Prop1_14_a : forall x y z,
   x + y = x + z -> y = z.
Proof.
  intros.
  rewrite <- (F_add_0 y), <- (F_add_0 z).
  rewrite <- (F_add_opp_0 x).
  rewrite (F_add_comm x).
  rewrite (F_add_assoc _ _ y).
  rewrite (F_add_assoc _ _ z).
  f_equal. apply H.
Qed.

Definition Prop1_14_b : forall x y,
  x + y = x -> y = 0.
Proof.
  intros.
  apply Prop1_14_a with (x := x).
  rewrite (F_add_comm _ 0).
  rewrite F_add_0.
  apply H.
Qed.

Definition Prop1_14_c : forall x y,
  x + y = 0 -> y = -x.
Proof.  Admitted.

Definition Prop1_14_d : forall x,
  -(-x) = x.
Proof.  Admitted.

Definition Prop1_15_c : forall x y,
  `x * y = 1 -> y = 1 / x.
Proof.  Admitted.

(*I think this needs 1.16a*)
Definition Prop_1_15_d_prev : forall x Px,
   ApartZero (/(x†Px)).
Proof.  Admitted.

Definition Prop1_15_d : forall x Px Px_inv,
  1 / ((1 / (x † Px)) † Px_inv) = x.
Proof.
  intros.
  symmetry.
  apply Prop1_15_c.
  rewrite F_mul_comm.
  simpl.
  rewrite F_mul_1.
  apply (F_mul_inv_1 (x†Px)).
Qed.

Definition Prop1_16_a : forall x,
  0 * x = 0.
Proof.  Admitted.

Definition Prop1_16_c1 : forall x y,
  (-(x * y) = (-x) * y).
Proof.  Admitted.

Definition Prop1_16_c2 : forall x y,
  (-(x * y) = x * (-y)).
Proof.  Admitted.

Open Scope ord_scope.

Class OrderedField (O : @Order U) : Type :=
  {
    ordered_field_add : forall x y z, y < z -> x + y < x + z;
    ordered_field_zero : forall x y, 0 < x -> 0 < y -> 0 < x * y;
  }.

Variable O : @Order U.
Variable OF : OrderedField O.

Definition Prop1_18_a : forall x,
  0 < x -> -x < 0.
Proof.
  intros.
  replace 0 with (-x + x).
  2:{ rewrite F_add_comm. apply F_add_opp_0. }
  replace (-x < -x + x) with (-x + 0 < -x + x).
  2:{ f_equal. rewrite F_add_comm. apply F_add_0. }
  apply ordered_field_add. apply H.
Qed.

Definition Prop1_18_c : forall x y z,
  x < 0 /\ y < z -> x * z < x * y.
Proof.
  intros.
  replace (x*y) with (x*y + 0).
  2:{ rewrite F_add_comm. rewrite F_add_0. reflexivity. }
  replace (x * z) with (x * y + (x * z - x * y)).
  2:{ rewrite F_add_comm. rewrite F_add_assoc.
      rewrite (F_add_comm (-(x*y))).
      rewrite F_add_opp_0. rewrite F_add_comm.
      rewrite F_add_0. reflexivity. }
  apply ordered_field_add.
  rewrite <- (Prop1_14_d (x * z - x * y)).
  apply Prop1_18_a.
  rewrite Prop1_16_c2.
  rewrite <- F_distr.
  rewrite Prop1_16_c1.
  apply ordered_field_zero.
  replace (-x) with (- x + 0).
  2: { rewrite F_add_comm. apply F_add_0. }
  replace (0 < -x + 0) with (-x + x < -x + 0).
  2: { f_equal. rewrite F_add_comm. apply F_add_opp_0. }
  apply ordered_field_add.
  apply H.
  rewrite F_add_comm.
  replace (0) with (-y+y).
  2: { rewrite F_add_comm. apply F_add_opp_0. }
  apply ordered_field_add.
  apply H.
Qed.

Definition Prop1_18_d : forall x,
  ApartZero x -> 0 < (x * x).
Proof.
  intros.
  destruct (O_prop1 0 x) as [H1 | [H1 | H1]].
  - apply ordered_field_zero.
    apply H1.
    apply H1.
  - assert False.
    apply F_nonzero.
    destruct H1 as [H2 [H3 H4]].
    rewrite H3.
    apply H.
    destruct H0.
  - rewrite <- Prop1_14_d.
    rewrite Prop1_16_c1.
    rewrite Prop1_16_c2.
    destruct H1 as [H2 [H3 H4]].
    apply (ordered_field_add (-x)) in H4.
    rewrite F_add_comm in H4.
    rewrite F_add_opp_0 in H4.
    rewrite F_add_comm in H4.
    rewrite F_add_0 in H4.
    apply ordered_field_zero.
    apply H4.
    apply H4.
Qed.

Definition Prop1_18_d_cor : 0 < 1.
Proof.
  rewrite <- F_mul_1.
  apply Prop1_18_d.
  apply (proj2_sig F_1).
Qed.

Lemma Prop1_18_lemma : forall x Px,
  0 < x -> 0 < /(x†Px).
Proof.
  intros.
  destruct (O_prop1 0 (/(x†Px))) as [H3| [H3 | H3]] eqn:H0.
    + apply H3.
    + destruct H3 as [H4 [H5 H6]]. assert (False) as contra.
      { apply F_nonzero. replace 0 with (/(x†Px)).
        apply Prop_1_15_d_prev. }
      destruct contra.
    + destruct H3 as [H4 [H5 H6]].
      assert (False) as contra.
      { pose (Prop1_18_c (/(x†Px)) 0 x) as H7.
        assert (/ (x † Px) < 0 < x) as H9.
        { split. apply H6. apply H. }
        apply H7 in H9.
        rewrite F_mul_comm in H9.
        rewrite (F_mul_inv_1 (x†Px)) in H9.
        rewrite F_mul_comm in H9.
        rewrite Prop1_16_a in H9.
        destruct (O_prop1 0 1) as [H1 | [H1 | H1]].
        * apply H1 in H9. apply H9.
        * apply H1 in H9. apply H9.
        * destruct H1 as [H1 [_ _]].
          apply (H1 Prop1_18_d_cor). }
      destruct contra.
Qed.

Definition Prop1_18_e : forall x Px y Py,
  0 < x < y -> 0 < /(y†Py) < /(x†Px).
Proof.
  intros.
  destruct H as [H1 H2].
  assert (0 < /(y†Py)).
  { apply Prop1_18_lemma.
    eapply O_prop2.
    apply H1. apply H2. }
  split.
  - apply H.
  - assert (0 < /(x†Px)).
    apply Prop1_18_lemma.
    apply H1.
    assert (0 < y - x).
    { rewrite F_add_comm.
      replace 0 with (-x+x).
      2: { rewrite F_add_comm. apply F_add_opp_0. }
      apply ordered_field_add.
      apply H2. }
    assert (0 < (/(x†Px)) * ((/(y†Py))) * (y-x)) as H4.
    { apply ordered_field_zero. 2: apply H3.
      apply ordered_field_zero. 2: apply H.
      apply H0. }
      rewrite F_distr in H4.
      rewrite (F_mul_assoc _ _ y) in H4.
      rewrite (F_mul_comm _ y) in H4.
      rewrite (F_mul_inv_1 (y†Py)) in H4.
      rewrite F_mul_comm in H4.
      rewrite F_mul_1 in H4.
      rewrite F_mul_comm in H4.
      rewrite <- F_mul_assoc in H4.
      rewrite <- Prop1_16_c1 in H4.
      rewrite (F_mul_inv_1 (x†Px)) in H4.
      rewrite <- Prop1_16_c1 in H4.
      rewrite F_mul_1 in H4.
      rewrite <- (F_add_0 (/(y†Py))).
      rewrite F_add_comm.
      replace (/(x†Px)) with ((/(y†Py)) + ((/(x†Px))- (/(y†Py)))).
      2:{ rewrite F_add_comm.
          rewrite F_add_assoc.
          rewrite (F_add_comm _ (/(y†Py))).
          rewrite F_add_opp_0.
          rewrite F_add_comm.
          apply F_add_0. }
      apply ordered_field_add.
      apply H4.
Qed.

End Props.

Close Scope F_scope.
Close Scope ord_scope.



