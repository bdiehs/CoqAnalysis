
Set Implicit Arguments.
Section FieldDef.

Context `{U : Type}.

(*An element of type U is either 0 or something with an inverse*)

Context `{ApartZero : U -> Prop}.
Definition Nonzero := sig (ApartZero).

Class Field : Type :=
  {
    F_add : U -> U -> U;
    F_opp : U -> U;
    F_mul : U -> U -> U;
    F_inv : Nonzero -> U;
    F_0 : U;
    F_1 : U;
  }.

Context `{F : Field}.


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
(*In this case, (x|Px) would be a nonzero element such that 
  x is the element in U and Px is the proof that x is nonzero. *)
Notation "x | Px" := (exist _ x Px) (at level 40) : F_scope.
Notation "0" := (F_0) : F_scope.
Notation "1" := (F_1) : F_scope.


Class FieldTheory (U : Type) (ApartZero : U -> Prop) (F : @Field U ApartZero)
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

Section Props.

Variable U : Type.
Variable ApartZero : U -> Prop.
Variable F : @Field U ApartZero.
Variable FT : @FieldTheory U ApartZero F.

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

Definition Prop1_15_d : forall x Px Px_inv,
  1 / ((1 / (x | Px)) | Px_inv) = x.
Proof.
  intros.
  symmetry.
  apply Prop1_15_c.
  rewrite F_mul_comm.
  simpl.
  rewrite F_mul_1.
  apply (F_mul_inv_1 (x|Px)).
Qed.

End Props.

Close Scope F_scope.
