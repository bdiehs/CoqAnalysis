
Set Implicit Arguments.
Section FieldDef.

Context `{U_star : Type}.

(*An element of type U is either 0 or something with an inverse*)
Inductive U : Type :=
  | F_0
  | F_star (u : U_star)
.

Class Field : Type :=
  {
    F_add : U -> U -> U;
    F_opp : U -> U;
    F_mul : U -> U -> U;
    F_inv : U_star -> U;
    F_1_star : U_star;
  }.

Context `{F : Field}.

Definition F_1 : U := F_star F_1_star.

End FieldDef.

Delimit Scope F_scope with field.
Local Open Scope F_scope.

Notation "a + b" := (F_add a b) : F_scope.
Notation "a * b" := (F_mul a b) : F_scope.
Notation "- a" := (F_opp a) : F_scope.
Notation "` a" := (F_inv a) (at level 40) : F_scope.
Notation "0" := (F_0) : F_scope.
Notation "1" := (F_1) : F_scope.


Class FieldTheory (U_star : Type) (F : @Field U_star) : Type :=
  {
    F_add_comm : forall x y, x + y = y + x;
    F_add_assoc : forall x y z, x + y + z = x + (y + z);
    F_add_0 : forall x, 0 + x = x;
    F_add_opp_0 : forall x, x + (-x) = 0;
    F_mul_comm : forall x y, x * y = y * x;
    F_mul_assoc : forall x y z, x * y * z = x * (y * z);
    F_mul_1 : forall x, 1 * x = x;
    F_mul_inv_1 : forall x_star,
      (F_star x_star) * (`x_star) = 1;
    F_distr : forall x y z, x * (y + z) = (x * y) + (x * z);
  }.

Section Props.

Variable U_star : Type.
Variable F : @Field U_star.
Variable FT : @FieldTheory U_star F.

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

End Props.

Close Scope F_scope.
