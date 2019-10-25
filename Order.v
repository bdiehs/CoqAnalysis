Require Import Coq.Relations.Relations.

Section SubsetDef.

Context `{U : Type}.

(*Definition 1.3*)
Definition subset (A : U -> Prop) (B : U -> Prop) :=
  forall x, A x -> B x.
Definition nonempty (A : U -> Prop) :=
  exists x, A x.

End SubsetDef.

Notation "A ⊂ B" := (subset A B) (at level 50) : subset_scope.
Notation "A == B" := (subset A B /\ subset B A) (at level 50) : subset_scope.

Section OrderDef.

Context `{U : Type}.

(*Definition 1.5*)
Class Order : Type :=
  {
    ord : relation U;
    O_prop1 : forall x y,
      (ord x y /\ ~(x = y) /\ ~(ord y x)) \/
      (~(ord x y) /\ x = y /\ ~(ord y x)) \/
      (~(ord x y) /\ ~(x = y) /\ ord y x);
    O_prop2 : forall x y z, ord x y -> ord y z -> ord x z;
  }.

End OrderDef.

Notation "x < y" := (ord x y) : ord_scope.
Notation "x ≤ y" := (ord x y \/ x = y) (at level 50) : ord_scope.

Section OrderBounds.

Variable U : Type.

Open Scope ord_scope.

(*Definition 1.6*)


(*Definition 1.7*)
Definition upper_bound (O : Order) (E : U -> Prop) (beta : U) :=
  forall x, E x -> x ≤ beta.

Definition lower_bound (O : Order) (E : U -> Prop) (beta : U) :=
  forall x, E x -> beta ≤ x.

(*Definition 1.8*)
Definition least_upper_bound (O : Order) (E : U -> Prop) (alpha : U) :=
  upper_bound O E alpha /\
  (forall gamma, gamma < alpha -> ~(upper_bound O E gamma)).

Definition greatest_lower_bound (O : Order) (E : U -> Prop) (alpha : U) :=
  lower_bound O E alpha /\
  (forall gamma, alpha < gamma -> ~(lower_bound O E gamma)).



(* Definition 1.10 *)
(*<sup> is the a supreme function that assigns a supreme to sets.
  In other words, "lub_prop O sup" holds if sup works as expected.
  One could argue that sup needs to be defined only for sets that 
  are nonempty and bounded above. However, this complicates a lot
  the typing.
*)
Definition lub_property (O : Order)
  (sup : (U -> Prop) -> U) : Prop :=
  forall (E : U -> Prop)
  (x_E : U) (beta_E : U)
  (H : E x_E /\ upper_bound O E beta_E),
  least_upper_bound O E (sup E).

Definition glb_property (O : Order)
  (inf : (U -> Prop) -> U) : Prop :=
  forall (E : U -> Prop)
  (x_E : U) (beta_E : U)
  (H : E x_E /\ lower_bound O E beta_E),
  greatest_lower_bound O E (inf E).

(*Theorem 1.11*)
Theorem Th_1_11 (O : Order) (sup : (U -> Prop) -> U) (B : U -> Prop)
  (x_B : U) (beta_B : U) :
  lub_property O sup -> B x_B -> lower_bound O B beta_B ->
  let L := fun x => (lower_bound O B x) in
    exists alpha, least_upper_bound O L alpha /\ greatest_lower_bound O B alpha.
Proof.
  intros.
  exists (sup L).
  assert (least_upper_bound O L (sup L)).
  { apply (H _ beta_B x_B). split.
    - unfold L. intros x H2. apply H1. apply H2.
    - intros x H2. apply H2. apply H0. }
  split.
  - apply H2.
  - split.
    + intros x H3. destruct (O_prop1 (sup L) x) as [H4 | [H4 | H4]].
      * left. apply H4.
      * right. apply H4.
      * destruct H2.
        assert False. unfold not in H5.
        apply (H5 x). apply H4.
        intros y H6. apply H6. apply H3.
        contradiction.
    + intros gamma H3 H4.
      destruct H2.
      assert (~(L gamma)).
      { intros H6. destruct (O_prop1 (sup L) gamma) as [H7 | [H7 | H7]].
        - destruct (H2 gamma H6) as [H8 | H8].
          * apply H7 in H8. apply H8.
          * destruct H7 as [H9 [H10 H11]]. apply H10. symmetry. apply H8.
        - apply H7 in H3. apply H3.
        - apply H7 in H3. apply H3. }
      * apply H6 in H4. apply H4.
Qed.

Close Scope ord_scope.

End OrderBounds.



