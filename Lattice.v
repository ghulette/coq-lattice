Section Relations.

  Variable A : Type.

  Definition Rel := A -> A -> Prop.

  Variable R : Rel.

  Definition reflexive := forall x, R x x.

  Definition symmetric := forall x y, R x y -> R y x.

  Definition antisymmetric := forall x y, R x y -> R y x -> x = y.

  Definition transitive := forall x y z, R x y -> R y z -> R x z.

  Definition order := reflexive /\ antisymmetric /\ transitive.

End Relations.

Section Lattice.

  Variable A : Type.
  Variable R : Rel A.
  Hypothesis ordered : order A R.

  Definition upper_bound x y ub := R x ub /\ R y ub.

  Definition lub x y ub :=
    upper_bound x y ub /\
    forall ub', upper_bound x y ub' -> R ub ub'.

  Theorem lub_unique :
    forall x y, exists z, lub x y z -> unique (lub x y) z.
  Admitted.

  Definition lower_bound x y lb := R lb x /\ R lb y.

  Definition glb x y lb :=
    lower_bound x y lb /\
    forall lb', lower_bound x y lb' -> R lb' lb.

  Theorem glb_unique :
    forall x y, exists z, glb x y z -> unique (glb x y) z.
  Admitted.

  Definition lattice :=
    forall x y,
      (exists u, lub x y u) /\
      (exists l, glb x y l).

End Lattice.


Section Ensembles.

  Variable A : Type.

  Definition Ensemble := A -> Prop.

  Definition In (x : A) (s : Ensemble) := s x.

  Definition included (s1 s2: Ensemble) := forall x, s1 x -> s2 x.

  Variant empty : Ensemble := .

  Definition is_empty (s : Ensemble) := ~exists x, s x.

  Theorem empty_is_empty :
    forall s, included s empty -> is_empty s.
  Proof.
    unfold included, is_empty.
    intros s H Hc.
    inversion Hc as (x,Hx).
    specialize (H x Hx).
    inversion H.
  Qed.

End Ensembles.
