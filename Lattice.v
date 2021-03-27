Section Relations.

  Variable A : Type.

  Definition Rel := A -> A -> Prop.

  Definition reflexive (R : Rel) := forall x, R x x.

  Definition symmetric (R : Rel) := forall x y, R x y -> R y x.

  Definition antisymmetric (R : Rel) := forall x y, R x y -> R y x -> x = y.

  Definition transitive (R : Rel) := forall x y z, R x y -> R y z -> R x z.

End Relations.


Section Ensembles.

  Variable A : Type.

  Definition Ensemble := A -> Prop.

  Definition In (x : A) (s : Ensemble) := s x.

  Definition included (s1 s2: Ensemble) := forall x, s1 x -> s2 x.

  Inductive empty : Ensemble := .

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
