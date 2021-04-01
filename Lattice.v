Require Import Coq.Relations.Relations.

Section LatticeOrder.

  Variable A : Type.
  Variable R : relation A.
  Hypothesis ordered : order A R.

  Definition upper_bound x y ub := R x ub /\ R y ub.

  Definition lub x y ub :=
    upper_bound x y ub /\
    forall ub', upper_bound x y ub' -> R ub ub'.

  Theorem lub_unique :
    forall x y z, lub x y z -> unique (lub x y) z.
  Proof.
    intros x y z (Hub1,HR1).
    split.
    split; assumption.
    intros z' (Hub2,HR2).
    apply (ord_antisym _ _ ordered).
    apply HR1; assumption.
    apply HR2; assumption.
  Qed.

  Definition lower_bound x y lb := R lb x /\ R lb y.

  Definition glb x y lb :=
    lower_bound x y lb /\
    forall lb', lower_bound x y lb' -> R lb' lb.

  Theorem glb_unique :
    forall x y z, glb x y z -> unique (glb x y) z.
  Proof.
    intros x y z (Hlb1,HR1).
    split.
    split; assumption.
    intros z' (Hlb2,HR2).
    apply (ord_antisym _ _ ordered).
    apply HR2; assumption.
    apply HR1; assumption.
  Qed.

  Record lattice_ord : Prop := {
    lattice_exists_meet : forall x y, exists u, lub x y u;
    lattice_exists_join : forall x y, exists u, glb x y u
  }.

End LatticeOrder.


Section LatticeAlgebra.

  Variable A : Type.

  Record lattice := {
    meet : A -> A -> A;
    join : A -> A -> A;
    lat_meet_comm : forall a b, meet a b = meet b a;
    lat_join_comm : forall a b, join a b = join b a;
    lat_meet_assoc : forall a b c, meet a (meet b c) = meet (meet a b) c;
    lat_join_assoc : forall a b c, join a (join b c) = join (join a b) c;
    lat_meet_idem : forall a, meet a a = a;
    lat_join_idem : forall a, join a a = a;
    lat_meet_absorbs : forall a b, meet a (join a b) = a;
    lat_join_absorbs : forall a b, join a (meet a b) = a;
  }.

End LatticeAlgebra.


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
