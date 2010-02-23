Require Import
  Technology.Setoid
  Abstract.Magma
  Abstract.Semigroup.

Class Monoid `{s : Semigroup} := {
  identity ;
  leftIdentity : forall a, identity & a == a ;
  rightIdentity : forall a, a & identity == a
}.

Class MultiplicativeMonoid `(Monoid) := {}.
Class AdditiveMonoid `(Monoid) := {}.

Definition getMultiplicative' `(MultiplicativeMonoid) : Monoid.
intros.
assumption.
Defined.

Definition getAdditive' `(AdditiveMonoid) : Monoid.
intros.
assumption.
Defined.

Notation "'zero'" := (@identity _ (getAdditive _) _ _).
Notation "'one'" := (@identity _ (getMultiplicative _) _ _).
