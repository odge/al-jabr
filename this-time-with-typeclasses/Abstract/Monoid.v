Require Import
  Technology.Setoid
  Abstract.Magma
  Abstract.Semigroup.

Class Monoid `{s : Semigroup} := {
  identity ;
  leftIdentity : forall a, identity & a == a ;
  rightIdentity : forall a, a & identity == a
}.

Notation "'zero'" := (@identity Additive _ _ _ _).
Notation "'one'" := (@identity Multiplicative _ _ _ _).

