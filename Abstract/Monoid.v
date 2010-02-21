Require Import
  Technology.Setoid
  Abstract.Magma
  Abstract.Semigroup.

Record Monoid (M : Setoid) (m : Magma M) (s : Semigroup M m) := {
  identity : car M ;
  leftIdentity : forall a : car M,
    eq M (operation M m identity a) a ;
  rightIdentity : forall a : car M,
    eq M (operation M m a identity) a
}.
