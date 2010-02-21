Require Import
  Technology.Setoid
  Abstract.Magma.

Record Semigroup (M : Setoid) (m : Magma M) := {
  associativity : forall a b c : car M,
    eq M (operation M m (operation M m a b) c) (operation M m a (operation M m b c))
}.
