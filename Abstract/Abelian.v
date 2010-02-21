Require Import
  Technology.Setoid
  Abstract.Magma.

Record Abelian (M : Setoid) (m : Magma M) := {
  commutativity : forall a b : car M,
    eq M (operation M m a b) (operation M m b a)
}.
