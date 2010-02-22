Require Import
  Technology.Setoid
  Technology.Nonzero
  Abstract.Magma.

Record Semigroup (M : Setoid) (m : Magma M) := {
  associativity : forall a b c : car M,
    eq M (operation M m (operation M m a b) c) (operation M m a (operation M m b c))
}.

Program Definition Semigroup_Nonzero (M : Setoid) (zero : car M) (m : Magma M) (s : Semigroup M m) :
  forall prf1 : (forall x y : car M, ~ eq M x zero -> ~ eq M y zero -> ~ eq M (operation M m x y) zero),
  Semigroup (Nonzero M zero) (Magma_Nonzero M zero m prf1) :=
  fun prf1 =>
    Build_Semigroup
      (Nonzero M zero)
      (Magma_Nonzero M zero m prf1)
      _.
Next Obligation.
apply (associativity _ _ s).
Qed.
