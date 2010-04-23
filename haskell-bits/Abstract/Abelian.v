Require Import
  Technology.Setoid
  Technology.Nonzero
  Abstract.Magma.

Record Abelian (M : Setoid) (m : Magma M) := {
  commutativity : forall a b : car M,
    eq M (operation M m a b) (operation M m b a)
}.

Program Definition Abelian_Nonzero (M : Setoid) (zero : car M) (m : Magma M) (a : Abelian M m) :
  forall prf1 : (forall x y : car M, ~ eq M x zero -> ~ eq M y zero -> ~ eq M (operation M m x y) zero),
  Abelian (Nonzero M zero) (Magma_Nonzero M zero m prf1) :=
  fun prf1 =>
    Build_Abelian
      (Nonzero M zero)
      (Magma_Nonzero M zero m prf1)
      _.
Next Obligation.
apply (commutativity _ _ a).
Qed.

