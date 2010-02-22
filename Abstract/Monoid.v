Require Import
  Technology.Setoid
  Technology.Nonzero
  Abstract.Magma
  Abstract.Semigroup.

Record Monoid (M : Setoid) (m : Magma M) (s : Semigroup M m) := {
  identity : car M ;
  leftIdentity : forall a : car M,
    eq M (operation M m identity a) a ;
  rightIdentity : forall a : car M,
    eq M (operation M m a identity) a
}.

Program Definition Monoid_Nonzero (M : Setoid) (zero : car M) (m : Magma M) (s : Semigroup M m) (mo : Monoid M m s) :
  forall (prf1 : forall x y : car M, ~ eq M x zero -> ~ eq M y zero -> ~ eq M (operation M m x y) zero)
         (prf2 : ~ eq M (identity M m s mo) zero),
  Monoid (Nonzero M zero) (Magma_Nonzero M zero m prf1) (Semigroup_Nonzero M zero m s prf1) :=
  fun prf1 prf2 =>
    Build_Monoid
      (Nonzero M zero)
      (Magma_Nonzero M zero m prf1)
      (Semigroup_Nonzero M zero m s prf1)
      (exist _ (identity M m s mo) prf2)
      _
      _.
Next Obligation.
apply (leftIdentity M m s mo).
Qed.
Next Obligation.
apply (rightIdentity M m s mo).
Qed.
