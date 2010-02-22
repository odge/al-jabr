Require Import
  Technology.Setoid
  Technology.Nonzero
  Abstract.Magma
  Abstract.Semigroup
  Abstract.Monoid.

Record Group (M : Setoid) (m : Magma M) (s : Semigroup M m) (mo : Monoid M m s) := {
  inverse : car M -> car M ;
  inverseRespectful : Proper (eq M ==> eq M) inverse ;
  leftInverse : forall a : car M,
    eq M (operation M m (inverse a) a) (identity M m s mo) ;
  rightInverse : forall a : car M,
    eq M (operation M m a (inverse a)) (identity M m s mo)
}.

Program Definition Group_Nonzero (M : Setoid) (zero : car M) (m : Magma M) (s : Semigroup M m) (mo : Monoid M m s) (g : Group M m s mo) :
  forall (prf1 : forall x y : car M, ~ eq M x zero -> ~ eq M y zero -> ~ eq M (operation M m x y) zero)
         (prf2 : ~ eq M (identity M m s mo) zero)
         (prf3 : forall a : car M, ~ eq M a zero -> ~ eq M (inverse M m s mo g a) zero),
  Group (Nonzero M zero) (Magma_Nonzero M zero m prf1) (Semigroup_Nonzero M zero m s prf1) (Monoid_Nonzero M zero m s mo prf1 prf2) :=
  fun prf1 prf2 prf3 =>
    Build_Group
      (Nonzero M zero)
      (Magma_Nonzero M zero m prf1)
      (Semigroup_Nonzero M zero m s prf1)
      (Monoid_Nonzero M zero m s mo prf1 prf2)
      (fun a =>
        exist _ (inverse M m s mo g (proj1_sig a)) (prf3 (proj1_sig a) (proj2_sig a)))
      _
      _
      _.
Next Obligation.
unfold Proper.
unfold respectful.
simpl.
intros.
destruct x; destruct y.
apply (inverseRespectful).
assumption.
Qed.
Next Obligation.
apply (leftInverse M m s mo).
Qed.
Next Obligation.
apply (rightInverse M m s mo).
Qed.
