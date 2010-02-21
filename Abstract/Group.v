Require Import
  Technology.Setoid
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

