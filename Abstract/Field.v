Require Import
  Technology.Setoid
  Abstract.Magma
  Abstract.Abelian
  Abstract.Semigroup
  Abstract.Monoid
  Abstract.Group.

Record Ring (M : Setoid) (m : Magma M) (m' : Magma M) (s : Semigroup M m) (mo : Monoid M m s) (a : Abelian M m) (s' : Semigroup M m') (mo' : Monoid M m' s') (g : Group M m s mo) := {
  leftDistributivity : forall a b c,
    eq M (operation M m' (operation M m a b) c)
         (operation M m (operation M m' a c) (operation M m' b c)) ;
  rightDistributivity : forall a b c,
    eq M (operation M m' c (operation M m a b))
         (operation M m (operation M m' c a) (operation M m' c b))
}.
