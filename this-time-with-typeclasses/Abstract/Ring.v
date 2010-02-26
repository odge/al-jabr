Require Import
  Technology.Setoid
  Abstract.Magma
  Abstract.Abelian
  Abstract.Semigroup
  Abstract.Monoid
  Abstract.Group.

Class Ring M
  `(add : Magma Additive M) `(mul : Magma Multiplicative M)
  s s'
  (addm : @Monoid Additive M add s) (mulm : @Monoid Multiplicative M mul s')
  (g : @Group Additive M add _ _)
  := {
    leftDistributivity : forall a b c, c (x) (a (+) b) == c (x) a (+) c (x) b ;
    rightDistributivity : forall a b c, (a (+) b) (x) c == a (x) c (+) b (x) c
  }.

