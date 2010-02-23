Require Import
  Technology.Setoid
  Abstract.Magma
  Abstract.Abelian
  Abstract.Semigroup
  Abstract.Monoid
  Abstract.Group.

Class Ring M
  `(add : AdditiveMagma M) `(mul : MultiplicativeMagma M) s s' mo mo'
  (addm : @AdditiveMonoid M (getAdditive add) s mo) (mulm : @MultiplicativeMonoid M (getMultiplicative mul) s' mo')
  (g : @Group M (getAdditive add) _ _)
  := {
    leftDistributivity : forall a b c, c (x) (a (+) b) == c (x) a (+) c (x) b ;
    rightDistributivity : forall a b c, (a (+) b) (x) c == a (x) c (+) b (x) c
  }.
