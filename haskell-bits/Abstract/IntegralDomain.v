Require Import
  Technology.Setoid
  Technology.Nonzero
  Abstract.Magma
  Abstract.Abelian
  Abstract.Semigroup
  Abstract.Monoid
  Abstract.Group
  Abstract.Ring.

Section IntegralDomain.

Variables
  (M : Setoid)
  (m : Magma M)
  (m' : Magma M)
  (s : Semigroup M m)
  (mo : Monoid M m s)
  (a : Abelian M m)
  (s' : Semigroup M m')
  (mo' : Monoid M m' s')
  (g : Group M m s mo).

Variable
  (a' : Abelian M m').

Definition zero := identity M m s mo.
Definition one := identity M m' s' mo'.

Record IntegralDomain := {
  zeroNotOne : ~ eq M zero one ;
  zeroProduct : forall a b,
    eq M (operation M m a b) zero ->
    eq M a zero \/ eq M b zero
}.

End IntegralDomain.
