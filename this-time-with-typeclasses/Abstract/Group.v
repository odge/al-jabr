Require Import
  Technology.Setoid
  Abstract.Magma
  Abstract.Semigroup
  Abstract.Monoid.

Class Group `{m : Monoid} := {
  inverse : car M -> car M ;
  inverseRespectful : Proper (eq M ==> eq M) inverse ;
  leftInverse : forall a, inverse a & a == identity ;
  rightInverse : forall a, a & inverse a == identity
}.

Add Parametric Morphism `(g : Group) : inverse with 
signature eq M ==> eq M as inverse_mor.
Proof. apply inverseRespectful. Qed.
