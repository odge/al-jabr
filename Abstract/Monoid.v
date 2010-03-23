Require Import
  Technology.FirstClassSetoid
  Technology.Tag
  Abstract.Magma.

Set Automatic Introduction.

Delimit Scope algebra_scope with algebra.
Open Scope algebra_scope.

Class Monoid `(M : Magma) := {
  identity ;
  leftIdentity : forall x, identity & x == x ;
  rightIdentity : forall x, x & identity == x
}.

Notation "'zero'" := (@identity Additive _ _ _) : algebra_scope.
Notation "'one'" := (@identity Multiplicative _ _ _) : algebra_scope.

Fixpoint expt {S} `{M : Monoid Multiplicative S} (m : S) (n : nat) : S :=
  match n with
    | O => one
    | S n => m * expt m n
  end.
Infix "^" := expt : algebra_scope.

(** tests **

Theorem monoid_test (S : Setoid) `(A : Monoid Additive S) `(M : Monoid Multiplicative S) :
  zero (x) one == zero (+) zero.
intros.
rewrite leftIdentity.
rewrite rightIdentity.
reflexivity.
Qed.

** **)
