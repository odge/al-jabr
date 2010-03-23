Require Import
  Technology.FirstClassSetoid
  Abstract.Magma
  Abstract.Semigroup
  Abstract.Abelian
  Abstract.Monoid
  Abstract.Group
  Abstract.Ring
  Machines.Sigma.
Require Import Arith List.

Section Sigma.
Context `(car : Setoid).
Context `(R : Ring car).

Parameter inj : nat -> car.

Axiom C : nat -> nat -> nat.

Lemma C_prop_1 {n k} : C (S n) (S k) = plus (C n (S k)) (C n k).
Admitted.

Lemma C_prop_2 {n} : C n 0 = 1.
Admitted.

Lemma C_prop_3 {n} : C n n = 1.
Admitted.

Theorem binomial {x n} : (one + x) ^ n == @Σ _ _ _ _ (ι n) (fun k => inj (C n k) * x ^ k).
Admitted.
