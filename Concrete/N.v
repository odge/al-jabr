Require Import
 Technology.FirstClassSetoid
 Abstract.Algebra.

Require Import Arith.

Program Definition N : Setoid := Build_Setoid nat (fun x y => x = y) (fun x y => x <> y) _ _ _ _.
Next Obligation.
unfold reflexive.
congruence.
Defined.
Next Obligation.
unfold symmetric.
congruence.
Defined.
Next Obligation.
unfold transitive.
congruence.
Defined.

