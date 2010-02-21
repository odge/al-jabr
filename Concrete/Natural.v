Require Import
 Technology.Setoid
 Abstract.Magma
 Abstract.Abelian
 Abstract.Semigroup.

Program Definition N : Setoid := Build_Setoid nat (fun x y => x = y) _ _ _.
Next Obligation.
unfold Relation_Definitions.reflexive.
intros; congruence.
Qed.
Next Obligation.
unfold Relation_Definitions.symmetric.
intros; congruence.
Qed.
Next Obligation.
unfold Relation_Definitions.transitive.
intros; congruence.
Qed.

Program Definition nat_magma_additive : Magma N := Build_Magma N plus _.
Next Obligation.
unfold Proper.
unfold respectful.
intros; congruence.
Qed.

Program Definition nat_magma_multiplicative : Magma N := Build_Magma N mult _.
Next Obligation.
unfold Proper.
unfold respectful.
intros; congruence.
Qed.

Require Import Arith.

Program Definition nat_abelian_additive : Abelian N nat_magma_additive := Build_Abelian N nat_magma_additive _.
Next Obligation.
apply plus_comm.
Qed.

Program Definition nat_abelian_multiplicative : Abelian N nat_magma_multiplicative := Build_Abelian N nat_magma_multiplicative _.
Next Obligation.
apply mult_comm.
Qed.

Program Definition nat_semigroup_additive : Semigroup N nat_magma_additive := Build_Semigroup N nat_magma_additive _.
Next Obligation.
rewrite plus_assoc.
reflexivity.
Qed.

Program Definition nat_semigroup_multiplicative : Semigroup N nat_magma_multiplicative := Build_Semigroup N nat_magma_multiplicative _.
Next Obligation.
rewrite mult_assoc.
reflexivity.
Qed.

