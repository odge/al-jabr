coq: Technology/Setoid.vo Technology/Nonzero.vo Abstract/Magma.vo Abstract/Abelian.vo Abstract/Semigroup.vo Abstract/Monoid.vo Abstract/Group.vo Abstract/Ring.vo Abstract/IntegralDomain.vo Abstract/Field.vo
	echo "done"

Technology/Setoid.vo: Technology/Setoid.v
	coqc -R Technology Technology -R Abstract Abstract Technology/Setoid.v

Technology/Nonzero.vo: Technology/Nonzero.v
	coqc -R Technology Technology -R Abstract Abstract Technology/Nonzero.v

Abstract/Magma.vo: Abstract/Magma.v Technology/Setoid.vo Technology/Nonzero.vo
	coqc -R Technology Technology -R Abstract Abstract Abstract/Magma.v

Abstract/Semigroup.vo: Abstract/Semigroup.v Technology/Setoid.vo Technology/Nonzero.vo Abstract/Magma.vo
	coqc -R Technology Technology -R Abstract Abstract Abstract/Semigroup.v

Abstract/Abelian.vo: Abstract/Abelian.v Technology/Setoid.vo Technology/Nonzero.vo Abstract/Magma.vo
	coqc -R Technology Technology -R Abstract Abstract Abstract/Abelian.v

Abstract/Monoid.vo: Abstract/Monoid.v Technology/Setoid.vo Technology/Nonzero.vo Abstract/Magma.vo Abstract/Semigroup.vo
	coqc -R Technology Technology -R Abstract Abstract Abstract/Monoid.v

Abstract/Group.vo: Abstract/Group.v Technology/Setoid.vo Technology/Nonzero.vo Abstract/Magma.vo Abstract/Semigroup.vo Abstract/Monoid.vo
	coqc -R Technology Technology -R Abstract Abstract Abstract/Group.v

Abstract/Ring.vo: Abstract/Ring.v Technology/Setoid.vo Technology/Nonzero.vo Abstract/Magma.vo Abstract/Semigroup.vo Abstract/Monoid.vo Abstract/Group.vo
	coqc -R Technology Technology -R Abstract Abstract Abstract/Ring.v

Abstract/IntegralDomain.vo: Abstract/IntegralDomain.v Technology/Setoid.vo Technology/Nonzero.vo Abstract/Magma.vo Abstract/Semigroup.vo Abstract/Monoid.vo Abstract/Group.vo Abstract/IntegralDomain.vo
	coqc -R Technology Technology -R Abstract Abstract Abstract/IntegralDomain.v

Abstract/Field.vo: Abstract/Field.v Technology/Setoid.vo Technology/Nonzero.vo Abstract/Magma.vo Abstract/Semigroup.vo Abstract/Monoid.vo Abstract/Group.vo Abstract/Ring.vo
	coqc -R Technology Technology -R Abstract Abstract Abstract/Field.v
