all:	Category.vo \
		Category2.vo \
		Monoid.vo	\
		MonoidAsCategory.vo \
		natAsMonoid.vo	\
		natAsCategory.vo \
		Category2AsCategory.vo \
		Axiom_ProofIrrelevance.vo
		
Category.vo : Category.v
	coqc Category.v

Category2.vo : Category2.v
	coqc Category2.v

Monoid.vo : Monoid.v
	coqc Monoid.v

MonoidAsCategory.vo: MonoidAsCategory.v Monoid.vo Category.vo
	coqc MonoidAsCategory.v

natAsMonoid.vo : natAsMonoid.v Monoid.vo
	coqc natAsMonoid.v

natAsCategory.vo : natAsCategory.v Category.vo natAsMonoid.vo MonoidAsCategory.vo 
	coqc natAsCategory.v

Category2AsCategory.vo : Category2AsCategory.v Category2.vo Category.v
	coqc Category2AsCategory.v

Axiom_ProofIrrelevance.vo : Axiom_ProofIrrelevance.v
	coqc Axiom_ProofIrrelevance.v
