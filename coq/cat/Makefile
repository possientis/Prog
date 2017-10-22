all:	Category.vo \
		Monoid.vo	\
		natAsMonoid.vo	\
		MonoidAsCategory.vo \
		natAsCategory.vo
		
Category.vo : Category.v
	coqc Category.v

Monoid.vo : Monoid.v
	coqc Monoid.v

natAsMonoid.vo : natAsMonoid.v Monoid.vo
	coqc natAsMonoid.v

MonoidAsCategory.vo: MonoidAsCategory.v Monoid.vo Category.vo
	coqc MonoidAsCategory.v

natAsCategory.vo : natAsCategory.v Category.vo natAsMonoid.vo MonoidAsCategory.vo 
	coqc natAsCategory.v


