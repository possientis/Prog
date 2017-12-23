all: 	Axiom_ProofIrrelevance.vo \
		Axiom_Extensionality.vo \
		Category.vo \
		Eq_Category.vo \
		Category2.vo \
		Category2AsCategory.vo \
		CategoryAsCategory2.vo \
		Monoid.vo	\
		Preorder.vo \
		MonoidAsCategory.vo \
		natAsMonoid.vo	\
		natAsPreorder.vo\
		natAsCategory.vo \
		ConvoyPattern.vo \
		DecidableEq.vo \
		Rewrite.vo \
		PreorderAsCategory.vo \
		natPreorderAsCategory.vo



Axiom_ProofIrrelevance.vo :	Axiom_ProofIrrelevance.v
	coqc Axiom_ProofIrrelevance.v


Axiom_Extensionality.vo : 	Axiom_Extensionality.v
	coqc Axiom_Extensionality.v


Category.vo : 				Category.v
	coqc Category.v


Eq_Category.vo :			Eq_Category.v \
							Axiom_Extensionality.vo \
							Axiom_ProofIrrelevance.vo \
				 			Category.vo
	coqc Eq_Category.v


Category2.vo : 				Category2.v
	coqc Category2.v


Category2AsCategory.vo :	Category2AsCategory.v \
							Category2.vo \
							Category.v
	coqc Category2AsCategory.v


CategoryAsCategory2.vo : 	CategoryAsCategory2.v \
							Category.vo \
							Eq_Category.vo \
							Category2.vo \
							Category2AsCategory.vo
	coqc CategoryAsCategory2.v	


Monoid.vo : 				Monoid.v
	coqc Monoid.v


Preorder.vo : 				Preorder.v
	coqc Preorder.v


MonoidAsCategory.vo: 		MonoidAsCategory.v \
							Monoid.vo \
							Category.vo
	coqc MonoidAsCategory.v


natAsMonoid.vo : 			natAsMonoid.v \
							Monoid.vo
	coqc natAsMonoid.v


natAsPreorder.vo : 			natAsPreorder.v \
							Preorder.vo
	coqc natAsPreorder.v


natAsCategory.vo : 			natAsCategory.v \
							Category.vo \
							natAsMonoid.vo \
							MonoidAsCategory.vo 
	coqc natAsCategory.v


ConvoyPattern.vo : 			ConvoyPattern.v
	coqc ConvoyPattern.v


DecidableEq.vo : 			DecidableEq.v
	coqc DecidableEq.v


Rewrite.vo : 				Rewrite.v
	coqc Rewrite.v


PreorderAsCategory.vo : 	PreorderAsCategory.v \
							Category.vo \
							Preorder.vo \
							Axiom_ProofIrrelevance.vo
	coqc PreorderAsCategory.v


natPreorderAsCategory.vo : 	natPreorderAsCategory.v \
							Category.vo \
							PreorderAsCategory.vo \
							natAsPreorder.vo	
	coqc natPreorderAsCategory.v
