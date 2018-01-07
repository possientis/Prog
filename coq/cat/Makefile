all: 	Axiom_ProofIrrelevance.vo \
		Axiom_Extensionality.vo \
		Cast.vo \
		Category.vo \
		Eq_Category.vo \
		Category2.vo \
		Eq_Category2.vo \
		Category3.vo \
		Eq_Category3.vo \
		Category4.vo \
		Eq_Category4.vo \
		Category5.vo \
		CategoryAsCategory2.vo \
		Category2AsCategory.vo \
		CategoryAsCategory3.vo \
		Category3AsCategory.vo \
		Category2AsCategory4.vo \
		Category4AsCategory2.vo \
		Iso_CatCat2.vo \
		Iso_CatCat3.vo \
		Iso_Cat2Cat4.vo \
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

Cast.vo : Cast.v
	coqc Cast.v

Category.vo : 				Category.v
	coqc Category.v

Eq_Category.vo :			Eq_Category.v \
							Axiom_Extensionality.vo \
							Axiom_ProofIrrelevance.vo \
				 			Category.vo
	coqc Eq_Category.v


Category2.vo : 				Category2.v
	coqc Category2.v

Eq_Category2.vo :			Eq_Category2.v \
							Axiom_Extensionality.vo \
							Axiom_ProofIrrelevance.vo \
				 			Category2.vo
	coqc Eq_Category2.v


Category3.vo : 				Category3.v
	coqc Category3.v

Eq_Category3.vo :			Eq_Category3.v \
							Axiom_Extensionality.vo \
							Axiom_ProofIrrelevance.vo \
							Cast.vo \
				 			Category3.vo
	coqc Eq_Category3.v

Category4.vo : 				Category4.v
	coqc Category4.v

Eq_Category4.vo :			Eq_Category4.v \
							Axiom_Extensionality.vo \
							Axiom_ProofIrrelevance.vo \
							Cast.vo \
				 			Category4.vo
	coqc Eq_Category4.v


Category5.vo : 				Category5.v
	coqc Category5.v


CategoryAsCategory2.vo : 	CategoryAsCategory2.v \
							Category.vo \
							Category2.vo \
							Axiom_ProofIrrelevance.vo
	coqc CategoryAsCategory2.v	


Category2AsCategory.vo :	Category2AsCategory.v \
							Category2.vo \
							Category.vo
	coqc Category2AsCategory.v


CategoryAsCategory3.vo : 	CategoryAsCategory3.v \
							Category.vo \
							Category3.vo
	coqc CategoryAsCategory3.v	



Category3AsCategory.vo :	Category3AsCategory.v \
							Category3.vo \
							Category.vo
	coqc Category3AsCategory.v


Category2AsCategory4.vo :	Category2AsCategory4.v \
							Category4.vo \
							Category2.vo
	coqc Category2AsCategory4.v


Category4AsCategory2.vo :	Category4AsCategory2.v \
							Category4.vo \
							Category2.vo
	coqc Category4AsCategory2.v


Iso_CatCat2.vo :			Iso_CatCat2.v \
							Category.vo \
							Eq_Category.vo \
							Category2.vo \
							CategoryAsCategory2.vo \
							Category2AsCategory.vo
	coqc Iso_CatCat2.v

Iso_CatCat3.vo :			Iso_CatCat3.v \
							Axiom_ProofIrrelevance.vo \
							Cast.vo \
							Category.vo \
							Eq_Category.vo \
							Category3.vo \
							Eq_Category3.vo \
							CategoryAsCategory3.vo \
							Category3AsCategory.vo
	coqc Iso_CatCat3.v


Iso_Cat2Cat4.vo :			Iso_Cat2Cat4.v \
							Axiom_ProofIrrelevance.vo \
							Cast.vo \
							Category2.vo \
							Eq_Category2.vo \
							Category4.vo \
							Eq_Category4.vo \
							Category2AsCategory4.vo \
							Category4AsCategory2.vo
	coqc Iso_Cat2Cat4.v


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
