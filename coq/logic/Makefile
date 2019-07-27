all:	   			Extensionality.vo \
					Identity.vo \
   					Composition.vo \
					Coincide.vo \
					Leq.vo \
					Max.vo \
					Map.vo \
					Eq.vo \
					Relation.vo \
					Replace.vo \
					Permute.vo \
					Injective.vo \
					Remove.vo \
					Include.vo \
					Lam/T.vo \
					Fol/P.vo \
					Lam/Order.vo \
					Fol/Order.vo \
					Lam/Subformula.vo \
					Fol/Subformula.vo \
					Lam/Congruence.vo \
					Fol/Congruence.vo \
					Lam/Variable.vo \
					Fol/Variable.vo \
					Lam/Free.vo \
					Fol/Free.vo \
					Lam/Bound.vo \
					Fol/Bound.vo

Extensionality.vo : Extensionality.v
	coqc Extensionality.v

Identity.vo : 		Identity.v
	coqc Identity.v

Composition.vo : 	Composition.v
	coqc Composition.v

Coincide.vo : 		Coincide.v
	coqc Coincide.v

Leq.vo : 			Leq.v
	coqc Leq.v

Max.vo : 			Max.v
	coqc Max.v

Map.vo : 			Map.v
	coqc Map.v

Eq.vo : 			Eq.v
	coqc Eq.v

Relation.vo : 		Relation.v
	coqc Relation.v

Replace.vo : 		Replace.v \
					Eq.vo \
					Identity.vo \
					Injective.vo \
					Coincide.vo \
					Composition.vo \
					Extensionality.vo
	coqc Replace.v

Permute.vo : 		Permute.v \
					Eq.vo \
					Replace.vo \
					Coincide.vo \
					Injective.vo \
					Composition.vo \
					Extensionality.vo
	coqc Permute.v

Injective.vo : 		Injective.v \
					Composition.vo \
					Include.vo
	coqc Injective.v

Remove.vo :			Remove.v \
					Eq.vo \
					Include.vo \
					Injective.vo
	coqc Remove.v

Include.vo :		Include.v 
	coqc Include.v

Lam/T.vo:   		Lam/T.v \
					Eq.vo \
					Extensionality.vo \
					Identity.vo \
					Composition.vo
	coqc Lam/T.v -R Lam Lam

Fol/P.vo:			Fol/P.v	\
					Eq.vo \
					Extensionality.vo \
					Identity.vo \
					Composition.vo
	coqc Fol/P.v -R Fol Fol

Lam/Order.vo : 		Lam/Order.v \
					Lam/T.vo
	coqc Lam/Order.v -R Lam Lam

Fol/Order.vo : 		Fol/Order.v \
					Fol/P.vo
	coqc Fol/Order.v -R Fol Fol

Lam/Subformula.vo :	Lam/Subformula.v \
					Eq.vo \
					Leq.vo \
					Max.vo \
					Lam/T.vo \
					Lam/Order.vo \
					Lam/Bound.vo \
					Lam/Variable.vo
	coqc Lam/Subformula.v -R Lam Lam

Fol/Subformula.vo : Fol/Subformula.v \
					Eq.vo \
					Leq.vo \
					Max.vo \
					Fol/P.vo \
					Fol/Order.vo \
					Fol/Bound.vo \
					Fol/Variable.vo
	coqc Fol/Subformula.v -R Fol Fol

Lam/Congruence.vo : Lam/Congruence.v \
					Relation.vo \
					Lam/T.vo
	coqc Lam/Congruence.v -R Lam Lam

Fol/Congruence.vo : Fol/Congruence.v \
					Relation.vo \
					Fol/P.vo
	coqc Fol/Congruence.v -R Fol Fol

Lam/Variable.vo :	Lam/Variable.v \
					Eq.vo \
					Map.vo \
					Permute.vo \
					Replace.vo \
					Coincide.vo \
					Composition.vo \
					Lam/T.vo
	coqc Lam/Variable.v -R Lam Lam 
					
Fol/Variable.vo :	Fol/Variable.v \
					Eq.vo \
					Map.vo \
					Permute.vo \
					Replace.vo \
					Coincide.vo \
					Composition.vo \
					Fol/P.vo
	coqc Fol/Variable.v -R Fol Fol

Lam/Free.vo :		Lam/Free.v \
					Eq.vo \
					Map.vo \
					Remove.vo \
					Replace.vo \
					Include.vo \
					Coincide.vo \
					Relation.vo \
					Injective.vo \
					Lam/T.vo \
					Lam/Variable.vo \
					Lam/Congruence.vo
	coqc Lam/Free.v -R Lam Lam

Fol/Free.vo :		Fol/Free.v \
					Eq.vo \
					Map.vo \
					Remove.vo \
					Replace.vo \
					Include.vo \
					Coincide.vo \
					Relation.vo \
					Injective.vo \
					Fol/P.vo \
					Fol/Variable.vo \
					Fol/Congruence.vo
	coqc Fol/Free.v -R Fol Fol

Lam/Bound.vo :		Lam/Bound.v \
					Eq.vo \
					Remove.vo \
					Include.vo \
					Lam/T.vo \
					Lam/Free.vo \
					Lam/Variable.vo
	coqc Lam/Bound.v -R Lam Lam

Fol/Bound.vo :		Fol/Bound.v \
					Eq.vo \
					Remove.vo \
					Include.vo \
					Fol/P.vo \
					Fol/Free.vo \
					Fol/Variable.vo
	coqc Fol/Bound.v -R Fol Fol
