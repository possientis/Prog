all:	   	Extensionality.vo \
			Identity.vo \
   			Composition.vo \
			Leq.vo \
			Max.vo \
			Eq.vo \
			Relation.vo \
			Lam/T.vo \
			Fol/P.vo \
			Lam/Order.vo \
			Fol/Order.vo \
			Lam/Subformula.vo \
			Fol/Subformula.vo \
			Lam/Congruence.vo \
			Fol/Congruence.vo

Extensionality.vo : Extensionality.v
	coqc Extensionality.v

Identity.vo : Identity.v
	coqc Identity.v

Composition.vo : Composition.v
	coqc Composition.v

Leq.vo : Leq.v
	coqc Leq.v

Max.vo : Max.v
	coqc Max.v

Eq.vo : Eq.v
	coqc Eq.v

Relation.vo : Relation.v
	coqc Relation.v

Lam/T.vo:   Lam/T.v Eq.vo Extensionality.vo Identity.vo Composition.vo
	coqc Lam/T.v -R Lam Lam

Fol/P.vo:	Fol/P.v	Eq.vo Extensionality.vo Identity.vo Composition.vo
	coqc Fol/P.v -R Fol Fol

Lam/Order.vo : Lam/Order.v Lam/T.vo
	coqc Lam/Order.v -R Lam Lam

Fol/Order.vo : Fol/Order.v Fol/P.vo
	coqc Fol/Order.v -R Fol Fol

Lam/Subformula.vo : Lam/Subformula.v \
					Eq.vo \
					Leq.vo \
					Max.vo \
					Lam/T.vo \
					Lam/Order.vo
	coqc Lam/Subformula.v -R Lam Lam

Fol/Subformula.vo : Fol/Subformula.v \
					Eq.vo \
					Leq.vo \
					Max.vo \
					Fol/P.vo \
					Fol/Order.vo
	coqc Fol/Subformula.v -R Fol Fol

Lam/Congruence.vo : Lam/Congruence.v \
					Relation.vo \
					Lam/T.vo
	coqc Lam/Congruence.v -R Lam Lam

Fol/Congruence.vo : Fol/Congruence.v \
					Relation.vo \
					Fol/P.vo
	coqc Fol/Congruence.v -R Fol Fol

