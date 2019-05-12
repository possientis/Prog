all:	   	Extensionality.vo \
			Identity.vo \
   			Composition.vo \
			Leq.vo \
			Max.vo \
			Eq.vo \
			Lam/T.vo \
			Fol/P.vo \
			Lam/Order.vo \
			Fol/Order.vo \
			Lam/Subformula.vo \
			Fol/Subformula.vo

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

Lam/T.vo:   Lam/T.v Extensionality.vo Identity.vo Composition.vo
	coqc Lam/T.v -R Lam Lam

Fol/P.vo:	Fol/P.v	Extensionality.vo Identity.vo Composition.vo
	coqc Fol/P.v -R Fol Fol

Lam/Order.vo : Lam/Order.v
	coqc Lam/Order.v -R Lam Lam

Fol/Order.vo : Fol/Order.v
	coqc Fol/Order.v -R Fol Fol

Lam/Subformula.vo : Lam/Subformula.v Lam/T.vo
	coqc Lam/Subformula.v -R Lam Lam

Fol/Subformula.vo : Fol/Subformula.v Fol/P.vo
	coqc Fol/Subformula.v -R Fol Fol

