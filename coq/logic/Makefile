all:	   	extensionality.vo \
			identity.vo \
   			composition.vo \
			le.vo \
			max.vo \
			Lam/T.vo \
			Fol/P.vo \
			Lam/order.vo \
			Fol/order.vo \
			Lam/subformula.vo \
			Fol/subformula.vo

extensionality.vo : extensionality.v
	coqc extensionality.v

identity.vo : identity.v
	coqc identity.v

composition.vo : composition.v
	coqc composition.v

le.vo : le.v
	coqc le.v

max.vo : max.v
	coqc max.v

Lam/T.vo:   Lam/T.v extensionality.vo identity.vo composition.vo
	coqc Lam/T.v -R Lam Lam

Fol/P.vo:	Fol/P.v	extensionality.vo identity.vo composition.vo
	coqc Fol/P.v -R Fol Fol

Lam/order.vo : Lam/order.v
	coqc Lam/order.v -R Lam Lam

Fol/order.vo : Fol/order.v
	coqc Fol/order.v -R Fol Fol

Lam/subformula.vo : Lam/subformula.v Lam/T.vo
	coqc Lam/subformula.v -R Lam Lam

Fol/subformula.vo : Fol/subformula.v Fol/P.vo
	coqc Fol/subformula.v -R Fol Fol

