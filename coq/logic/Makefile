all:	   	extensionality.vo \
			identity.vo \
   			composition.vo \
			T \
			P
extensionality.vo : extensionality.v
	coqc extensionality.v

identity.vo : identity.v
	coqc identity.v

composition.vo : composition.v
	coqc composition.v

T:			Lam/T.v extensionality.vo identity.vo composition.vo
			coqc Lam/T.v -R Lam Lam

P:			Fol/P.v	extensionality.vo identity.vo composition.vo
			coqc Fol/P.v -R Fol Fol


