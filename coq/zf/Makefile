all:	Axiom_LEM.vo \
			Axiom_Skolem.vo \
			set.vo \
			belong.vo \
			Axiom_Empty_Set.vo \
			subset.vo	\
			Axiom_Extensionality.vo \
			empty.vo
			
Axiom_LEM.vo: Axiom_LEM.v
	coqc Axiom_LEM.v

Axiom_Skolem.vo: Axiom_Skolem.v
	coqc Axiom_Skolem.v

set.vo: set.v
	coqc set.v

belong.vo:	belong.v set.vo
	coqc belong.v

Axiom_Empty_Set.vo: Axiom_Empty_Set.v
	coqc Axiom_Empty_Set.v

subset.vo: subset.v belong.vo set.vo 
	coqc subset.v

Axiom_Extensionality.vo: Axiom_Extensionality.v subset.vo set.vo
	coqc Axiom_Extensionality.v

empty.vo: empty.v set.vo belong.vo subset.vo Axiom_Extensionality.vo \
 					Axiom_Skolem.vo Axiom_Empty_Set.vo
	coqc empty.v	



