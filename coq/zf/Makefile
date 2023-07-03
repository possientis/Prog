all:	logic.vo \
			Axiom_LEM.vo \
			lem.vo \
			set.vo \
			Axiom_Skolem.vo \
			belong.vo \
			Axiom_Empty_Set.vo \
			Axiom_Pairing.vo \
			Axiom_Union.vo \
			subset.vo	\
			Axiom_Extensionality.vo \
			Axiom_Power_Set.vo \
			empty.vo \
			pair.vo	\
			singleton.vo \
			ord_pair.vo \
			union.vo \
			power.vo

logic.vo: logic.v
	coqc logic.v
			
Axiom_LEM.vo: Axiom_LEM.v
	coqc Axiom_LEM.v

lem.vo: lem.v Axiom_LEM.vo logic.vo
	coqc lem.v

set.vo: set.v
	coqc set.v

Axiom_Skolem.vo: Axiom_Skolem.v set.vo
	coqc Axiom_Skolem.v

belong.vo:	belong.v set.vo
	coqc belong.v

Axiom_Empty_Set.vo: Axiom_Empty_Set.v set.vo belong.vo
	coqc Axiom_Empty_Set.v

Axiom_Pairing.vo: Axiom_Pairing.v set.vo belong.vo
	coqc Axiom_Pairing.v

Axiom_Union.vo: Axiom_Union.v set.vo belong.vo
	coqc Axiom_Union.v

subset.vo: subset.v belong.vo set.vo 
	coqc subset.v

Axiom_Extensionality.vo: Axiom_Extensionality.v set.vo subset.vo
	coqc Axiom_Extensionality.v

Axiom_Power_Set.vo: Axiom_Power_Set.v set.vo belong.vo subset.vo
	coqc Axiom_Power_Set.v

empty.vo: empty.v set.vo belong.vo subset.vo Axiom_Extensionality.vo \
 					Axiom_Skolem.vo Axiom_Empty_Set.vo
	coqc empty.v	

pair.vo: pair.v set.vo Axiom_Skolem.vo belong.vo Axiom_Pairing.vo \
				 subset.vo Axiom_Extensionality.vo
	coqc pair.v

singleton.vo: singleton.v set.vo belong.vo subset.vo empty.vo pair.vo
	coqc singleton.v

ord_pair.vo: ord_pair.v set.vo belong.vo pair.vo singleton.vo
	coqc ord_pair.v

union.vo: union.v set.vo Axiom_Skolem.vo belong.vo Axiom_Union.vo subset.vo \
	Axiom_Extensionality.vo empty.vo pair.vo
	coqc union.v

power.vo: power.v set.vo Axiom_Skolem.vo belong.vo subset.vo \
	Axiom_Power_Set.vo Axiom_Extensionality.vo
	coqc power.v




