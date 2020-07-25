LIB := -Q . Logic.Axiom -Q ../../Logic Logic

all: 										Extensionality.vo \
											LEM.vo \
											Decidable.vo
	touch Done

Extensionality.vo:							Extensionality.v
	coqc Extensionality.v	${LIB} 


LEM.vo :									LEM.v
	coqc LEM.v		${LIB}

Decidable.vo :								Decidable.v \
											LEM.vo
	coqc Decidable.v	${LIB}


clean :
	rm -f *.glob *.vo .*.aux Done
