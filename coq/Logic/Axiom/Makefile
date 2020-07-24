LIB := -Q . Logic.Axiom -Q ../../Logic Logic

all: 										Extensionality.vo
	touch Done

Extensionality.vo:							Extensionality.v
	coqc Extensionality.v	${LIB} 


clean :
	rm -f *.glob *.vo .*.aux Done
