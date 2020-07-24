LIB := -Q . Logic.Class -Q ../../Logic Logic

all: 										Eq.vo
	touch Done

Eq.vo:										Eq.v
	coqc Eq.v 		${LIB} 


clean :
	rm -f *.glob *.vo .*.aux Done
