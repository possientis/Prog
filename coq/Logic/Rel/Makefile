LIB := -Q . Logic.Rel -Q ../../Logic Logic

all: 										Properties.vo
	touch Done

Properties.vo:								Properties.v
	coqc Properties.v 	${LIB} 


clean :
	rm -f *.glob *.vo .*.aux Done
