LIB := -Q . Logic.Nat -Q ../../Logic Logic

all: 										Leq.vo \
											Max.vo
	touch Done

Leq.vo:										Leq.v
	coqc Leq.v 		${LIB} 


Max.vo:										Max.v
	coqc Max.v 		${LIB} 

clean :
	rm -f *.glob *.vo .*.aux Done
