LIB := -Q . Logic.Class -Q ../../Logic Logic

all: 										Eq.vo \
											Ord.vo
	touch Done

Eq.vo:										Eq.v
	coqc Eq.v 		${LIB} 

Ord.vo:										Ord.v \
											Eq.vo
	coqc Ord.v 		${LIB} 

clean :
	rm -f *.glob *.vo .*.aux Done
