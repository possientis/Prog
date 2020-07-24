LIB := -Q . Logic.Func -Q ../../Logic Logic

all: 										Composition.vo \
											Identity.vo \
											Injective.vo \
											Replace.vo \
											Permute.vo
	touch Done

Composition.vo:								Composition.v
	coqc Composition.v 	${LIB} 


Identity.vo:								Identity.v
	coqc Identity.v 	${LIB} 


Injective.vo:								Injective.v
	coqc Injective.v 	${LIB} 


Replace.vo:									Replace.v \
											Injective.vo \
											Composition.vo
	coqc Replace.v 		${LIB}


Permute.vo:									Permute.v \
											Injective.vo \
											Composition.vo
	coqc Permute.v 		${LIB}

clean :
	rm -f *.glob *.vo .*.aux Done
