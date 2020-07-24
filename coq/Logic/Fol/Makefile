LIB := -Q . Logic.Fol -Q ../../Logic Logic


all: 										Syntax.vo \
											Order.vo \
											Functor.vo \
											Congruence.vo \
											Eq.vo \
											Variable.vo \
											Free.vo \
											Dmap.vo \
											Bound.vo \
											Subformula.vo \
											Valid.vo
	touch Done

Syntax.vo:									Syntax.v
	coqc Syntax.v 		${LIB}


Order.vo:									Order.v \
											Syntax.vo
	coqc Order.v 		${LIB}


Functor.vo:									Functor.v \
											Syntax.vo
	coqc Functor.v 		${LIB}


Congruence.vo:								Congruence.v \
											Functor.vo \
											Syntax.vo
	coqc Congruence.v	${LIB}


Eq.vo:										Eq.v \
											Syntax.vo
	coqc Eq.v 		${LIB}


Variable.vo:								Variable.v \
											Syntax.vo \
											Functor.vo
	coqc Variable.v 	${LIB}


Free.vo:									Free.v \
											Syntax.vo \
											Functor.vo \
											Variable.vo \
											Congruence.vo
	coqc Free.v 		${LIB}


Dmap.vo:									Dmap.v \
											Syntax.vo
	coqc Dmap.v 		${LIB}


Bound.vo:									Bound.v \
											Free.vo \
											Syntax.vo \
											Functor.vo \
											Variable.vo
	coqc Bound.v 		${LIB}


Subformula.vo:								Subformula.v \
											Eq.vo \
											Order.vo \
											Bound.vo \
											Syntax.vo \
											Functor.vo \
											Variable.vo
	coqc Subformula.v 	${LIB}


Valid.vo:									Valid.v \
											Free.vo \
											Bound.vo \
											Syntax.vo \
											Functor.vo \
											Variable.vo \
											Subformula.vo
	coqc Valid.v 		${LIB}


clean :
	rm -f *.glob *.vo .*.aux Done
