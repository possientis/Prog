LIB := -Q . Logic.Nat -Q ../../Logic Logic

all: 										Eq.vo \
											Leq.vo \
											Max.vo \
											Weaken.vo \
											Plus.vo \
											Maximum.vo \
											Minimal.vo \
											Seq.vo \
											Fresh.vo
	touch Done

Eq.vo:										Eq.v
	coqc Eq.v 		${LIB} 


Leq.vo:										Leq.v \
											Eq.vo
	coqc Leq.v 		${LIB} 


Max.vo:										Max.v
	coqc Max.v 		${LIB} 


Weaken.vo:									Weaken.v
	coqc Weaken.v 		${LIB} 


Plus.vo:									Plus.v
	coqc Plus.v 		${LIB} 


Maximum.vo:									Maximum.v \
											Max.vo
	coqc Maximum.v 		${LIB} 


Minimal.vo:									Minimal.v
	coqc Minimal.v 		${LIB} 


Seq.vo:										Seq.v \
											Leq.vo
	coqc Seq.v 		${LIB} 


Fresh.vo:									Fresh.v
	coqc Fresh.v 		${LIB} 


clean :
	rm -f *.glob *.vo .*.aux Done
