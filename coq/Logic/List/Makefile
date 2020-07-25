LIB := -Q . Logic.List -Q ../../Logic Logic 

all: 										In.vo \
											Nil.vo \
											Concat.vo \
											Include.vo \
											InjectiveOn.vo \
											Equiv.vo \
											Append.vo \
											Coincide.vo \
											Intersect.vo \
											Difference.vo \
											Replace.vo \
											Remove.vo \
											Nub.vo \
											Sort.vo \
											Normal.vo \
											Filter.vo
	touch Done

In.vo:										In.v
	coqc In.v 		${LIB} 


Nil.vo:										Nil.v \
											In.vo
	coqc Nil.v 		${LIB} 


Concat.vo:									Concat.v \
											In.vo
	coqc Concat.v 		${LIB} 


Include.vo:								    Include.v \
											Concat.vo \
											In.vo
	coqc Include.v 		${LIB} 


InjectiveOn.vo:								InjectiveOn.v \
											In.vo \
											Include.vo
	coqc InjectiveOn.v 	${LIB} 


Equiv.vo:								    Equiv.v \
											In.vo \
											Include.vo
	coqc Equiv.v 		${LIB} 


Append.vo:								    Append.v \
											In.vo \
											Equiv.vo
	coqc Append.v 		${LIB} 


Coincide.vo:								Coincide.v \
											In.vo \
											Include.vo
	coqc Coincide.v		${LIB} 


Intersect.vo:								Intersect.v \
											In.vo \
											Nil.vo \
											Equiv.vo \
											Concat.vo \
											Append.vo \
											Include.vo
	coqc Intersect.v	${LIB}


Difference.vo:								Difference.v \
											In.vo \
											Equiv.vo \
											Concat.vo \
											Include.vo \
											Intersect.vo
	coqc Difference.v	${LIB}


Replace.vo:									Replace.v \
											In.vo \
											Coincide.vo \
											InjectiveOn.vo
	coqc Replace.v		${LIB}


Remove.vo:									Remove.v \
											In.vo \
											Include.vo \
											InjectiveOn.vo \
											Difference.vo
	coqc Remove.v		${LIB}


Nub.vo:								    	Nub.v \
											In.vo \
											Equiv.vo
	coqc Nub.v 		${LIB} 


Sort.vo:								    Sort.v \
											In.vo \
											Equiv.vo
	coqc Sort.v 		${LIB} 


Normal.vo:								    Normal.v \
											In.vo \
											Nub.vo \
											Sort.vo \
											Equiv.vo
	coqc Normal.v 		${LIB} 


Filter.vo:									Filter.v \
											In.vo \
											Nil.vo
	coqc Filter.v		${LIB} 


clean :
	rm -f *.glob *.vo .*.aux Done
