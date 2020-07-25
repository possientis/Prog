LIB := -Q . Logic.Set -Q ../../Logic Logic

all :									Set.vo \
										Order.vo \
										Core.vo \
										Incl.vo \
										Elem.vo \
										ToList.vo \
										Trans.vo \
										ElemIncl.vo \
										Equal.vo \
										Extensionality.vo \
										Cons.vo \
										Decidable.vo \
										Empty.vo \
										Pairing.vo \
										Union.vo \
										Intersection.vo \
										Powerset.vo
	touch Done


Set.vo : 								Set.v
	coqc Set.v		${LIB}			


Order.vo : 								Order.v \
										Set.vo
	coqc Order.v		${LIB}			


Core.vo : 								Core.v \
										Set.vo \
										Order.vo
	coqc Core.v		${LIB}			


Incl.vo : 								Incl.v \
										Set.vo \
										Core.vo \
										Order.vo
	coqc Incl.v		${LIB}			


Elem.vo : 								Elem.v \
										Set.vo \
										Incl.vo
	coqc Elem.v		${LIB}			


ToList.vo : 							ToList.v \
										Set.vo \
										Core.vo \
										Incl.vo \
										Elem.vo \
										Order.vo
	coqc ToList.v		${LIB}			


Trans.vo : 								Trans.v \
										Set.vo \
										Core.vo \
										Incl.vo \
										Elem.vo \
										Order.vo \
										ToList.vo
	coqc Trans.v		${LIB}			


ElemIncl.vo : 							ElemIncl.v \
										Set.vo \
										Incl.vo \
										Elem.vo \
										ToList.vo \
										Trans.vo
	coqc ElemIncl.v		${LIB}			


Equal.vo : 								Equal.v \
										Set.vo \
										Elem.vo
	coqc Equal.v		${LIB}			


Extensionality.vo : 					Extensionality.v \
										Set.vo \
										Incl.vo \
										Elem.vo \
										Trans.vo \
										Equal.vo \
										ToList.vo \
										ElemIncl.vo
	coqc Extensionality.v	${LIB}			


Cons.vo : 								Cons.v \
										Set.vo \
										Incl.vo \
										Elem.vo \
										Trans.vo \
										Equal.vo \
										ToList.vo \
										Extensionality.vo
	coqc Cons.v		${LIB}			


Decidable.vo : 							Decidable.v \
										Set.vo \
										Order.vo \
										Core.vo \
										Incl.vo \
										Elem.vo \
										Equal.vo \
										Extensionality.vo
	coqc Decidable.v	${LIB}			


Empty.vo : 								Empty.v \
										Set.vo \
										Incl.vo \
										Elem.vo \
										Cons.vo \
										Equal.vo \
										ToList.vo \
										ElemIncl.vo \
										Extensionality.vo
	coqc Empty.v		${LIB}			



Pairing.vo : 							Pairing.v \
										Set.vo \
										Incl.vo \
										Elem.vo \
										Cons.vo \
										Equal.vo \
										Empty.vo \
										ToList.vo \
										Extensionality.vo
	coqc Pairing.v		${LIB}			


Union.vo : 								Union.v \
										Set.vo \
										Incl.vo \
										Elem.vo \
										Cons.vo \
										Equal.vo \
										Empty.vo \
										ToList.vo \
										Pairing.vo \
										Extensionality.vo
	coqc Union.v		${LIB}			


Intersection.vo : 						Intersection.v \
										Set.vo \
										Incl.vo \
										Elem.vo \
										Cons.vo \
										Equal.vo \
										Empty.vo \
										ToList.vo \
										Decidable.vo \
										Extensionality.vo
	coqc Intersection.v	${LIB}			


Powerset.vo : 							Powerset.v \
										Set.vo \
										Incl.vo \
										Elem.vo \
										Cons.vo \
										Equal.vo \
										Empty.vo \
										ToList.vo \
										ElemIncl.vo \
										Decidable.vo \
										Intersection.vo \
										Extensionality.vo
	coqc Powerset.v		${LIB}			


clean :
	rm -f *.glob *.vo .*.aux Done
