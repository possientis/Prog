FOL=Fol
LAM=Lam
OPT=-Q ${FOL} ${FOL} -Q ${LAM} ${LAM}

all:	   						Extensionality.vo \
								Identity.vo \
   								Composition.vo \
								Coincide.vo \
								Leq.vo \
								Max.vo \
								Map.vo \
								Eq.vo \
								Relation.vo \
								Replace.vo \
								Permute.vo \
								Injective.vo \
								Remove.vo \
								Difference.vo \
								Intersect.vo \
								Include.vo \
								${LAM}/T.vo \
								${FOL}/P.vo \
								${LAM}/Order.vo \
								${FOL}/Order.vo \
								${LAM}/Subformula.vo \
								${FOL}/Subformula.vo \
								${LAM}/Congruence.vo \
								${FOL}/Congruence.vo \
								${LAM}/Variable.vo \
								${FOL}/Variable.vo \
								${LAM}/Free.vo \
								${FOL}/Free.vo \
								${LAM}/Bound.vo \
								${FOL}/Bound.vo \
								${LAM}/Valid.vo \
								${FOL}/Valid.vo \
								${LAM}/Dmap.vo \
								${FOL}/Dmap.vo \
								${LAM}/Subst.vo \
								${LAM}/Replace.vo

Extensionality.vo : 			Extensionality.v
	coqc Extensionality.v

Identity.vo : 					Identity.v
	coqc Identity.v

Composition.vo : 				Composition.v
	coqc Composition.v

Coincide.vo : 					Coincide.v
	coqc Coincide.v

Leq.vo : 						Leq.v
	coqc Leq.v

Max.vo : 						Max.v
	coqc Max.v

Map.vo : 						Map.v
	coqc Map.v

Eq.vo : 						Eq.v
	coqc Eq.v

Relation.vo : 					Relation.v
	coqc Relation.v

Replace.vo : 					Replace.v \
								Eq.vo \
								Identity.vo \
								Injective.vo \
								Coincide.vo \
								Composition.vo \
								Extensionality.vo
	coqc Replace.v


Permute.vo : 					Permute.v \
								Eq.vo \
								Replace.vo \
								Coincide.vo \
								Injective.vo \
								Composition.vo \
								Extensionality.vo
	coqc Permute.v



Injective.vo : 					Injective.v \
								Composition.vo \
								Include.vo
	coqc Injective.v


Remove.vo :						Remove.v \
								Eq.vo \
								Include.vo \
								Injective.vo
	coqc Remove.v



Difference.vo :					Difference.v \
								Eq.vo
	coqc Difference.v



Intersect.vo :					Intersect.v \
								Eq.vo
	coqc Intersect.v



Include.vo :					Include.v 
	coqc Include.v

${LAM}/T.vo:   					${LAM}/T.v \
								Eq.vo \
								Extensionality.vo \
								Identity.vo \
								Composition.vo
	coqc ${LAM}/T.v				${OPT} 




${FOL}/P.vo:					${FOL}/P.v	\
								Eq.vo \
								Extensionality.vo \
								Identity.vo \
								Composition.vo
	coqc ${FOL}/P.v				${OPT} 



${LAM}/Order.vo : 				${LAM}/Order.v \
								${LAM}/T.vo
	coqc ${LAM}/Order.v			${OPT} 



${FOL}/Order.vo : 				${FOL}/Order.v \
								${FOL}/P.vo
	coqc ${FOL}/Order.v			${OPT} 



${LAM}/Subformula.vo :			${LAM}/Subformula.v \
								Eq.vo \
								Leq.vo \
								Max.vo \
								Include.vo \
								${LAM}/T.vo \
								${LAM}/Order.vo \
								${LAM}/Bound.vo \
								${LAM}/Variable.vo
	coqc ${LAM}/Subformula.v	${OPT} 




${FOL}/Subformula.vo : 			${FOL}/Subformula.v \
								Eq.vo \
								Leq.vo \
								Max.vo \
								Include.vo \
								${FOL}/P.vo \
								${FOL}/Order.vo \
								${FOL}/Bound.vo \
								${FOL}/Variable.vo
	coqc ${FOL}/Subformula.v	${OPT} 


${LAM}/Congruence.vo : 			${LAM}/Congruence.v \
								Relation.vo \
								${LAM}/T.vo
	coqc ${LAM}/Congruence.v	${OPT} 



${FOL}/Congruence.vo : 			${FOL}/Congruence.v \
								Relation.vo \
								${FOL}/P.vo
	coqc ${FOL}/Congruence.v	${OPT} 




${LAM}/Variable.vo :			${LAM}/Variable.v \
								Eq.vo \
								Map.vo \
								Permute.vo \
								Replace.vo \
								Coincide.vo \
								Composition.vo \
								${LAM}/T.vo
	coqc ${LAM}/Variable.v		${OPT} 
	

				

${FOL}/Variable.vo :			${FOL}/Variable.v \
								Eq.vo \
								Map.vo \
								Permute.vo \
								Replace.vo \
								Coincide.vo \
								Composition.vo \
								${FOL}/P.vo
	coqc ${FOL}/Variable.v     ${OPT}


${LAM}/Free.vo :				${LAM}/Free.v \
								Eq.vo \
								Map.vo \
								Remove.vo \
								Replace.vo \
								Include.vo \
								Coincide.vo \
								Relation.vo \
								Injective.vo \
								Difference.vo \
								Composition.vo \
								${LAM}/T.vo \
								${LAM}/Subst.vo \
								${LAM}/Variable.vo \
								${LAM}/Congruence.vo
	coqc ${LAM}/Free.v			${OPT} 



${FOL}/Free.vo :				${FOL}/Free.v \
								Eq.vo \
								Map.vo \
								Remove.vo \
								Replace.vo \
								Include.vo \
								Coincide.vo \
								Relation.vo \
								Injective.vo \
								${FOL}/P.vo \
								${FOL}/Variable.vo \
								${FOL}/Congruence.vo
	coqc ${FOL}/Free.v			${OPT} 




${LAM}/Bound.vo :				${LAM}/Bound.v \
								Eq.vo \
								Remove.vo \
								Include.vo \
								${LAM}/T.vo \
								${LAM}/Free.vo \
								${LAM}/Variable.vo
	coqc ${LAM}/Bound.v			${OPT} 




${FOL}/Bound.vo :				${FOL}/Bound.v \
								Eq.vo \
								Remove.vo \
								Include.vo \
								${FOL}/P.vo \
								${FOL}/Free.vo \
								${FOL}/Variable.vo
	coqc ${FOL}/Bound.v			${OPT} 




${LAM}/Valid.vo :				${LAM}/Valid.v \
								Eq.vo \
								Map.vo \
								Remove.vo \
								Replace.vo \
								Include.vo \
								Coincide.vo \
								Injective.vo \
								Composition.vo \
								${LAM}/T.vo \
								${LAM}/Free.vo \
								${LAM}/Bound.vo \
								${LAM}/Variable.vo \
								${LAM}/Subformula.vo
	coqc ${LAM}/Valid.v			${OPT} 

${FOL}/Valid.vo :				${FOL}/Valid.v \
								Eq.vo \
								Map.vo \
								Remove.vo \
								Replace.vo \
								Include.vo \
								Coincide.vo \
								Injective.vo \
								Composition.vo \
								${FOL}/P.vo \
								${FOL}/Free.vo \
								${FOL}/Bound.vo \
								${FOL}/Variable.vo \
								${FOL}/Subformula.vo
	coqc ${FOL}/Valid.v			${OPT} 


${LAM}/Dmap.vo :				${LAM}/Dmap.v \
								Eq.vo \
								Map.vo \
								Identity.vo \
								Extensionality.vo \
								${LAM}/T.vo
	coqc ${LAM}/Dmap.v			${OPT} 


${FOL}/Dmap.vo :				${FOL}/Dmap.v \
								Eq.vo \
								Map.vo \
								Identity.vo \
								Extensionality.vo \
								${FOL}/P.vo
	coqc ${FOL}/Dmap.v			${OPT} 


${LAM}/Subst.vo :				${LAM}/Subst.v \
								Eq.vo \
								${LAM}/T.vo
	coqc ${LAM}/Subst.v			${OPT} 


${LAM}/Replace.vo :				${LAM}/Replace.v \
								Eq.vo \
								${LAM}/T.vo
	coqc ${LAM}/Replace.v		${OPT} 

