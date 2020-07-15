UTILS=Utils
CORE=Core
LANG1=Lang1
NORM=Normal

OPT=-Q ${UTILS} ${UTILS} -Q ${CORE} ${CORE} -Q ${LANG1} ${LANG1} -Q ${NORM} ${NORM}

all :							${UTILS}/LEM.vo \
								${UTILS}/Composition.vo \
								${UTILS}/Decidable.vo \
								${UTILS}/Filter.vo \
								${UTILS}/Nat.vo \
								${UTILS}/Replace.vo \
								${UTILS}/Remove.vo \
								${UTILS}/Fresh.vo \
								${UTILS}/Eq.vo \
								${UTILS}/Ord.vo \
								${UTILS}/Include.vo \
								${UTILS}/Equiv.vo \
								${UTILS}/Sort.vo \
								${UTILS}/Nub.vo \
								${UTILS}/Normal.vo \
								${CORE}/Set.vo \
								${CORE}/Order.vo \
								${CORE}/Core.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/ToList.vo \
								${CORE}/Trans.vo \
								${CORE}/ElemIncl.vo \
								${CORE}/Equal.vo \
								${CORE}/Extensionality.vo \
								${CORE}/Cons.vo \
								${CORE}/Decidability.vo \
								${CORE}/Empty.vo \
								${CORE}/Pairing.vo \
								${CORE}/Union.vo \
								${CORE}/Intersection.vo \
								${CORE}/Powerset.vo \
								${CORE}/Rank.vo \
								${CORE}/Foundation.vo \
								${CORE}/Compatible.vo \
								${CORE}/Specification.vo \
								${CORE}/Functional.vo \
								${CORE}/Replacement.vo \
								${NORM}/InListOf.vo \
								${NORM}/Map.vo \
								${NORM}/Leq.vo \
								${NORM}/Equiv.vo \
								${NORM}/Nub.vo \
								${NORM}/Sort.vo \
								${NORM}/Insert.vo \
								${NORM}/Normal.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Apply.vo \
								${LANG1}/Valid.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo \
								${LANG1}/Relevance.vo \
								${LANG1}/Substitution.vo \
								${LANG1}/Compatible.vo \
								${LANG1}/Incl.vo \
								${LANG1}/Trans.vo \
								${LANG1}/ElemIncl.vo \
								${LANG1}/Equal.vo \
								${LANG1}/Extensionality.vo \
								${LANG1}/Empty.vo \
								${LANG1}/Pairing.vo \
								${LANG1}/Union.vo \
								${LANG1}/Powerset.vo \
								${LANG1}/Foundation.vo \
								${LANG1}/Specification.vo

${UTILS}/LEM.vo :				${UTILS}/LEM.v
	coqc ${UTILS}/LEM.v 		${OPT}

${UTILS}/Composition.vo :		${UTILS}/Composition.v
	coqc ${UTILS}/Composition.v ${OPT}

${UTILS}/Decidable.vo :			${UTILS}/Decidable.v
	coqc ${UTILS}/Decidable.v 	${OPT}


${UTILS}/Filter.vo : 			${UTILS}/Filter.v \
								${UTILS}/Decidable.vo \
								${UTILS}/LEM.vo
	coqc ${UTILS}/Filter.v 		${OPT}


${UTILS}/Nat.vo : 				${UTILS}/Nat.v
	coqc ${UTILS}/Nat.v 		${OPT}

${UTILS}/Replace.vo : 			${UTILS}/Replace.v
	coqc ${UTILS}/Replace.v 	${OPT}

${UTILS}/Remove.vo : 			${UTILS}/Remove.v
	coqc ${UTILS}/Remove.v 		${OPT}

${UTILS}/Fresh.vo :				${UTILS}/Fresh.v
	coqc ${UTILS}/Fresh.v		${OPT} 

${UTILS}/Eq.vo :				${UTILS}/Eq.v
	coqc ${UTILS}/Eq.v			${OPT} 

${UTILS}/Ord.vo :				${UTILS}/Ord.v \
								${UTILS}/Eq.vo
	coqc ${UTILS}/Ord.v			${OPT} 

${UTILS}/Include.vo :			${UTILS}/Include.v
	coqc ${UTILS}/Include.v		${OPT} 

${UTILS}/Equiv.vo :				${UTILS}/Equiv.v \
								${UTILS}/Include.vo
	coqc ${UTILS}/Equiv.v		${OPT} 

${UTILS}/Sort.vo :				${UTILS}/Sort.v \
								${UTILS}/Ord.vo \
								${UTILS}/Equiv.vo
	coqc ${UTILS}/Sort.v		${OPT} 

${UTILS}/Nub.vo :				${UTILS}/Nub.v \
								${UTILS}/Eq.vo \
								${UTILS}/Equiv.vo
	coqc ${UTILS}/Nub.v			${OPT} 


${UTILS}/Normal.vo :			${UTILS}/Normal.v \
								${UTILS}/Nub.vo \
								${UTILS}/Ord.vo \
								${UTILS}/Sort.vo \
								${UTILS}/Equiv.vo
	coqc ${UTILS}/Normal.v		${OPT} 


${CORE}/Set.vo : 				${CORE}/Set.v
	coqc ${CORE}/Set.v			${OPT} 


${CORE}/Order.vo :				${CORE}/Order.v \
								${UTILS}/Nat.vo \
								${CORE}/Set.vo
	coqc ${CORE}/Order.v		${OPT} 


${CORE}/Core.vo :				${CORE}/Core.v \
								${UTILS}/Nat.vo \
								${CORE}/Set.vo \
								${CORE}/Order.vo
	coqc ${CORE}/Core.v			${OPT} 


${CORE}/Incl.vo :				${CORE}/Incl.v \
								${UTILS}/Nat.vo \
								${CORE}/Set.vo \
								${CORE}/Order.vo \
								${CORE}/Core.vo
	coqc ${CORE}/Incl.v			${OPT} 

	
${CORE}/Elem.vo :				${CORE}/Elem.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo
	coqc ${CORE}/Elem.v			${OPT} 
		

${CORE}/ToList.vo :				${CORE}/ToList.v \
								${UTILS}/Nat.vo \
								${CORE}/Set.vo \
								${CORE}/Order.vo \
								${CORE}/Core.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo
	coqc ${CORE}/ToList.v		${OPT} 
	

${CORE}/Trans.vo :				${CORE}/Trans.v \
								${CORE}/Set.vo \
								${CORE}/Order.vo \
								${CORE}/Core.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/ToList.vo
	coqc ${CORE}/Trans.v		${OPT} 
	

${CORE}/ElemIncl.vo :			${CORE}/ElemIncl.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/ToList.vo \
								${CORE}/Trans.vo
	coqc ${CORE}/ElemIncl.v		${OPT} 


${CORE}/Equal.vo :				${CORE}/Equal.v \
								${CORE}/Set.vo \
								${CORE}/Elem.vo
	coqc ${CORE}/Equal.v		${OPT} 
	

${CORE}/Extensionality.vo :		${CORE}/Extensionality.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/ToList.vo \
								${CORE}/Trans.vo \
								${CORE}/ElemIncl.vo \
								${CORE}/Equal.vo
	coqc ${CORE}/Extensionality.v ${OPT} 


${CORE}/Cons.vo :				${CORE}/Cons.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/ToList.vo \
								${CORE}/Trans.vo \
								${CORE}/Equal.vo \
								${CORE}/Extensionality.vo
	coqc ${CORE}/Cons.v ${OPT} 


${CORE}/Decidability.vo : 		${CORE}/Decidability.v \
								${UTILS}/Decidable.vo \
								${UTILS}/Filter.vo \
								${UTILS}/Eq.vo \
								${CORE}/Set.vo \
								${CORE}/Order.vo \
								${CORE}/Core.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Extensionality.vo
	coqc ${CORE}/Decidability.v	${OPT} 


${CORE}/Empty.vo :				${CORE}/Empty.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Cons.vo \
								${CORE}/Equal.vo \
								${CORE}/ToList.vo \
								${CORE}/ElemIncl.vo \
								${CORE}/Extensionality.vo
	coqc ${CORE}/Empty.v		${OPT} 


${CORE}/Pairing.vo :			${CORE}/Pairing.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Cons.vo \
								${CORE}/Equal.vo \
								${CORE}/ToList.vo \
								${CORE}/Extensionality.vo \
								${CORE}/Empty.vo
	coqc ${CORE}/Pairing.v		${OPT} 


${CORE}/Union.vo :				${CORE}/Union.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Cons.vo \
								${CORE}/Equal.vo \
								${CORE}/Empty.vo \
								${CORE}/ToList.vo \
								${CORE}/Extensionality.vo
	coqc ${CORE}/Union.v		${OPT} 


${CORE}/Intersection.vo :		${CORE}/Intersection.v \
								${UTILS}/Decidable.vo \
								${UTILS}/Filter.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Cons.vo \
								${CORE}/Equal.vo \
								${CORE}/Empty.vo \
								${CORE}/ToList.vo \
								${CORE}/Decidability.vo \
								${CORE}/Extensionality.vo
	coqc ${CORE}/Intersection.v ${OPT} 


${CORE}/Powerset.vo :			${CORE}/Powerset.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Cons.vo \
								${CORE}/Equal.vo \
								${CORE}/Empty.vo \
								${CORE}/ToList.vo \
								${CORE}/ElemIncl.vo \
								${CORE}/Intersection.vo \
								${CORE}/Decidability.vo \
								${CORE}/Extensionality.vo
	coqc ${CORE}/Powerset.v		${OPT} 


${CORE}/Rank.vo :				${CORE}/Rank.v \
								${UTILS}/Nat.vo \
								${UTILS}/Ord.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Empty.vo \
								${CORE}/ToList.vo \
								${CORE}/ElemIncl.vo \
								${CORE}/Decidability.vo \
								${CORE}/Extensionality.vo \
								${NORM}/Leq.vo 
	coqc ${CORE}/Rank.v			${OPT} 


${CORE}/Foundation.vo :			${CORE}/Foundation.v \
								${UTILS}/Nat.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Cons.vo \
								${CORE}/Rank.vo \
								${CORE}/Order.vo \
								${CORE}/Equal.vo \
								${CORE}/Trans.vo \
								${CORE}/Empty.vo \
								${CORE}/ElemIncl.vo \
								${CORE}/Decidability.vo \
								${CORE}/Extensionality.vo
	coqc ${CORE}/Foundation.v	${OPT} 


${CORE}/Compatible.vo :			${CORE}/Compatible.v \
								${CORE}/Set.vo \
								${CORE}/Equal.vo
	coqc ${CORE}/Compatible.v	${OPT} 


${CORE}/Specification.vo :		${CORE}/Specification.v \
								${UTILS}/LEM.vo \
								${UTILS}/Decidable.vo \
								${UTILS}/Filter.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo	\
								${CORE}/Equal.vo \
								${CORE}/ToList.vo \
								${CORE}/Compatible.vo \
								${CORE}/Extensionality.vo
	coqc ${CORE}/Specification.v ${OPT} 


${CORE}/Functional.vo :			${CORE}/Functional.v \
								${CORE}/Set.vo \
								${CORE}/Equal.vo
	coqc ${CORE}/Functional.v	${OPT} 


${CORE}/Replacement.vo :		${CORE}/Functional.v \
								${UTILS}/LEM.vo \
								${UTILS}/Filter.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo	\
								${CORE}/Equal.vo \
								${CORE}/ToList.vo \
								${CORE}/Functional.vo \
								${CORE}/Compatible.vo \
								${CORE}/Extensionality.vo \
								${NORM}/Normal.vo
	coqc ${CORE}/Replacement.v	${OPT}


${NORM}/InListOf.vo :			${NORM}/InListOf.v \
								${CORE}/Set.vo
	coqc ${NORM}/InListOf.v		${OPT}


${NORM}/Map.vo :				${NORM}/Map.v \
								${CORE}/Set.vo \
								${NORM}/InListOf.vo
	coqc ${NORM}/Map.v			${OPT}


${NORM}/Leq.vo :				${NORM}/Leq.v \
								${UTILS}/Ord.v \
								${CORE}/Set.vo \
								${CORE}/Decidability.vo
	coqc ${NORM}/Leq.v			${OPT} 


${NORM}/Equiv.vo :				${NORM}/Equiv.v \
								${UTILS}/Equiv.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/ToList.vo \
								${CORE}/ElemIncl.vo \
								${CORE}/Extensionality.vo \
								${NORM}/Leq.vo
	coqc ${NORM}/Equiv.v		${OPT}


${NORM}/Nub.vo :				${NORM}/Nub.v \
								${UTILS}/Nub.v \
								${CORE}/Set.vo \
								${CORE}/Rank.vo \
								${CORE}/Equal.vo \
								${NORM}/Leq.vo \
								${NORM}/Equiv.vo \
								${NORM}/InListOf.vo
	coqc ${NORM}/Nub.v			${OPT} 


${NORM}/Sort.vo :				${NORM}/Sort.v \
								${UTILS}/Sort.v \
								${CORE}/Set.vo \
								${CORE}/Rank.vo \
								${CORE}/Equal.vo \
								${NORM}/Leq.vo \
								${NORM}/Equiv.vo \
								${NORM}/Insert.vo \
								${NORM}/InListOf.vo
	coqc ${NORM}/Sort.v			${OPT} 


${NORM}/Insert.vo :				${NORM}/Insert.v \
								${UTILS}/Sort.vo \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/Cons.vo \
								${CORE}/Equal.vo \
								${CORE}/Decidability.vo \
								${NORM}/Leq.vo \
								${NORM}/Equiv.vo \
								${NORM}/InListOf.vo
	coqc ${NORM}/Insert.v		${OPT} 


${NORM}/Normal.vo :				${NORM}/Normal.v \
								${UTILS}/Nat.vo \
								${UTILS}/Normal.vo \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/Cons.vo \
								${CORE}/Rank.vo \
								${CORE}/Equal.vo \
								${CORE}/ToList.vo \
								${CORE}/Extensionality.vo \
								${NORM}/Map.vo \
								${NORM}/Nub.vo \
								${NORM}/Sort.vo \
								${NORM}/Equiv.vo \
								${NORM}/Insert.vo \
								${NORM}/InListOf.vo
	coqc ${NORM}/Normal.v		${OPT} 




${LANG1}/Syntax.vo :			${LANG1}/Syntax.v \
								${UTILS}/Fresh.vo
	coqc ${LANG1}/Syntax.v		${OPT} 

${LANG1}/Apply.vo :				${LANG1}/Apply.v \
								${UTILS}/Replace.vo
	coqc ${LANG1}/Apply.v		${OPT} 

${LANG1}/Valid.vo :				${LANG1}/Valid.v \
								${LANG1}/Syntax.vo
	coqc ${LANG1}/Valid.v		${OPT} 


${LANG1}/Environment.vo :		${LANG1}/Environment.v \
								${CORE}/Set.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo
	coqc ${LANG1}/Environment.v	${OPT} 


${LANG1}/Semantics.vo :			${LANG1}/Semantics.v \
								${UTILS}/LEM.vo \
								${UTILS}/Nat.vo \
								${UTILS}/Fresh.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Empty.vo \
								${CORE}/ElemIncl.vo \
								${CORE}/Foundation.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo
	coqc ${LANG1}/Semantics.v	${OPT} 


${LANG1}/Relevance.vo :			${LANG1}/Relevance.v \
								${UTILS}/Remove.vo \
								${CORE}/Set.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo
	coqc ${LANG1}/Relevance.v	${OPT} 
					

${LANG1}/Substitution.vo :		${LANG1}/Substitution.v \
								${UTILS}/Remove.vo \
								${UTILS}/Composition.vo \
								${CORE}/Set.vo \
								${CORE}/Equal.vo \
								${LANG1}/Valid.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Semantics.vo \
								${LANG1}/Relevance.vo \
								${LANG1}/Environment.vo
	coqc ${LANG1}/Substitution.v ${OPT} 
	
${LANG1}/Compatible.vo :		${LANG1}/Compatible.v \
								${CORE}/Set.vo \
								${CORE}/Equal.vo \
								${CORE}/Compatible.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo \
								${LANG1}/Relevance.vo
	coqc ${LANG1}/Compatible.v	${OPT} 
	

${LANG1}/Incl.vo :				${LANG1}/Incl.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo
	coqc ${LANG1}/Incl.v		${OPT} 


${LANG1}/Trans.vo :				${LANG1}/Trans.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Semantics.vo \
								${LANG1}/Environment.vo
	coqc ${LANG1}/Trans.v		${OPT} 


${LANG1}/ElemIncl.vo :			${LANG1}/ElemIncl.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo
	coqc ${LANG1}/ElemIncl.v	${OPT} 


${LANG1}/Equal.vo :				${LANG1}/Equal.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo
	coqc ${LANG1}/Equal.v		${OPT} 


${LANG1}/Extensionality.vo :	${LANG1}/Extensionality.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo
	coqc ${LANG1}/Extensionality.v ${OPT} 


${LANG1}/Empty.vo :				${LANG1}/Empty.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo
	coqc ${LANG1}/Empty.v		${OPT} 


${LANG1}/Pairing.vo :			${LANG1}/Pairing.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo
	coqc ${LANG1}/Pairing.v		${OPT} 


${LANG1}/Union.vo :				${LANG1}/Union.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo
	coqc ${LANG1}/Union.v		${OPT} 


${LANG1}/Powerset.vo :			${LANG1}/Powerset.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/Incl.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo
	coqc ${LANG1}/Powerset.v	${OPT} 


${LANG1}/Foundation.vo :		${LANG1}/Foundation.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo \
								${CORE}/Foundation.vo
	coqc ${LANG1}/Foundation.v	${OPT} 

${LANG1}/Specification.vo :		${LANG1}/Specification.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Compatible.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo \
								${LANG1}/Relevance.vo
	
	coqc ${LANG1}/Specification.v ${OPT} 

