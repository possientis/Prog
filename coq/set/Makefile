UTILS=Utils
CORE=Core
LANG1=Lang1

all :							${UTILS}/LEM.vo \
								${UTILS}/Decidable.vo \
								${UTILS}/Filter.vo \
								${UTILS}/Nat.vo \
								${UTILS}/Fresh.vo \
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
								${CORE}/Decidability.vo \
								${CORE}/Empty.vo \
								${CORE}/Pairing.vo \
								${CORE}/Union.vo \
								${CORE}/Intersection.vo \
								${CORE}/Powerset.vo \
								${CORE}/Rank.vo \
								${CORE}/Foundation.vo \
								${CORE}/Compatible.vo \
								${CORE}/Comprehension.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo \
								${LANG1}/Relevance.vo \
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
								${LANG1}/Comprehension.vo

${UTILS}/LEM.vo :				${UTILS}/LEM.v
	coqc ${UTILS}/LEM.v -Q ${UTILS} ${UTILS}

${UTILS}/Decidable.vo :			${UTILS}/Decidable.v
	coqc ${UTILS}/Decidable.v -Q ${UTILS} ${UTILS}

${UTILS}/Filter.vo : 			${UTILS}/Filter.v \
								${UTILS}/Decidable.vo \
								${UTILS}/LEM.vo
	coqc ${UTILS}/Filter.v -Q ${UTILS} ${UTILS}


${UTILS}/Nat.vo : 				${UTILS}/Nat.v
	coqc ${UTILS}/Nat.v -Q ${UTILS} ${UTILS}

${UTILS}/Fresh.vo :				${UTILS}/Fresh.v
	coqc ${UTILS}/Fresh.v -Q ${UTILS} ${UTILS}

${CORE}/Set.vo : 				${CORE}/Set.v
	coqc ${CORE}/Set.v -Q ${CORE} ${CORE}


${CORE}/Order.vo :				${CORE}/Order.v \
								${UTILS}/Nat.vo \
								${CORE}/Set.vo
	coqc ${CORE}/Order.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}



${CORE}/Core.vo :				${CORE}/Core.v \
								${UTILS}/Nat.vo \
								${CORE}/Set.vo \
								${CORE}/Order.vo
	coqc ${CORE}/Core.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}


${CORE}/Incl.vo :				${CORE}/Incl.v \
								${UTILS}/Nat.vo \
								${CORE}/Set.vo \
								${CORE}/Order.vo \
								${CORE}/Core.vo
	coqc ${CORE}/Incl.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}

	
${CORE}/Elem.vo :				${CORE}/Elem.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo
	coqc ${CORE}/Elem.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}
		


${CORE}/ToList.vo :				${CORE}/ToList.v \
								${UTILS}/Nat.vo \
								${CORE}/Set.vo \
								${CORE}/Order.vo \
								${CORE}/Core.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo
	coqc ${CORE}/ToList.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}
	

${CORE}/Trans.vo :				${CORE}/Trans.v \
								${CORE}/Set.vo \
								${CORE}/Order.vo \
								${CORE}/Core.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/ToList.vo
	coqc ${CORE}/Trans.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}
	

${CORE}/ElemIncl.vo :			${CORE}/ElemIncl.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/ToList.vo \
								${CORE}/Trans.vo
	coqc ${CORE}/ElemIncl.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}


${CORE}/Equal.vo :				${CORE}/Equal.v \
								${CORE}/Set.vo \
								${CORE}/Elem.vo
	coqc ${CORE}/Equal.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}
	

${CORE}/Extensionality.vo :		${CORE}/Extensionality.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/ToList.vo \
								${CORE}/Trans.vo \
								${CORE}/ElemIncl.vo \
								${CORE}/Equal.vo
	coqc ${CORE}/Extensionality.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}


${CORE}/Decidability.vo : 		${CORE}/Decidability.v \
								${UTILS}/Decidable.vo \
								${UTILS}/Filter.vo \
								${CORE}/Set.vo \
								${CORE}/Order.vo \
								${CORE}/Core.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Extensionality.vo
	coqc ${CORE}/Decidability.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}


${CORE}/Empty.vo :				${CORE}/Empty.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/ToList.vo \
								${CORE}/ElemIncl.vo \
								${CORE}/Extensionality.vo
	coqc ${CORE}/Empty.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}


${CORE}/Pairing.vo :			${CORE}/Pairing.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/ToList.vo \
								${CORE}/Extensionality.vo \
								${CORE}/Empty.vo
	coqc ${CORE}/Pairing.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}



${CORE}/Union.vo :				${CORE}/Union.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Empty.vo \
								${CORE}/ToList.vo \
								${CORE}/Extensionality.vo
	coqc ${CORE}/Union.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}


${CORE}/Intersection.vo :		${CORE}/Intersection.v \
								${UTILS}/Decidable.vo \
								${UTILS}/Filter.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Empty.vo \
								${CORE}/ToList.vo \
								${CORE}/Decidability.vo \
								${CORE}/Extensionality.vo

	coqc ${CORE}/Intersection.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}


${CORE}/Powerset.vo :			${CORE}/Powerset.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Empty.vo \
								${CORE}/ToList.vo \
								${CORE}/ElemIncl.vo \
								${CORE}/Intersection.vo \
								${CORE}/Decidability.vo \
								${CORE}/Extensionality.vo

	coqc ${CORE}/Powerset.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}


${CORE}/Rank.vo :				${CORE}/Rank.v \
								${UTILS}/Nat.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Empty.vo \
								${CORE}/ToList.vo \
								${CORE}/ElemIncl.vo \
								${CORE}/Decidability.vo \
								${CORE}/Extensionality.vo 
	
	coqc ${CORE}/Rank.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}


${CORE}/Foundation.vo :			${CORE}/Foundation.v \
								${UTILS}/Nat.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Rank.vo \
								${CORE}/Order.vo \
								${CORE}/Equal.vo \
								${CORE}/Trans.vo \
								${CORE}/Empty.vo \
								${CORE}/ElemIncl.vo \
								${CORE}/Decidability.vo \
								${CORE}/Extensionality.vo
	coqc ${CORE}/Foundation.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}

${CORE}/Compatible.vo :			${CORE}/Compatible.v \
								${CORE}/Set.vo \
								${CORE}/Equal.vo
	coqc ${CORE}/Compatible.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}

${CORE}/Comprehension.vo :		${CORE}/Comprehension.v \
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
	coqc ${CORE}/Comprehension.v -Q ${CORE} ${CORE} -Q ${UTILS} ${UTILS}




${LANG1}/Syntax.vo :			${LANG1}/Syntax.v \
								${UTILS}/Fresh.vo
	coqc ${LANG1}/Syntax.v -Q ${LANG1} ${LANG1} -Q ${UTILS} ${UTILS}


${LANG1}/Environment.vo :		${LANG1}/Environment.v \
								${CORE}/Set.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo
	coqc ${LANG1}/Environment.v -Q ${CORE} ${CORE} -Q ${LANG1} ${LANG1} -Q ${UTILS} ${UTILS}

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
	coqc ${LANG1}/Semantics.v -Q ${CORE} ${CORE} -Q ${LANG1} ${LANG1} -Q ${UTILS} ${UTILS}

${LANG1}/Relevance.vo :			${LANG1}/Relevance.v \
								${UTILS}/Nat.vo \
								${CORE}/Set.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo
	coqc ${LANG1}/Relevance.v -Q ${CORE} ${CORE} -Q ${LANG1} ${LANG1} -Q ${UTILS} ${UTILS}
					
${LANG1}/Compatible.vo :		${LANG1}/Compatible.v \
								${CORE}/Set.vo \
								${CORE}/Equal.vo \
								${CORE}/Compatible.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo \
								${LANG1}/Relevance.vo
	coqc ${LANG1}/Compatible.v -Q ${CORE} ${CORE} -Q ${LANG1} ${LANG1} -Q ${UTILS} ${UTILS}
	

${LANG1}/Incl.vo :				${LANG1}/Incl.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo
	coqc ${LANG1}/Incl.v -Q ${CORE} ${CORE} -Q ${LANG1} ${LANG1} -Q ${UTILS} ${UTILS}


${LANG1}/Trans.vo :				${LANG1}/Trans.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Semantics.vo \
								${LANG1}/Environment.vo
	coqc ${LANG1}/Trans.v -Q ${CORE} ${CORE} -Q ${LANG1} ${LANG1} -Q ${UTILS} ${UTILS}


${LANG1}/ElemIncl.vo :			${LANG1}/ElemIncl.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo
	coqc ${LANG1}/ElemIncl.v -Q ${CORE} ${CORE} -Q ${LANG1} ${LANG1} -Q ${UTILS} ${UTILS}


${LANG1}/Equal.vo :				${LANG1}/Equal.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo
	coqc ${LANG1}/Equal.v -Q ${CORE} ${CORE} -Q ${LANG1} ${LANG1} -Q ${UTILS} ${UTILS}


${LANG1}/Extensionality.vo :	${LANG1}/Extensionality.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo
	coqc ${LANG1}/Extensionality.v -Q ${CORE} ${CORE} -Q ${LANG1} ${LANG1} -Q ${UTILS} ${UTILS}


${LANG1}/Empty.vo :				${LANG1}/Empty.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo
	coqc ${LANG1}/Empty.v -Q ${CORE} ${CORE} -Q ${LANG1} ${LANG1} -Q ${UTILS} ${UTILS}


${LANG1}/Pairing.vo :			${LANG1}/Pairing.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo
	coqc ${LANG1}/Pairing.v -Q ${CORE} ${CORE} -Q ${LANG1} ${LANG1} -Q ${UTILS} ${UTILS}


${LANG1}/Union.vo :				${LANG1}/Union.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo
	coqc ${LANG1}/Union.v -Q ${CORE} ${CORE} -Q ${LANG1} ${LANG1} -Q ${UTILS} ${UTILS}


${LANG1}/Powerset.vo :			${LANG1}/Powerset.v \
								${UTILS}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/Incl.vo \
								${CORE}/Equal.vo \
								${LANG1}/Syntax.vo \
								${LANG1}/Environment.vo \
								${LANG1}/Semantics.vo
	coqc ${LANG1}/Powerset.v -Q ${CORE} ${CORE} -Q ${LANG1} ${LANG1} -Q ${UTILS} ${UTILS}


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
	
	coqc ${LANG1}/Foundation.v -Q ${CORE} ${CORE} -Q ${LANG1} ${LANG1} -Q ${UTILS} ${UTILS}

${LANG1}/Comprehension.vo :		${LANG1}/Comprehension.v \
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
	
	coqc ${LANG1}/Comprehension.v -Q ${CORE} ${CORE} -Q ${LANG1} ${LANG1} -Q ${UTILS} ${UTILS}

