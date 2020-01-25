CORE=Core
SEM=Semantics

all :							${CORE}/Nat.vo \
								${CORE}/LEM.vo \
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
								${CORE}/Filter.vo \
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
								${CORE}/Fresh.vo \
								${CORE}/Syntax.vo \
								${CORE}/Environment.vo \
								${CORE}/Semantics.vo \
								${SEM}/Incl.vo \
								${SEM}/Trans.vo \
								${SEM}/ElemIncl.vo \
								${SEM}/Equal.vo \
								${SEM}/Extensionality.vo \
								${SEM}/Empty.vo \
								${SEM}/Pairing.vo \
								${SEM}/Union.vo \
								${SEM}/Powerset.vo \
								${SEM}/Foundation.vo \
								${SEM}/Compatible.vo

${CORE}/Nat.vo : 				${CORE}/Nat.v
	coqc ${CORE}/Nat.v -R ${CORE} ${CORE}

${CORE}/LEM.vo :				${CORE}/LEM.v
	coqc ${CORE}/LEM.v -R ${CORE} ${CORE}

${CORE}/Set.vo : 				${CORE}/Set.v
	coqc ${CORE}/Set.v -R ${CORE} ${CORE}


${CORE}/Order.vo :				${CORE}/Order.v \
								${CORE}/Nat.vo \
								${CORE}/Set.vo
	coqc ${CORE}/Order.v -R ${CORE} ${CORE}


${CORE}/Core.vo :				${CORE}/Core.v \
								${CORE}/Nat.vo \
								${CORE}/Set.vo \
								${CORE}/Order.vo
	coqc ${CORE}/Core.v -R ${CORE} ${CORE}


${CORE}/Incl.vo :				${CORE}/Incl.v \
								${CORE}/Nat.vo \
								${CORE}/Set.vo \
								${CORE}/Order.vo \
								${CORE}/Core.vo
	coqc ${CORE}/Incl.v -R ${CORE} ${CORE}

	
${CORE}/Elem.vo :				${CORE}/Elem.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo
	coqc ${CORE}/Elem.v -R ${CORE} ${CORE}
		


${CORE}/ToList.vo :				${CORE}/ToList.v \
								${CORE}/Nat.vo \
								${CORE}/Set.vo \
								${CORE}/Order.vo \
								${CORE}/Core.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo
	coqc ${CORE}/ToList.v -R ${CORE} ${CORE}
	

${CORE}/Trans.vo :				${CORE}/Trans.v \
								${CORE}/Set.vo \
								${CORE}/Order.vo \
								${CORE}/Core.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/ToList.vo
	coqc ${CORE}/Trans.v -R ${CORE} ${CORE}
	

${CORE}/ElemIncl.vo :			${CORE}/ElemIncl.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/ToList.vo \
								${CORE}/Trans.vo
	coqc ${CORE}/ElemIncl.v -R ${CORE} ${CORE}


${CORE}/Equal.vo :				${CORE}/Equal.v \
								${CORE}/Set.vo \
								${CORE}/Elem.vo
	coqc ${CORE}/Equal.v -R ${CORE} ${CORE}
	

${CORE}/Extensionality.vo :		${CORE}/Extensionality.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/ToList.vo \
								${CORE}/Trans.vo \
								${CORE}/ElemIncl.vo \
								${CORE}/Equal.vo
	coqc ${CORE}/Extensionality.v -R ${CORE} ${CORE}

${CORE}/Filter.vo : 			${CORE}/Filter.v
	coqc ${CORE}/Filter.v -R ${CORE} ${CORE}


${CORE}/Decidability.vo : 		${CORE}/Decidability.v \
								${CORE}/Filter.vo \
								${CORE}/Set.vo \
								${CORE}/Order.vo \
								${CORE}/Core.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Extensionality.vo
	coqc ${CORE}/Decidability.v -R ${CORE} ${CORE}

${CORE}/Empty.vo :				${CORE}/Empty.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/ToList.vo \
								${CORE}/ElemIncl.vo \
								${CORE}/Extensionality.vo
	coqc ${CORE}/Empty.v -R ${CORE} ${CORE}


${CORE}/Pairing.vo :			${CORE}/Pairing.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/ToList.vo \
								${CORE}/Extensionality.vo \
								${CORE}/Empty.vo
	coqc ${CORE}/Pairing.v -R ${CORE} ${CORE}



${CORE}/Union.vo :				${CORE}/Union.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Empty.vo \
								${CORE}/ToList.vo \
								${CORE}/Extensionality.vo
	coqc ${CORE}/Union.v -R ${CORE} ${CORE}


${CORE}/Intersection.vo :		${CORE}/Intersection.v \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Empty.vo \
								${CORE}/Filter.vo \
								${CORE}/ToList.vo \
								${CORE}/Decidability.vo \
								${CORE}/Extensionality.vo

	coqc ${CORE}/Intersection.v -R ${CORE} ${CORE}


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

	coqc ${CORE}/Powerset.v -R ${CORE} ${CORE}


${CORE}/Rank.vo :				${CORE}/Rank.v \
								${CORE}/Nat.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Empty.vo \
								${CORE}/ToList.vo \
								${CORE}/ElemIncl.vo \
								${CORE}/Decidability.vo \
								${CORE}/Extensionality.vo
	
	coqc ${CORE}/Rank.v -R ${CORE} ${CORE}


${CORE}/Foundation.vo :			${CORE}/Foundation.v \
								${CORE}/Nat.vo \
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
	coqc ${CORE}/Foundation.v -R ${CORE} ${CORE}

${CORE}/Compatible.vo :			${CORE}/Compatible.v \
								${CORE}/Set.vo \
								${CORE}/Elem.vo
	coqc ${CORE}/Compatible.v -R ${CORE} ${CORE}

${CORE}/Comprehension.vo :		${CORE}/Comprehension.v \
								${CORE}/Set.vo
	coqc ${CORE}/Comprehension.v -R ${CORE} ${CORE}


${CORE}/Fresh.vo :				${CORE}/Fresh.v
	coqc ${CORE}/Fresh.v -R ${CORE} ${CORE}

${CORE}/Syntax.vo :				${CORE}/Syntax.v
	coqc ${CORE}/Syntax.v -R ${CORE} ${CORE}


${CORE}/Environment.vo :		${CORE}/Environment.v \
								${CORE}/Set.vo \
								${CORE}/Equal.vo
	coqc ${CORE}/Environment.v -R ${CORE} ${CORE}

${CORE}/Semantics.vo :			${CORE}/Semantics.v \
								${CORE}/LEM.vo \
								${CORE}/Nat.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Empty.vo \
								${CORE}/Fresh.vo \
								${CORE}/Syntax.vo \
								${CORE}/ElemIncl.vo \
								${CORE}/Foundation.vo \
								${CORE}/Environment.vo
	coqc ${CORE}/Semantics.v -R ${CORE} ${CORE}
				

${SEM}/Incl.vo :				${SEM}/Incl.v \
								${CORE}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Equal.vo \
								${CORE}/Syntax.vo \
								${CORE}/Semantics.vo \
								${CORE}/Environment.vo
	coqc ${SEM}/Incl.v -R ${CORE} ${CORE}


${SEM}/Trans.vo :				${SEM}/Trans.v \
								${CORE}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Syntax.vo \
								${CORE}/Semantics.vo \
								${CORE}/Environment.vo
	coqc ${SEM}/Trans.v -R ${CORE} ${CORE}


${SEM}/ElemIncl.vo :			${SEM}/ElemIncl.v \
								${CORE}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Syntax.vo \
								${CORE}/Semantics.vo \
								${CORE}/Environment.vo
	coqc ${SEM}/ElemIncl.v -R ${CORE} ${CORE}


${SEM}/Equal.vo :				${SEM}/Equal.v \
								${CORE}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Syntax.vo \
								${CORE}/Semantics.vo \
								${CORE}/Environment.vo
	coqc ${SEM}/Equal.v -R ${CORE} ${CORE}


${SEM}/Extensionality.vo :		${SEM}/Extensionality.v \
								${CORE}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Syntax.vo \
								${CORE}/Semantics.vo \
								${CORE}/Environment.vo
	coqc ${SEM}/Extensionality.v -R ${CORE} ${CORE}


${SEM}/Empty.vo :				${SEM}/Empty.v \
								${CORE}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Syntax.vo \
								${CORE}/Semantics.vo \
								${CORE}/Environment.vo
	coqc ${SEM}/Empty.v -R ${CORE} ${CORE}


${SEM}/Pairing.vo :				${SEM}/Pairing.v \
								${CORE}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Syntax.vo \
								${CORE}/Semantics.vo \
								${CORE}/Environment.vo
	coqc ${SEM}/Pairing.v -R ${CORE} ${CORE}


${SEM}/Union.vo :				${SEM}/Union.v \
								${CORE}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Syntax.vo \
								${CORE}/Semantics.vo \
								${CORE}/Environment.vo
	coqc ${SEM}/Union.v -R ${CORE} ${CORE}


${SEM}/Powerset.vo :			${SEM}/Powerset.v \
								${CORE}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/Incl.vo \
								${CORE}/Equal.vo \
								${CORE}/Syntax.vo \
								${CORE}/Semantics.vo \
								${CORE}/Environment.vo
	coqc ${SEM}/Powerset.v -R ${CORE} ${CORE}


${SEM}/Foundation.vo :			${SEM}/Foundation.v \
								${CORE}/LEM.vo \
								${CORE}/Set.vo \
								${CORE}/Incl.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Syntax.vo \
								${CORE}/Semantics.vo \
								${CORE}/Foundation.vo \
								${CORE}/Environment.vo
	
	coqc ${SEM}/Foundation.v -R ${CORE} ${CORE}

${SEM}/Compatible.vo :			${SEM}/Compatible.v \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/Equal.vo \
								${CORE}/Syntax.vo \
								${CORE}/Semantics.vo \
								${CORE}/Compatible.vo \
								${CORE}/Environment.vo
	
	coqc ${SEM}/Compatible.v -R ${CORE} ${CORE}
