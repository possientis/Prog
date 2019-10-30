CORE=Core

all :							${CORE}/Nat.vo \
								${CORE}/Filter.vo \
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
								${CORE}/Pairing.vo \
								${CORE}/Empty.vo \
								${CORE}/Union.vo \
								${CORE}/Intersection.vo \
								${CORE}/Powerset.vo


${CORE}/Nat.vo : 				${CORE}/Nat.v
	coqc ${CORE}/Nat.v -R ${CORE} ${CORE}


${CORE}/Filter.vo : 			${CORE}/Filter.v
	coqc ${CORE}/Filter.v -R ${CORE} ${CORE}


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


${CORE}/Pairing.vo :			${CORE}/Pairing.v \
								${CORE}/Set.vo
	coqc ${CORE}/Pairing.v -R ${CORE} ${CORE}


${CORE}/Empty.vo :				${CORE}/Empty.v \
								${CORE}/Set.vo \
								${CORE}/Elem.vo \
								${CORE}/ToList.vo
	coqc ${CORE}/Empty.v -R ${CORE} ${CORE}


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

