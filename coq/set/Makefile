CORE=Core

all :			${CORE}/Nat.vo \
				${CORE}/Set.vo \
				${CORE}/Order.vo \
				${CORE}/ToList.vo \
				${CORE}/Core.vo \
				${CORE}/Incl.vo \
				${CORE}/Elem.vo \
				${CORE}/Equal.vo \


${CORE}/Nat.vo : 	${CORE}/Nat.v
	coqc ${CORE}/Nat.v -R ${CORE} ${CORE}



${CORE}/Set.vo : 	${CORE}/Set.v
	coqc ${CORE}/Set.v -R ${CORE} ${CORE}



${CORE}/Order.vo :	${CORE}/Order.v \
					${CORE}/Set.vo
	coqc ${CORE}/Order.v -R ${CORE} ${CORE}



${CORE}/ToList.vo :	${CORE}/ToList.v \
					${CORE}/Set.vo \
					${CORE}/Order.vo \
					${CORE}/Nat.vo
	coqc ${CORE}/ToList.v -R ${CORE} ${CORE}
				


${CORE}/Core.vo :	${CORE}/Core.v \
					${CORE}/Set.vo \
					${CORE}/Nat.vo \
					${CORE}/Order.vo \
					${CORE}/ToList.vo
	coqc ${CORE}/Core.v -R ${CORE} ${CORE}



${CORE}/Incl.vo :	${CORE}/Incl.v \
					${CORE}/Set.vo \
					${CORE}/Nat.vo \
					${CORE}/Core.vo \
					${CORE}/Order.vo
	coqc ${CORE}/Incl.v -R ${CORE} ${CORE}


${CORE}/Elem.vo :	${CORE}/Elem.v \
					${CORE}/Set.vo \
					${CORE}/Nat.vo \
					${CORE}/Incl.vo \
					${CORE}/Core.vo \
					${CORE}/Order.vo
	coqc ${CORE}/Elem.v -R ${CORE} ${CORE}
		


${CORE}/Equal.vo :	${CORE}/Equal.v \
					${CORE}/Set.vo \
					${CORE}/Elem.vo
	coqc ${CORE}/Equal.v -R ${CORE} ${CORE}
	
