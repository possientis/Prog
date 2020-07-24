AXIOM := Axiom
CLASS := Class
NAT   := Nat
REL	  := Rel
FUNC  := Func
LIST  := List
FOL   := Fol
LAM   := Lam

all : Done

Done : 	${AXIOM}/Done \
		${CLASS}/Done \
		${NAT}/Done \
		${REL}/Done \
		${FUNC}/Done \
		${LIST}/Done \
		${FOL}/Done \
		${LAM}/Done
	touch Done

${AXIOM}/Done : 					$(ls ${AXIOM}/*.v)
	$(MAKE) --directory=${AXIOM}


${CLASS}/Done : 					$(ls ${CLASS}/*.v)
	$(MAKE) --directory=${CLASS}


${NAT}/Done : 						$(ls ${NAT}/*.v)
	$(MAKE) --directory=${NAT}


${REL}/Done : 						$(ls ${REL}/*.v)
	$(MAKE) --directory=${REL}


${FUNC}/Done : 						$(ls ${FUNC}/*.v) \
									${AXIOM}/Done \
									${CLASS}/Done
	$(MAKE) --directory=${FUNC}


${LIST}/Done : 						$(ls ${LIST}/*.v) \
									${AXIOM}/Done \
									${CLASS}/Done \
									${FUNC}/Done
	$(MAKE) --directory=${LIST}


${FOL}/Done : 						$(ls ${FOL}/*.v) \
									${AXIOM}/Done \
									${CLASS}/Done \
									${NAT}/Done \
									${REL}/Done \
									${FUNC}/Done \
									${LIST}/Done
	$(MAKE) --directory=${FOL}


${LAM}/Done : 						$(ls ${LAM}/*.v) \
									${AXIOM}/Done \
									${CLASS}/Done \
									${NAT}/Done \
									${REL}/Done \
									${FUNC}/Done \
									${LIST}/Done
	$(MAKE) --directory=${LAM}


clean: 
	$(MAKE) --directory=${AXIOM} 	clean
	$(MAKE) --directory=${CLASS} 	clean
	$(MAKE) --directory=${NAT} 		clean
	$(MAKE) --directory=${REL} 		clean
	$(MAKE) --directory=${FUNC} 	clean
	$(MAKE) --directory=${LIST} 	clean
	$(MAKE) --directory=${FOL} 		clean
	$(MAKE) --directory=${LAM} 		clean
	rm -f Done
