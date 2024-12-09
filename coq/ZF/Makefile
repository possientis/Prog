.PHONY : all clean

# Folder names
AXIOM = Axiom
CLASS = Class
SET   = Set
CORE  = Core

# coqc command line option
TOP_LIB   = -Q . ZF
AXIOM_LIB = -Q ${AXIOM} ZF.${AXIOM} -Q . ZF
CLASS_LIB = -Q ${CLASS} ZF.${CLASS} -Q . ZF
SET_LIB   = -Q ${SET}   ZF.${SET}   -Q . ZF
CORE_LIB  = -Q ${CORE}  ZF.${CORE}  -Q . ZF

# Object files
TOP_OBJ = Core.vo \
					Class.vo

AXIOM_OBJ = ${AXIOM}/Define.vo \
	${AXIOM}/Classic.vo \
	${AXIOM}/Extensionality.vo \
	${AXIOM}/Replacement.vo \
	${AXIOM}/Specification.vo \
	${AXIOM}/Pairing.vo \
	${AXIOM}/Union.vo \
	${AXIOM}/Power.vo \
	${AXIOM}/NonEmpty.vo \
	${AXIOM}/Foundation.vo \
	${AXIOM}/Infinity.vo

CLASS_OBJ = ${CLASS}/Binary.vo \
	${CLASS}/Small.vo \
	${CLASS}/Bounded.vo \
	${CLASS}/Russell.vo \
	${CLASS}/Relation.vo \
	${CLASS}/Include.vo \
	${CLASS}/Utils.vo \
	${CLASS}/Product.vo \
	${CLASS}/V.vo \
	${CLASS}/Union.vo \
	${CLASS}/Intersect.vo

SET_OBJ = ${SET}/Empty.vo \
	${SET}/Pair.vo \
	${SET}/Singleton.vo \
	${SET}/OrdPair.vo \
	${SET}/OrdTuple.vo \
	${SET}/Union.vo \
	${SET}/Tuple.vo \
	${SET}/Intersect.vo \
	${SET}/Difference.vo \
	${SET}/Include.vo \
	${SET}/Power.vo \
	${SET}/Product.vo \
	${SET}/Utils.vo \
	${SET}/Relation.vo


CORE_OBJ = ${CORE}/Equiv.vo

# Overall target
all : ${TOP_OBJ} \
	${AXIOM_OBJ} \
	${CLASS_OBJ} \
	${SET_OBJ} \
	${CORE_OBJ}

# General rules
%.vo : %.v
	coqc $< ${TOP_LIB}

${AXIOM}/%.vo : ${AXIOM}/%.v
	coqc $< ${AXIOM_LIB}

${CLASS}/%.vo : ${CLASS}/%.v
	coqc $< ${CLASS_LIB}

${SET}/%.vo : ${SET}/%.v
	coqc $< ${SET_LIB}

${CORE}/%.vo : ${CORE}/%.v
	coqc $< ${CORE_LIB}

deps :
	./deps.sh

include deps

clean :
	bash rm.sh
