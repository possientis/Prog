.PHONY : all clean

# Folder names
AXIOM  = Axiom
BINARY = Binary
CLASS  = Class
CORE   = Core
SET    = Set

# coqc command line option
TOP_LIB    		= -Q . ZF
AXIOM_LIB  		= -Q ${AXIOM}  ZF.${AXIOM} -Q . ZF
BINARY_LIB 		= -Q ${BINARY} ZF.${BINARY} -Q . ZF
CLASS_LIB  		= -Q ${CLASS}  ZF.${CLASS} -Q . ZF
CORE_LIB   		= -Q ${CORE}   ZF.${CORE}  -Q . ZF
SET_LIB    		= -Q ${SET}    ZF.${SET}   -Q . ZF

# Object files
TOP_OBJ = \
	Binary.vo \
	Class.vo \
	Set.vo

AXIOM_OBJ = \
	${AXIOM}/Classic.vo \
	${AXIOM}/Define.vo \
	${AXIOM}/Extensionality.vo \
	${AXIOM}/Foundation.vo \
	${AXIOM}/Infinity.vo \
	${AXIOM}/NonEmpty.vo \
	${AXIOM}/Pairing.vo \
	${AXIOM}/Power.vo \
	${AXIOM}/Replacement.vo \
	${AXIOM}/Specification.vo \
	${AXIOM}/Union.vo

BINARY_OBJ = \
	${BINARY}/Compose.vo \
	${BINARY}/Domain.vo \
	${BINARY}/Range.vo \
	${BINARY}/Restrict.vo

CLASS_OBJ = \
	${CLASS}/Bijection.vo \
	${CLASS}/Bounded.vo \
	${CLASS}/Comp.vo \
	${CLASS}/Compose.vo \
	${CLASS}/Converse.vo \
	${CLASS}/Diff.vo \
	${CLASS}/Domain.vo \
	${CLASS}/FromBinary.vo \
	${CLASS}/Fst.vo \
	${CLASS}/Function.vo \
	${CLASS}/Functional.vo \
	${CLASS}/Image.vo \
	${CLASS}/Include.vo \
	${CLASS}/Inter.vo \
	${CLASS}/OneToOne.vo \
	${CLASS}/Product.vo \
	${CLASS}/Range.vo \
	${CLASS}/Relation.vo \
	${CLASS}/Restrict.vo \
	${CLASS}/Russell.vo \
	${CLASS}/Small.vo \
	${CLASS}/Snd.vo \
	${CLASS}/Switch.vo \
	${CLASS}/Union.vo \
	${CLASS}/V.vo

CORE_OBJ = \
	${CORE}/And.vo \
	${CORE}/Diff.vo \
	${CORE}/Dot.vo \
	${CORE}/Equiv.vo \
	${CORE}/Image.vo \
	${CORE}/Leq.vo \
	${CORE}/Lt.vo \
	${CORE}/Not.vo \
	${CORE}/Or.vo \
	${CORE}/Pipe.vo \
	${CORE}/Product.vo \
	${CORE}/Zero.vo

SET_OBJ = \
	${SET}/Converse.vo \
	${SET}/Diff.vo \
	${SET}/Empty.vo \
	${SET}/Functional.vo \
	${SET}/Include.vo \
	${SET}/Inter.vo \
	${SET}/OrdPair.vo \
	${SET}/OrdTuple.vo \
	${SET}/Pair.vo \
	${SET}/Power.vo \
	${SET}/Product.vo \
	${SET}/Relation.vo \
	${SET}/Singleton.vo \
	${SET}/Specify.vo \
	${SET}/Tuple.vo \
	${SET}/Union.vo


# Overall target
all : \
	${AXIOM_OBJ} \
	${BINARY_OBJ} \
	${CLASS_OBJ} \
	${CORE_OBJ} \
	${SET_OBJ} \
	${TOP_OBJ}

# General rules
%.vo : %.v
	coqc $< ${TOP_LIB}

${AXIOM}/%.vo : ${AXIOM}/%.v
	coqc $< ${AXIOM_LIB}

${BINARY}/%.vo : ${BINARY}/%.v
	coqc $< ${BINARY_LIB}

${CLASS}/%.vo : ${CLASS}/%.v
	coqc $< ${CLASS_LIB}

${CORE}/%.vo : ${CORE}/%.v
	coqc $< ${CORE_LIB}

${SET}/%.vo : ${SET}/%.v
	coqc $< ${SET_LIB}

deps :
	./deps.sh

include deps

clean :
	bash rm.sh
