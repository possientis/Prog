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
	${AXIOM}/NonEmptyUniverse.vo \
	${AXIOM}/Pairing.vo \
	${AXIOM}/Power.vo \
	${AXIOM}/Replacement.vo \
	${AXIOM}/Specification.vo \
	${AXIOM}/Union.vo

BINARY_OBJ = \
	${BINARY}/Bijection.vo \
	${BINARY}/Compose.vo \
	${BINARY}/Converse.vo \
	${BINARY}/Domain.vo \
	${BINARY}/Function.vo \
	${BINARY}/Functional.vo \
	${BINARY}/FunctionalAt.vo \
	${BINARY}/Image.vo \
	${BINARY}/InvImage.vo \
	${BINARY}/OneToOne.vo \
	${BINARY}/Range.vo \
	${BINARY}/Restrict.vo

CLASS_OBJ = \
	${CLASS}/AntiSymmetric.vo \
	${CLASS}/Bij.vo \
	${CLASS}/Bijection.vo \
	${CLASS}/BijectionOn.vo \
	${CLASS}/Bounded.vo \
	${CLASS}/Complement.vo \
	${CLASS}/Compose.vo \
	${CLASS}/Converse.vo \
	${CLASS}/Diff.vo \
	${CLASS}/Domain.vo \
	${CLASS}/Empty.vo \
	${CLASS}/Eval.vo \
	${CLASS}/FromBinary.vo \
	${CLASS}/Fst.vo \
	${CLASS}/Fun.vo \
	${CLASS}/Function.vo \
	${CLASS}/Functional.vo \
	${CLASS}/FunctionalAt.vo \
	${CLASS}/FunctionOn.vo \
	${CLASS}/Image.vo \
	${CLASS}/Incl.vo \
	${CLASS}/Inj.vo \
	${CLASS}/Inter.vo \
	${CLASS}/Irreflexive.vo \
	${CLASS}/OneToOne.vo \
	${CLASS}/Onto.vo \
	${CLASS}/Pair.vo \
	${CLASS}/PartialOrd.vo \
	${CLASS}/Power.vo \
	${CLASS}/Prod.vo \
	${CLASS}/Proper.vo \
	${CLASS}/Range.vo \
	${CLASS}/Reflexive.vo \
	${CLASS}/Rel.vo \
	${CLASS}/Restrict.vo \
	${CLASS}/Russell.vo \
	${CLASS}/Small.vo \
	${CLASS}/Snd.vo \
	${CLASS}/StrictOrd.vo \
	${CLASS}/StrictTotalOrd.vo \
	${CLASS}/Switch.vo \
	${CLASS}/Total.vo \
	${CLASS}/Transitive.vo \
	${CLASS}/Union.vo \
	${CLASS}/UnionGen.vo \
	${CLASS}/Union2.vo \
	${CLASS}/Utils.vo \
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
	${CORE}/Prod.vo \
	${CORE}/Union.vo \
	${CORE}/Zero.vo

SET_OBJ = \
	${SET}/Converse.vo \
	${SET}/Diff.vo \
	${SET}/Domain.vo \
	${SET}/Empty.vo \
	${SET}/Eval.vo \
	${SET}/Foundation.vo \
	${SET}/FromClass.vo \
	${SET}/Functional.vo \
	${SET}/Incl.vo \
	${SET}/Inter.vo \
	${SET}/OrdPair.vo \
	${SET}/OrdTuple.vo \
	${SET}/Pair.vo \
	${SET}/Power.vo \
	${SET}/Prod.vo \
	${SET}/Range.vo \
	${SET}/Rel.vo \
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
