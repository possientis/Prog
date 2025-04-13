.PHONY : all clean

VFILES := $(shell find . -name "*.v")
VOFILES := $(VFILES:.v=.vo)

# Folder names
AXIOM  = Axiom
CLASS  = Class
CORE   = Core
SET    = Set
TOP    = .

# coqc command line option
TOP_LIB    		= -Q . ZF
AXIOM_LIB  		= -Q ${AXIOM}  ZF.${AXIOM} -Q . ZF
CLASS_LIB  		= -Q ${CLASS}  ZF.${CLASS} -Q . ZF
CORE_LIB   		= -Q ${CORE}   ZF.${CORE}  -Q . ZF
SET_LIB    		= -Q ${SET}    ZF.${SET}   -Q . ZF

# Overall target
all : deps $(VOFILES)

# General rules
%.vo : %.v
	coqc $< ${TOP_LIB}

${AXIOM}/%.vo : ${AXIOM}/%.v
	coqc $< ${AXIOM_LIB}

${CLASS}/%.vo : ${CLASS}/%.v
	coqc $< ${CLASS_LIB}

${CORE}/%.vo : ${CORE}/%.v
	coqc $< ${CORE_LIB}

${SET}/%.vo : ${SET}/%.v
	coqc $< ${SET_LIB}

deps : $(VFILES)
	@echo "Generating dependencies..."
	@coqdep -vos -R . ZF $(VFILES) > deps 

include deps

clean :
	@echo "Cleaning up artefacts..."
	@bash -c '\
		rm -f {*,*/*,*/*/*}.{glob,vo,vok,vos,aux} ; \
	  rm -f	{.*,*/.*,*/*/.*}.aux ; \
		rm -f deps ; \
		'

