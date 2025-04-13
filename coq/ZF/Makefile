.PHONY : all clean

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

TOP_OBJ 	:= $(shell for f in ${TOP}/*.v;   do printf "${TOP}/%s.vo " 	$$(basename $$f .v); done)
AXIOM_OBJ := $(shell for f in ${AXIOM}/*.v; do printf "${AXIOM}/%s.vo " $$(basename $$f .v); done)
CLASS_OBJ := $(shell for f in ${CLASS}/*.v; do printf "${CLASS}/%s.vo " $$(basename $$f .v); done)
CORE_OBJ 	:= $(shell for f in ${CORE}/*.v; 	do printf "${CORE}/%s.vo " 	$$(basename $$f .v); done)
SET_OBJ 	:= $(shell for f in ${SET}/*.v; 	do printf "${SET}/%s.vo " 	$$(basename $$f .v); done)

# Overall target
all : deps \
	${AXIOM_OBJ} \
	${CLASS_OBJ} \
	${CORE_OBJ} \
	${SET_OBJ} \
	${TOP_OBJ}

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

deps :
	@echo "Generating dependencies..."
	@coqdep -vos -R . ZF $(shell find . -name "*.v") > deps 

include deps

clean :
	@echo "Cleaning up artefacts..."
	@bash -c '\
		rm -f {*,*/*,*/*/*}.{glob,vo,vok,vos,aux} ; \
	  rm -f	{.*,*/.*,*/*/.*}.aux ; \
		rm -f deps ; \
		'

