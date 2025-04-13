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

TOP_OBJ   := $(patsubst %.v,%.vo,$(notdir $(wildcard ${TOP}/*.v)))
TOP_OBJ   := $(addprefix ${TOP}/,${TOP_OBJ})
AXIOM_OBJ := $(patsubst %.v,%.vo,$(notdir $(wildcard ${AXIOM}/*.v)))
AXIOM_OBJ := $(addprefix ${AXIOM}/,${AXIOM_OBJ})
CLASS_OBJ := $(patsubst %.v,%.vo,$(notdir $(wildcard ${CLASS}/*.v)))
CLASS_OBJ := $(addprefix ${CLASS}/,${CLASS_OBJ})
CORE_OBJ  := $(patsubst %.v,%.vo,$(notdir $(wildcard ${CORE}/*.v)))
CORE_OBJ  := $(addprefix ${CORE}/,${CORE_OBJ})
SET_OBJ  := $(patsubst %.v,%.vo,$(notdir $(wildcard ${SET}/*.v)))
SET_OBJ  := $(addprefix ${SET}/,${SET_OBJ})

# Overall target
all : \
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
	@bash rm.sh
