.PHONY : all clean meta

VFILES  	:= $(shell find . -name "*.v")
VOFILES   := $(VFILES:.v=.vo)
METAVFILES  := $(shell find ./Meta -name "*.v")
METAVOFILES := $(METAVFILES:.v=.vo)

VOKFILES  = $(shell find . -name "*.vok")
VOSFILES  = $(shell find . -name "*.vos")
AUXFILES  = $(shell find . -name "*.aux")
GLOBFILES = $(shell find . -name "*.glob")

ARTIFACTS = $(VOFILES) $(VOKFILES) $(VOSFILES) $(AUXFILES) $(GLOBFILES)

all : deps $(VOFILES)

meta : deps $(METAVOFILES)

%.vo : %.v
	@echo "Compiling $<"
	@coqc -R . ZF $<

deps : $(VFILES)
	@echo "Generating dependencies..."
	@coqdep -vos -R . ZF $(VFILES) > deps 

include deps

clean :
	@echo "Cleaning up artifacts..."
	@rm -f $(ARTIFACTS) deps

