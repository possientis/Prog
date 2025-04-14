.PHONY : all clean

VFILES  	:= $(shell find . -name "*.v")
VOFILES   := $(VFILES:.v=.vo)

VOKFILES  = $(shell find . -name "*.vok")
VOSFILES  = $(shell find . -name "*.vos")
AUXFILES  = $(shell find . -name "*.aux")
GLOBFILES = $(shell find . -name "*.glob")

ARTIFACTS = $(VOFILES) $(VOKFILES) $(VOSFILES) $(AUXFILES) $(GLOBFILES)

all : deps $(VOFILES)

%.vo : %.v
	@echo "Compiling $<"
	@coqc -R . CPDT $<

deps : $(VFILES)
	@echo "Generating dependencies..."
	@coqdep -vos -R . CPDT $(VFILES) > deps 

include deps

clean :
	@echo "Cleaning up artifacts..."
	@rm -f $(ARTIFACTS) deps

