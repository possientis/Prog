.PHONY : all clean

VFILES  	:= $(shell find . -name "*.v")
VOFILES   := $(VFILES:.v=.vo)

VOKFILES  = $(shell find . -name "*.vok")
VOSFILES  = $(shell find . -name "*.vos")
AUXFILES  = $(shell find . -name "*.aux")
GLOBFILES = $(shell find . -name "*.glob")
HIFILES   = $(shell find . -name "*.hi")
OBJFILES  = $(shell find . -name "*.o")
MAINFILE  = $(shell find . -name "Main")

ARTIFACTS = $(VOFILES) $(VOKFILES) $(VOSFILES) $(AUXFILES) $(GLOBFILES) $(HIFILES) $(OBJFILES) $(MAINFILE)

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

