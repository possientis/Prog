.PHONY : all clean

VFILES  := $(shell find . -name "*.v")
VOFILES := $(VFILES:.v=.vo)

# Overall target
all : deps $(VOFILES)

# General rules
%.vo : %.v
	coqc -q -R . ZF $<

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

