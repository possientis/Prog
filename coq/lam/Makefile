all:	    eq.vo \
			incl.vo \
			term.vo \
			var.vo \
			injective.vo \
			remove.vo \
			vsubst.vo \
			free.vo \
			subst.vo \
			alpha.vo

eq.vo:			eq.v
	coqc eq.v

incl.vo:		incl.v eq.vo
	coqc incl.v


term.vo:		term.v
	coqc term.v

var.vo:			var.v term.vo
	coqc var.v

injective.vo:	injective.v term.vo var.vo incl.vo
	coqc injective.v

remove.vo:		remove.v eq.vo incl.vo injective.vo
	coqc remove.v

vsubst.vo: 		vsubst.v eq.vo term.vo 
	coqc vsubst.v

free.vo:		free.v eq.vo incl.vo remove.vo term.vo var.vo vsubst.vo
	coqc free.v

subst.vo:		subst.v	eq.vo term.vo
	coqc subst.v

alpha.vo : 		alpha.v eq.vo term.vo free.vo vsubst.vo
	coqc alpha.v




