all : 	type.vo \
		term.vo \
		value.vo \
		context.vo

type.vo: type.v
	coqc type.v

term.vo : term.v type.vo
	coqc term.v

value.vo : value.v term.vo
	coqc value.v

context.vo : context.v type.vo term.vo
	coqc context.v
		
