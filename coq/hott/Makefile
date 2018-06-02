all: 	set.vo \
		equal.vo \
		empty.vo \
		singleton.vo


set.vo : set.v
	coqc set.v

equal.vo : equal.v set.vo
	coqc equal.v

empty.vo : empty.v set.vo
	coqc empty.v

singleton.vo : singleton.v set.vo empty.vo
	coqc singleton.v

