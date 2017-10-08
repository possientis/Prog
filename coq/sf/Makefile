all:	bool.vo \
		nat.vo \
		binary.vo \
		induction.vo


bool.vo: bool.v
	coqc bool.v

nat.vo: nat.v bool.vo
	coqc nat.v

binary.vo: binary.v
	coqc binary.v

induction.vo: induction.v bool.vo nat.vo binary.vo
	coqc induction.v


