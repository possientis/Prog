all:	bool.vo \
		nat.vo \
		binary.vo \
		induction.vo \
		natprod.vo \
		natlist.vo \
		natoption.vo \
		list.vo \
		option.vo


bool.vo: bool.v
	coqc bool.v

nat.vo: nat.v bool.vo
	coqc nat.v

binary.vo: binary.v
	coqc binary.v

induction.vo: induction.v bool.vo nat.vo binary.vo
	coqc induction.v

natprod.vo : natprod.v
	coqc natprod.v

natlist.vo: natlist.v nat.vo bool.vo induction.vo
	coqc natlist.v

natoption.vo: natoption.v nat.vo bool.vo natlist.vo 
	coqc natoption.v

list.vo : list.v bool.vo
	coqc list.v

option.vo : option.v list.vo nat.vo bool.vo
	coqc option.v
