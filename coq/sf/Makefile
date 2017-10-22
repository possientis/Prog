all:	bool.vo \
		nat.vo \
		binary.vo \
		induction.vo \
		natprod.vo \
		natlist.vo \
		option.vo \
		list.vo


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

option.vo: option.v nat.vo bool.vo natlist.vo 
	coqc option.v

list.vo : list.v bool.vo
	coqc list.v
