all:	bool.vo \
		nat.vo \
		binary.vo \
		induction.vo \
		natprod.vo \
		natlist.vo \
		natoption.vo \
		natdict.vo \
		list.vo \
		option.vo \
		higher_order.vo \
		fmap.vo \
		fold.vo \
		const.vo


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

natdict.vo: natdict.v nat.vo bool.vo natoption.vo
	coqc natdict.v

list.vo : list.v bool.vo
	coqc list.v

option.vo : option.v list.vo nat.vo bool.vo
	coqc option.v

higher_order.vo : higher_order.v list.vo bool.vo nat.vo
	coqc higher_order.v

fmap.vo : fmap.v nat.vo bool.vo list.vo
	coqc fmap.v	

fold.vo : fold.v list.vo bool.vo
	coqc fold.v

const.vo : const.v higher_order.vo
	coqc const.v



