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
		prod.vo \
		higher_order.vo \
		fmap.vo \
		fold.vo \
		const.vo \
		church.vo \
		apply.vo \
		inversion.vo \
		tactic_hyp.vo \
		unfold.vo \
		destruct.vo \
		and.vo \
		or.vo \
		not.vo \
		iff.vo \
		setoid.vo \
		exists.vo \
		In.vo \
		equal.vo \
		reflection.vo \
		logic.vo \
		inductive_prop.vo \
		le.vo \
		subseq.vo \
		regex.vo


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

list.vo : list.v bool.vo induction.vo
	coqc list.v

option.vo : option.v list.vo nat.vo bool.vo
	coqc option.v

prod.vo : prod.v list.vo
	coqc prod.v

higher_order.vo : higher_order.v list.vo bool.vo nat.vo
	coqc higher_order.v

fmap.vo : fmap.v nat.vo bool.vo list.vo
	coqc fmap.v	

fold.vo : fold.v list.vo bool.vo
	coqc fold.v

const.vo : const.v higher_order.vo
	coqc const.v

church.vo : church.v
	coqc church.v

apply.vo : apply.v list.vo nat.vo bool.vo
	coqc apply.v

inversion.vo : inversion.v list.vo nat.vo bool.vo
	coqc inversion.v	

tactic_hyp.vo : tactic_hyp.v nat.vo bool.vo induction.vo
	coqc tactic_hyp.v

unfold.vo : unfold.v induction.vo
	coqc unfold.v

destruct.vo : destruct.v nat.vo bool.vo
	coqc destruct.v

and.vo : and.v
	coqc and.v

or.vo : or.v nat.vo
	coqc or.v

not.vo : not.v
	coqc not.v

iff.vo : iff.v
	coqc iff.v

setoid.vo : setoid.v or.vo
	coqc setoid.v

exists.vo : exists.v not.vo
	coqc exists.v

In.vo : In.v list.vo fmap.vo nat.vo bool.vo induction.vo
	coqc In.v

equal.vo : equal.v induction.vo
	coqc equal.v	

reflection.vo : reflection.v nat.vo bool.vo induction.vo
	coqc reflection.v

logic.vo : logic.v not.vo
	coqc logic.v

inductive_prop.vo : inductive_prop.v induction.vo nat.vo bool.vo not.vo
	coqc inductive_prop.v

le.vo : le.v inductive_prop.vo
	coqc le.v

subseq.vo : subseq.v list.vo
	coqc subseq.v	

regex.vo : regex.v list.vo fold.vo In.vo bool.vo
	coqc regex.v
