all:	Axiom_Extensionality.vo \
		ex.vo \
		test_ex.vo \
		True.vo \
		False.vo \
		bool.vo \
		test_bool.vo \
		nat.vo \
		binary.vo \
		induction.vo \
		natprod.vo \
		natlist.vo \
		natoption.vo \
		natdict.vo \
		list.vo \
		test_list.vo \
		option.vo \
		prod.vo \
		higher_order.vo \
		fmap.vo \
		disjoint.vo \
		test_disjoint.vo \
		fold.vo \
		const.vo \
		church.vo \
		apply.vo \
		inversion.vo \
		tactic_hyp.vo \
		unfold.vo \
		destruct.vo \
		and.vo \
		test_and.vo \
		or.vo \
		test_or.vo \
		not.vo \
		iff.vo \
		setoid.vo \
		exists.vo \
		In.vo \
		test_In.vo \
		filter.vo \
		equal.vo \
		reflection.vo \
		logic.vo \
		inductive_prop.vo \
		test_inductive_prop.vo \
		le.vo \
		subseq.vo \
		regex.vo \
		palindrome.vo \
		merge.vo \
		dictionary.vo \
		test_dictionary.vo \
		my_equality.vo \
		nat_ind.vo

Axiom_Extensionality.vo : Axiom_Extensionality.v
	coqc Axiom_Extensionality.v

ex.vo : ex.v
	coqc ex.v

test_ex.vo : test_ex.v nat.vo inductive_prop.vo
	coqc test_ex.v

True.vo : True.v
	coqc True.v

False.vo : False.v
	coqc False.v

bool.vo: bool.v
	coqc bool.v

test_bool.vo: test_bool.v bool.vo
	coqc test_bool.v

nat.vo: nat.v bool.vo
	coqc nat.v

binary.vo: binary.v
	coqc binary.v

induction.vo: induction.v bool.vo nat.vo
	coqc induction.v

natprod.vo : natprod.v
	coqc natprod.v

natlist.vo: natlist.v nat.vo bool.vo induction.vo
	coqc natlist.v

natoption.vo: natoption.v nat.vo bool.vo natlist.vo 
	coqc natoption.v

natdict.vo: natdict.v nat.vo bool.vo natoption.vo
	coqc natdict.v

list.vo : list.v nat.vo bool.vo
	coqc list.v

test_list.vo : test_list.v list.vo
	coqc test_list.v

option.vo : option.v list.vo nat.vo bool.vo
	coqc option.v

prod.vo : prod.v list.vo
	coqc prod.v


higher_order.vo : higher_order.v bool.vo nat.vo list.vo In.vo filter.vo
	coqc higher_order.v

fmap.vo : fmap.v nat.vo bool.vo list.vo
	coqc fmap.v	

disjoint.vo : disjoint.v list.vo In.vo
	coqc disjoint.v

test_disjoint.vo : test_disjoint.v list.vo In.vo disjoint.vo
	coqc test_disjoint.v

fold.vo : fold.v bool.vo nat.vo list.vo
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

test_and.vo : test_and.v
	coqc test_and.v

or.vo : or.v nat.vo
	coqc or.v

test_or.vo : test_or.v
	coqc test_or.v

not.vo : not.v
	coqc not.v

iff.vo : iff.v
	coqc iff.v

setoid.vo : setoid.v nat.vo or.vo
	coqc setoid.v

exists.vo : exists.v not.vo
	coqc exists.v

In.vo : In.v list.vo fmap.vo 
	coqc In.v

test_In.vo : test_In.v In.vo list.vo fmap.vo nat.vo bool.vo induction.vo
	coqc test_In.v

filter.vo : filter.v bool.vo list.vo In.vo
	coqc filter.v

equal.vo : equal.v nat.vo
	coqc equal.v	

reflection.vo : reflection.v nat.vo bool.vo list.vo In.vo \
				filter.vo induction.vo
	coqc reflection.v

logic.vo : logic.v not.vo
	coqc logic.v

inductive_prop.vo : inductive_prop.v induction.vo nat.vo bool.vo not.vo
	coqc inductive_prop.v

test_inductive_prop.vo : test_inductive_prop.v nat.vo bool.vo induction.vo
	coqc test_inductive_prop.v

le.vo : le.v inductive_prop.vo induction.vo nat.vo bool.vo
	coqc le.v

subseq.vo : subseq.v bool.vo list.vo le.vo In.vo filter.vo
	coqc subseq.v	

regex.vo : regex.v list.vo fold.vo In.vo bool.vo le.vo
	coqc regex.v

palindrome.vo : palindrome.v list.vo nat.vo le.vo
	coqc palindrome.v

merge.vo : merge.v list.vo bool.vo In.vo higher_order.vo
	coqc merge.v

dictionary.vo : dictionary.v nat.vo bool.vo
	coqc dictionary.v

test_dictionary.vo : test_dictionary.v dictionary.vo bool.vo nat.vo
	coqc test_dictionary.v

my_equality.vo : my_equality.v nat.vo list.vo
	coqc my_equality.v

nat_ind.vo : nat_ind.v nat.vo
	coqc nat_ind.v
