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
		nat_ind.vo \
		test_nat_ind.vo \
		polymorphism.vo \
		closure.vo \
		lia.vo \
		syntax.vo \
		eval.vo \
		test_eval.vo \
		optimize.vo \
		optimize_sound.vo \
		evalR.vo \
		try_evalR.vo \
		state.vo \
		Imp_code.vo \
		ISA.vo \
		compile.vo \
		execute.vo \
		test_execute.vo \
		test_compile.vo \
		equiv.vo \
		test_equiv.vo \
		transform.vo \
		fold_constants.vo \
		test_fold_constants.vo \
		fold_constants_sound.vo \
		subst.vo \
		test_subst.vo \
		hsyntax.vo \
		heval.vo \
		hequiv.vo

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

fold.vo : fold.v bool.vo nat.vo list.vo fmap.vo
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

test_inductive_prop.vo : test_inductive_prop.v nat.vo bool.vo induction.vo inductive_prop.vo
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

dictionary.vo : dictionary.v nat.vo bool.vo option.vo reflection.vo
	coqc dictionary.v

test_dictionary.vo : test_dictionary.v dictionary.vo bool.vo nat.vo
	coqc test_dictionary.v

my_equality.vo : my_equality.v nat.vo list.vo
	coqc my_equality.v

nat_ind.vo : nat_ind.v nat.vo
	coqc nat_ind.v

test_nat_ind.vo : test_nat_ind.v nat_ind.vo nat.vo
	coqc test_nat_ind.v

polymorphism.vo : polymorphism.v
	coqc polymorphism.v

closure.vo : closure.v nat.vo le.vo
	coqc closure.v

lia.vo : lia.v
	coqc lia.v

syntax.vo : syntax.v bool.vo nat.vo dictionary.vo
	coqc syntax.v

eval.vo : eval.v bool.vo nat.vo syntax.vo state.vo
	coqc eval.v

test_eval.vo : test_eval.v bool.vo nat.vo syntax.vo eval.vo Imp_code.vo state.vo
	coqc test_eval.v

evalR.vo : evalR.v nat.vo bool.vo syntax.vo eval.vo
	coqc evalR.v

try_evalR.vo : try_evalR.v nat.vo syntax.vo
	coqc try_evalR.v

state.vo : state.v dictionary.vo nat.vo
	coqc state.v

Imp_code.vo : Imp_code.v nat.vo syntax.vo state.vo
	coqc Imp_code.v

ISA.vo : ISA.v nat.vo dictionary.vo
	coqc ISA.v	

compile.vo : compile.v nat.vo list.vo dictionary.vo syntax.vo state.vo \
	execute.vo eval.vo ISA.vo
	coqc compile.v

execute.vo : execute.v nat.vo list.vo dictionary.vo state.vo ISA.vo
	coqc execute.v

test_execute.vo : test_execute.v nat.vo list.vo dictionary.vo state.vo \
	compile.vo execute.vo ISA.vo
	coqc test_execute.v

test_compile.vo : test_compile.v nat.vo list.vo syntax.vo state.vo compile.vo
	coqc test_compile.v

equiv.vo : equiv.v bool.vo nat.vo syntax.vo eval.vo dictionary.vo state.vo test_eval.vo Imp_code.vo
	coqc equiv.v

test_equiv.vo : test_equiv.v bool.vo nat.vo dictionary.vo state.vo syntax.vo \
	eval.vo equiv.vo
	coqc test_equiv.v

transform.vo : transform.v bool.vo nat.vo syntax.vo eval.vo state.vo equiv.vo
	coqc transform.v

fold_constants.vo : fold_constants.v bool.vo nat.vo syntax.vo eval.vo state.vo \
	dictionary.vo equiv.vo transform.vo
	coqc fold_constants.v

test_fold_constants.vo : test_fold_constants.v nat.vo syntax.vo state.vo fold_constants.vo
	coqc test_fold_constants.v

fold_constants_sound.vo : fold_constants_sound.v bool.vo nat.vo syntax.vo \
	eval.vo state.vo dictionary.vo equiv.vo transform.vo fold_constants.vo
	coqc fold_constants_sound.v

optimize.vo : optimize.v nat.vo syntax.vo transform.vo fold_constants.vo
	coqc optimize.v

optimize_sound.vo : optimize_sound.v bool.vo nat.vo syntax.vo eval.vo \
	optimize.vo state.vo dictionary.vo equiv.vo transform.vo fold_constants.vo \
	fold_constants_sound.vo
	coqc optimize_sound.v

subst.vo : subst.v bool.vo nat.vo syntax.vo eval.vo dictionary.vo equiv.vo \
	state.vo
	coqc subst.v

test_subst.vo : test_subst.v nat.vo subst.vo syntax.vo state.vo
	coqc test_subst.v


hsyntax.vo : hsyntax.v bool.vo nat.vo dictionary.vo
	coqc hsyntax.v

heval.vo : heval.v nat.vo hsyntax.vo state.vo dictionary.vo
	coqc heval.v

hequiv.vo : hequiv.v bool.vo nat.vo hsyntax.vo heval.vo dictionary.vo state.vo
	coqc hequiv.v
