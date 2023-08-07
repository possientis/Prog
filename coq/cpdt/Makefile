all: Utils/nat.vo \
		extensionality.vo \
		irrelevance.vo \
		untyped.vo \
		typed.vo \
		chapt3.vo \
		mutual.vo \
		nested.vo \
		reflexive.vo \
		recursion.vo \
		tactic.vo \
		stream.vo \
		coind_sem.vo \
		dependent.vo \
		sumbool.vo \
		maybe.vo \
		sumor.vo \
		refine.vo \
		type_check.vo \
		option.vo \
		well_founded.vo \
		Max2.vo \
		domain.vo \
		thunk.vo \
		comp.vo \
		vec.vo \
		type.vo \
		RedBlackTree.vo \
		regex.vo \
		Ltac/find_if.vo \
		Ltac/monoid.vo \
		Test/untyped_t.vo \
		Test/typed_t.vo \
		Test/option_t.vo

Utils/nat.vo : Utils/nat.v
	coqc Utils/nat.v -R Utils Utils

extensionality.vo : extensionality.v
	coqc extensionality.v

irrelevance.vo : irrelevance.v
	coqc irrelevance.v

untyped.vo : untyped.v
	coqc untyped.v

typed.vo : typed.v Utils/nat.vo
	coqc typed.v -R Utils Utils

chapt3.vo : chapt3.v
	coqc chapt3.v

mutual.vo : mutual.v
	coqc mutual.v

nested.vo : nested.v
	coqc nested.v

reflexive.vo : reflexive.v
	coqc reflexive.v

recursion.vo : recursion.v
	coqc recursion.v

tactic.vo : tactic.v
	coqc tactic.v

stream.vo : stream.v
	coqc stream.v

coind_sem.vo : coind_sem.v
	coqc coind_sem.v

dependent.vo : dependent.v
	coqc dependent.v

sumbool.vo : sumbool.v
	coqc sumbool.v

maybe.vo : maybe.v
	coqc maybe.v

sumor.vo : sumor.v
	coqc sumor.v

refine.vo : refine.v
	coqc refine.v

type_check.vo : type_check.v option.vo
	coqc type_check.v

option.vo : option.v
	coqc option.v

well_founded.vo : well_founded.v stream.vo
	coqc well_founded.v

Max2.vo : Max2.v
	coqc Max2.v

domain.vo : domain.v Max2.vo extensionality.vo irrelevance.vo
	coqc domain.v

thunk.vo : thunk.v
	coqc thunk.v

comp.vo : comp.v
	coqc comp.v

vec.vo : vec.v
	coqc vec.v

type.vo : type.v Utils/nat.vo
	coqc type.v -R Utils Utils

RedBlackTree.vo : 	RedBlackTree.v Utils/nat.vo	
	coqc RedBlackTree.v -R Utils Utils

regex.vo : regex.v
	coqc regex.v
	
Ltac/find_if.vo : Ltac/find_if.v
	coqc Ltac/find_if.v -R Ltac Ltac

Ltac/monoid.vo : Ltac/monoid.v
	coqc Ltac/monoid.v -R Ltac Ltac

Test/untyped_t.vo : Test/untyped_t.v untyped.vo
	coqc Test/untyped_t.v 

Test/typed_t.vo : Test/typed_t.v typed.vo Utils/nat.vo
	coqc Test/typed_t.v -R Utils Utils

Test/option_t.vo : Test/option_t.v option.vo
	coqc Test/option_t.v



