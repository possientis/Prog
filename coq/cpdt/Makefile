all:	utils_nat.vo \
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
		test_untyped.vo \
		test_typed.vo
	
utils_nat.vo : Utils/nat.v
	coqc Utils/nat.v -R Utils Utils

untyped.vo : untyped.v
	coqc untyped.v

typed.vo : typed.v
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

test_untyped.vo : Test/untyped_t.v untyped.vo
	coqc Test/untyped_t.v 

test_typed.vo : Test/typed_t.v typed.vo
	coqc Test/typed_t.v -R Utils Utils


