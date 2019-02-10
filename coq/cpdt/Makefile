all:	utils_nat.vo \
		untyped.vo \
		typed.vo \
		chapt3.vo \
		mutual_ind.vo \
		reflexive.vo \
		recursion.vo \
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

mutual_ind.vo : mutual_ind.v
	coqc mutual_ind.v

reflexive.vo : reflexive.v
	coqc reflexive.v

recursion.vo : recursion.v
	coqc recursion.v

test_untyped.vo : Test/untyped_t.v untyped.vo
	coqc Test/untyped_t.v 

test_typed.vo : Test/typed_t.v typed.vo
	coqc Test/typed_t.v -R Utils Utils


