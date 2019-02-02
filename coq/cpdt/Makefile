all:	utils_nat.vo \
		untyped.vo \
		typed.vo \
		test_untyped.vo \
		test_typed.vo
	
utils_nat.vo : Utils/nat.v
	coqc Utils/nat.v -R Utils Utils

untyped.vo : untyped.v
	coqc untyped.v

typed.vo : typed.v
	coqc typed.v -R Utils Utils

test_untyped.vo : Test/untyped_t.v untyped.vo
	coqc Test/untyped_t.v 

test_typed.vo : Test/typed_t.v typed.vo
	coqc Test/typed_t.v -R Utils Utils


