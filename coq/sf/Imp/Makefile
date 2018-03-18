all :   bool.vo \
		nat.vo \
		syntax.vo \
		eval.vo \
		test_eval.vo \
		optimize.vo \
		test_optimize.vo \
		try_evalR.vo \
		evalR.vo

bool.vo : bool.v
	coqc bool.v

nat.vo : nat.v bool.vo
	coqc nat.v

syntax.vo : syntax.v nat.vo
	coqc syntax.v


eval.vo : eval.v syntax.vo
	coqc eval.v

test_eval.vo : test_eval.v syntax.vo eval.vo bool.vo nat.vo
	coqc test_eval.v

optimize.vo : optimize.v nat.vo syntax.vo
	coqc optimize.v

test_optimize.vo : test_optimize.v nat.vo syntax.vo eval.vo optimize.vo
	coqc test_optimize.v

try_evalR.vo : try_evalR.v nat.vo syntax.vo
	coqc try_evalR.v

evalR.vo : evalR.v nat.vo syntax.vo
	coqc evalR.v
