all: 			set.vo \
				nat.vo \
				Exists.vo \
				Order.vo \
				subset.vo 



set.vo : 		set.v
	coqc set.v

nat.vo :		nat.v
	coqc nat.v

Exists.vo : 	Exists.v \
				set.vo
	coqc Exists.v

Order.vo :		Order.v \
				set.vo
	coqc Order.v

subset.vo :		subset.v \
				set.vo \
				nat.vo \
				Exists.vo \
				Order.vo
	coqc subset.v


