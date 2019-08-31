all: 			set.vo \
				Exists.vo \
				Order.vo \
				subset.vo 



set.vo : 		set.v
	coqc set.v

Exists.vo : 	Exists.v \
				set.vo
	coqc Exists.v

Order.vo :		Order.v \
				set.vo
	coqc Order.v

subset.vo :		subset.v \
				set.vo \
				Exists.vo	
	coqc subset.v


