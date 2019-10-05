all: 			set.vo \
				nat.vo \
				Exists.vo \
				Order.vo \
				Subset_n.vo \
				subset.vo \
				Elem.vo \
				Equal.vo



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

Subset_n.vo :	Subset_n.v \
				set.vo \
				nat.vo \
				Exists.vo \
				Order.vo
	coqc Subset_n.v

subset.vo :		subset.v \
				set.vo \
				nat.vo \
				Order.vo \
				Exists.vo \
				Subset_n.vo
	coqc subset.v

Elem.vo :		Elem.v \
				set.vo \
				subset.vo \
				Order.vo
	coqc Elem.v

Equal.vo :		Equal.v \
				set.vo \
				Elem.vo
	coqc Equal.v
