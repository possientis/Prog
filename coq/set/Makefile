all: order

set: set.vo set.glob .set.vo.aux

set.glob: set.v
	coqc set.v
set.vo: set.v
	coqc set.v
.set.vo.aux: set.v
	coqc set.v

order: set order.vo order.glob .order.vo.aux

order.glob: order.v
	coqc order.v
order.vo: order.v
	coqc order.v
.order.vo.aux: order.v
	coqc order.v

