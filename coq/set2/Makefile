all: 	set.vo \
 			order.vo \
			elements.vo \
			order_elements.vo \
			subset.vo	\
			belong.vo	\
			equiv.vo \
			single_compatible.vo \
			subset_elements.vo \
			equiv_symmetric.vo \
			subset_reflexive.vo\
			equiv_reflexive.vo \
			belong_elements.vo \
			subset_transitive.vo \
			equiv_transitive.vo \
			subset_belong.vo \
			equiv_compatible.vo \
			union_compatible.vo \
			subset_compatible.vo \
			belong_compatible.vo

# set
set.vo: set.v
	coqc set.v

# order
order.vo: order.v \
	set.vo
	coqc order.v

# elements
elements.vo: elements.v \
	set.vo
	coqc elements.v

# order_elements
order_elements.vo: order_elements.v \
	set.vo \
	order.vo \
	elements.vo
	coqc order_elements.v

# subset
subset.vo: subset.v \
	set.vo \
	order.vo
	coqc subset.v

# belong
belong.vo: belong.v \
	set.vo \
	subset.vo 
	coqc belong.v

# equiv
equiv.vo: equiv.v \
	set.vo \
	subset.vo
	coqc equiv.v

# single_compatible
single_compatible.vo: single_compatible.v \
	set.vo \
	subset.vo \
	equiv.vo 
	coqc single_compatible.v

# subset_elements
subset_elements.vo: subset_elements.v \
	set.vo \
	elements.vo \
	subset.vo \
	equiv.vo 
	coqc subset_elements.v

# equiv_symmetric
equiv_symmetric.vo: equiv_symmetric.v \
	set.vo \
	subset.vo \
	equiv.vo
	coqc equiv_symmetric.v

# subset_reflexive
subset_reflexive.vo: subset_reflexive.v \
	set.vo \
	order.vo \
	order_elements.vo \
	subset.vo \
	equiv.vo \
	subset_elements.vo
	coqc subset_reflexive.v

# equiv_reflexive
equiv_reflexive.vo: equiv_reflexive.v \
	set.vo \
	equiv.vo \
	subset_reflexive.vo
	coqc equiv_reflexive.v

# belong_elements
belong_elements.vo: belong_elements.v \
	set.vo \
	elements.vo \
	subset.vo \
	belong.vo \
	equiv.vo \
	subset_elements.vo \
	equiv_reflexive.vo
	coqc belong_elements.v


# subset_transitive
subset_transitive.vo: subset_transitive.v \
	set.vo \
	order.vo \
	elements.vo \
	order_elements.vo \
	subset.vo \
	equiv.vo \
	subset_elements.vo \
	equiv_symmetric.vo \
	subset_reflexive.vo \
	equiv_reflexive.vo 
	coqc subset_transitive.v

# equiv_transitive
equiv_transitive.vo: equiv_transitive.v \
	set.vo \
	subset.vo \
	equiv.vo \
	subset_transitive.vo
	coqc equiv_transitive.v

# subset_belong
subset_belong.vo: subset_belong.v \
	set.vo \
	elements.vo \
	subset.vo \
	belong.vo \
	equiv.vo \
	subset_elements.vo \
	belong_elements.vo \
	equiv_transitive.vo
	coqc subset_belong.v

# equiv_compatible
equiv_compatible.vo: equiv_compatible.v \
	set.vo \
	equiv.vo \
	equiv_symmetric.vo \
	equiv_transitive.vo
	coqc equiv_compatible.v

# union_compatible
union_compatible.vo: union_compatible.v \
	set.vo \
	subset.vo \
	equiv.vo \
	subset_transitive.vo
	coqc union_compatible.v


# subset_compatible
subset_compatible.vo: subset_compatible.v \
	set.vo \
	subset.vo \
	equiv.vo \
	subset_transitive.vo
	coqc subset_compatible.v

# belong_compatible
belong_compatible.vo: belong_compatible.v \
	set.vo \
	subset.vo \
	belong.vo \
	equiv.vo \
	single_compatible.vo \
	subset_compatible.vo 
	coqc belong_compatible.v 


