all:  subset_transitive.vo \
			equiv_transitive.vo \
			subset_compatible.vo

##########################################################################
#                              set                                       #
##########################################################################
set.vo: set.v
	coqc set.v

##########################################################################
#                             order                                      #
##########################################################################
order.vo: order.v \
	set.vo
	coqc order.v

##########################################################################
#                             subset                                     #
##########################################################################

subset.vo: subset.v \
	set.vo \
	order.vo
	coqc subset.v

##########################################################################
#                             equiv                                      #
##########################################################################

equiv.vo: equiv.v \
	set.vo \
	subset.vo
	coqc equiv.v

##########################################################################
#                            equiv_symmetric                             #
##########################################################################

equiv_symmetric.vo: equiv_symmetric.v \
	set.vo \
	subset.vo \
	equiv.vo
	coqc equiv_symmetric.v


##########################################################################
#                             elements                                   #
##########################################################################
elements.vo: elements.v \
	set.vo \
	order.vo \
	subset.vo \
	equiv.vo 
	coqc elements.v

##########################################################################
#                           subset_reflexive                             #
##########################################################################
subset_reflexive.vo: subset_reflexive.v \
	set.vo \
	order.vo \
	subset.vo \
	equiv.vo  \
	elements.vo
	coqc subset_reflexive.v

##########################################################################
#                           equiv_reflexive                              #
##########################################################################
equiv_reflexive.vo: equiv_reflexive.v \
	set.vo \
	equiv.vo \
	subset_reflexive.vo
	coqc equiv_reflexive.v

##########################################################################
#                           subset_transitive                            #
##########################################################################
subset_transitive.vo: subset_transitive.v \
	set.vo \
	order.vo \
	subset.vo \
	equiv.vo \
	elements.vo \
	subset_reflexive.vo \
	equiv_reflexive.vo \
	equiv_symmetric.vo

	coqc subset_transitive.v

##########################################################################
#                           equiv_transitive                             #
##########################################################################
equiv_transitive.vo: equiv_transitive.v \
	set.vo \
	subset.vo \
	equiv.vo \
	subset_transitive.vo

	coqc equiv_transitive.v

##########################################################################
#                          subset_compatible                             #
##########################################################################
subset_compatible.vo: subset_compatible.v \
	set.vo \
	subset.vo \
	equiv.vo \
	subset_transitive.vo

	coqc subset_compatible.v




