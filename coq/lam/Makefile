all:	    eq.vo \
			utils.vo \
			identity.vo \
			composition.vo \
			index.vo \
			vequal.vo \
			injective.vo \
			map.vo \
			incl.vo \
			term.vo \
			var.vo \
			subst.vo \
			inj_on_list.vo \
			permute.vo \
			inj_on_term.vo \
			remove.vo \
			vmap.vo \
			swap.vo \
			free.vo \
			adpair.vo \
			alpha.vo \
			alpha2.vo

eq.vo:			eq.v
	coqc eq.v

utils.vo:		utils.v
	coqc utils.v

identity.vo:	identity.v
	coqc identity.v

composition.vo: composition.v
	coqc composition.v

index.vo: 		index.v eq.vo
	coqc index.v

vequal.vo:		vequal.v eq.vo index.vo
	coqc vequal.v

injective.vo:	injective.v \
				composition.vo
	coqc injective.v

map.vo: 		map.v
	coqc map.v

incl.vo:		incl.v \
				eq.vo
	coqc incl.v

term.vo:		term.v
	coqc term.v

var.vo:			var.v \
				term.vo
	coqc var.v

subst.vo:		subst.v	\
				eq.vo term.vo
	coqc subst.v

inj_on_list.vo:	inj_on_list.v \
				injective.vo incl.vo 
	coqc inj_on_list.v

permute.vo:		permute.v \
				eq.vo utils.vo injective.vo
	coqc permute.v

inj_on_term.vo:	inj_on_term.v \
				inj_on_list.vo term.vo var.vo
	coqc inj_on_term.v

remove.vo:		remove.v \
				eq.vo incl.vo inj_on_list.vo
	coqc remove.v

vmap.vo: 		vmap.v \
				eq.vo identity.vo term.vo permute.vo
	coqc vmap.v

swap.vo:		swap.v \
				eq.vo composition.vo injective.vo \
				term.vo permute.vo vmap.vo
	coqc swap.v

free.vo:		free.v \
				eq.vo injective.vo incl.vo term.vo var.vo \
				inj_on_list.vo permute.vo inj_on_term.vo \
				remove.vo vmap.vo swap.vo
	coqc free.v

adpair.vo:		adpair.v \
				eq.vo injective.vo term.vo free.vo
	coqc adpair.v

alpha.vo : 		alpha.v \
				eq.vo identity.vo composition.vo injective.vo \
				map.vo incl.vo term.vo var.vo inj_on_list.vo \
				remove.vo free.vo vmap.vo utils.vo var.vo permute.vo \
				inj_on_term.vo adpair.vo
	coqc alpha.v

alpha2.vo :	alpha2.v eq.vo term.vo vequal.vo alpha.vo index.vo
	coqc alpha2.v


