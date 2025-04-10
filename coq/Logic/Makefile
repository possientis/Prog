.PHONY : all clean

# Folder names
AXIOM = Axiom
CLASS = Class
FUNC  = Func
REL   = Rel
NAT	  = Nat
BOOL  = Bool
LIST  = List
FOL	  = Fol
FOL2  = Fol2
LAM   = Lam
SET   = Set
NORM  = Normal
LANG1 = Lang1
STLC  = STLC
PROP  = Prop

# coqc command line option
AXIOM_LIB = -Q ${AXIOM} Logic.${AXIOM} -Q . Logic
CLASS_LIB = -Q ${CLASS} Logic.${CLASS} -Q . Logic
FUNC_LIB  = -Q ${FUNC}  Logic.${FUNC}  -Q . Logic
REL_LIB   = -Q ${REL}   Logic.${REL}   -Q . Logic
NAT_LIB   = -Q ${NAT}   Logic.${NAT}   -Q . Logic
BOOL_LIB  = -Q ${BOOL}  Logic.${BOOL}  -Q . Logic
LIST_LIB  = -Q ${LIST}  Logic.${LIST}  -Q . Logic
FOL_LIB   = -Q ${FOL}   Logic.${FOL}   -Q . Logic
FOL2_LIB  = -Q ${FOL2}  Logic.${FOL2}  -Q . Logic
LAM_LIB   = -Q ${LAM}   Logic.${LAM}   -Q . Logic
SET_LIB   = -Q ${SET}   Logic.${SET}   -Q . Logic
LANG1_LIB = -Q ${LANG1} Logic.${LANG1} -Q . Logic
STLC_LIB  = -Q ${STLC}  Logic.${STLC}  -Q . Logic
PROP_LIB  = -Q ${PROP}  Logic.${PROP}  -Q . Logic
NORM_LIB  = -Q ${SET}/${NORM}   Logic.${SET}.${NORM}   -Q . Logic

# Object files
AXIOM_OBJ = ${AXIOM}/Extensionality.vo \
			${AXIOM}/Dec.vo \
			${AXIOM}/Wec.vo \
			${AXIOM}/LEM.vo \
			${AXIOM}/Sat.vo \
			${AXIOM}/CO.vo \
			${AXIOM}/Sec.vo \
			${AXIOM}/Markov.vo \
			${AXIOM}/Witness.vo \
			${AXIOM}/Post.vo \
			${AXIOM}/Reduction.vo

CLASS_OBJ = ${CLASS}/Ord.vo \
		   	${CLASS}/Eq.vo	

FUNC_OBJ  = ${FUNC}/Composition.vo \
			${FUNC}/Identity.vo \
			${FUNC}/Injective.vo \
			${FUNC}/Replace.vo \
			${FUNC}/Permute.vo

REL_OBJ   = ${REL}/Properties.vo \
			${REL}/Equiv.vo \
			${REL}/R.vo \
			${REL}/Id.vo \
			${REL}/Composition.vo \
			${REL}/Converse.vo \
			${REL}/Intersect.vo \
			${REL}/Include.vo \
			${REL}/Functional.vo \
			${REL}/Modularity.vo \
			${REL}/Total.vo \
			${REL}/Function.vo \
			${REL}/Embed.vo \
			${REL}/Shunting.vo \
			${REL}/Allegory.vo \
			${REL}/Sum.vo \
			${REL}/Product.vo \
			${REL}/Initial.vo \
			${REL}/Terminal.vo \
			${REL}/Coreflexive.vo \
			${REL}/Domain.vo \
			${REL}/Range.vo \
			${REL}/Prop.vo

NAT_OBJ   = ${NAT}/Eq.vo \
			${NAT}/Leq.vo \
			${NAT}/Ord.vo \
			${NAT}/Wec.vo \
			${NAT}/Dec.vo \
			${NAT}/Subset.vo \
			${NAT}/Max.vo \
			${NAT}/Weaken.vo \
			${NAT}/Plus.vo \
			${NAT}/Maximum.vo \
			${NAT}/Minimal.vo \
			${NAT}/Seq.vo \
			${NAT}/Fresh.vo \
			${NAT}/NatxNat.vo

BOOL_OBJ  = ${BOOL}/Eq.vo \
			${BOOL}/Three.vo

LIST_OBJ  = ${LIST}/In.vo \
		   	${LIST}/Nil.vo \
		   	${LIST}/Concat.vo \
		   	${LIST}/Include.vo \
		   	${LIST}/InjectiveOn.vo \
		   	${LIST}/Equiv.vo \
		   	${LIST}/Append.vo \
		   	${LIST}/Coincide.vo \
		   	${LIST}/Intersect.vo \
		   	${LIST}/Difference.vo \
		   	${LIST}/Replace.vo \
		   	${LIST}/Nub.vo \
		   	${LIST}/Sort.vo \
		   	${LIST}/Normal.vo \
		   	${LIST}/Filter.vo

FOL_OBJ   = ${FOL}/Syntax.vo \
			${FOL}/Order.vo \
			${FOL}/Functor.vo \
			${FOL}/Congruence.vo \
			${FOL}/Eq.vo \
			${FOL}/Variable.vo \
			${FOL}/Free.vo \
			${FOL}/Dmap.vo \
			${FOL}/Bound.vo \
			${FOL}/Subformula.vo \
			${FOL}/Valid.vo \
			${FOL}/LocalInv.vo \
			${FOL}/StrongAlpha.vo \
			${FOL}/Admissible.vo \
			${FOL}/Alpha.vo

FOL2_OBJ	= ${FOL2}/Context.vo \
					  ${FOL2}/Axiom.vo \
						${FOL2}/Proof.vo \
						${FOL2}/Monotone.vo \
						${FOL2}/Remove.vo	

LAM_OBJ   = ${LAM}/Syntax.vo \
			${LAM}/Order.vo \
			${LAM}/Subst.vo \
			${LAM}/Replace.vo \
			${LAM}/Functor.vo \
			${LAM}/Congruence.vo \
			${LAM}/Eq.vo \
			${LAM}/Variable.vo \
			${LAM}/Free.vo \
			${LAM}/Dmap.vo \
			${LAM}/Bound.vo \
			${LAM}/Subformula.vo \
			${LAM}/Valid.vo \
			${LAM}/BetaValid.vo \
			${LAM}/LocalInv.vo \
			${LAM}/StrongAlpha.vo \
			${LAM}/Admissible.vo \
			${LAM}/Alpha.vo

SET_OBJ   = ${SET}/Set.vo \
			${SET}/Order.vo \
			${SET}/Core.vo \
			${SET}/Incl.vo \
			${SET}/Elem.vo \
			${SET}/ToList.vo \
			${SET}/Trans.vo \
			${SET}/ElemIncl.vo \
			${SET}/Equal.vo \
			${SET}/Extensionality.vo \
			${SET}/Cons.vo \
			${SET}/Decidable.vo \
			${SET}/Empty.vo \
			${SET}/Pairing.vo \
			${SET}/Union.vo \
			${SET}/Intersection.vo \
			${SET}/Powerset.vo \
			${SET}/Rank.vo \
			${SET}/Compatible.vo \
			${SET}/Foundation.vo \
			${SET}/Functional.vo \
			${SET}/Replacement.vo \
			${SET}/Specification.vo

LANG1_OBJ = ${LANG1}/Syntax.vo \
			${LANG1}/Environment.vo \
			${LANG1}/Context.vo \
			${LANG1}/Semantics.vo \
			${LANG1}/SemanCtx.vo \
			${LANG1}/Relevance.vo \
			${LANG1}/Substitution.vo \
			${LANG1}/Apply.vo \
			${LANG1}/Compatible.vo \
			${LANG1}/ElemIncl.vo \
			${LANG1}/Trans.vo \
			${LANG1}/Incl.vo \
			${LANG1}/Equal.vo \
			${LANG1}/Extensionality.vo \
			${LANG1}/Empty.vo \
			${LANG1}/Pairing.vo \
			${LANG1}/Union.vo \
			${LANG1}/Powerset.vo \
			${LANG1}/Foundation.vo \
			${LANG1}/Specification.vo \
			${LANG1}/Replacement.vo

STLC_OBJ  = ${STLC}/Syntax.vo \
			${STLC}/Value.vo \
			${STLC}/Subst.vo \
			${STLC}/Replace.vo \
			${STLC}/Eval.vo \
			${STLC}/Example.vo \
			${STLC}/Context.vo \
			${STLC}/IsType.vo \
			${STLC}/Valid.vo \
			${STLC}/Valid2.vo \
			${STLC}/Typing.vo \
			${STLC}/Typing2.vo

PROP_OBJ = ${PROP}/Syntax.vo \
					 ${PROP}/Context.vo \
					 ${PROP}/Proof.vo \
					 ${PROP}/Lemma.vo \
					 ${PROP}/Eq.vo \
					 ${PROP}/Semantics.vo \
					 ${PROP}/Entails.vo \
					 ${PROP}/Sound.vo \
					 ${PROP}/Consistent.vo \
					 ${PROP}/Monotone.vo

NORM_OBJ  = ${SET}/${NORM}/Leq.vo \
			${SET}/${NORM}/Ord.vo \
			${SET}/${NORM}/InListOf.vo \
			${SET}/${NORM}/Equiv.vo \
			${SET}/${NORM}/Map.vo \
			${SET}/${NORM}/Nub.vo \
			${SET}/${NORM}/Insert.vo \
			${SET}/${NORM}/Sort.vo \
			${SET}/${NORM}/Normal.vo

# Overall target
all : 	${AXIOM_OBJ} \
		${CLASS_OBJ} \
		${FUNC_OBJ}	 \
		${REL_OBJ} \
		${NAT_OBJ} \
		${BOOL_OBJ} \
		${LIST_OBJ} \
		${FOL_OBJ} \
		${FOL2_OBJ} \
		${LAM_OBJ} \
		${SET_OBJ} \
		${LANG1_OBJ} \
		${STLC_OBJ} \
		${PROP_OBJ} \
		${NORM_OBJ}

# General rules
${AXIOM}/%.vo : ${AXIOM}/%.v
	coqc $< 		${AXIOM_LIB}

${CLASS}/%.vo : ${CLASS}/%.v
	coqc $< 		${CLASS_LIB}

${FUNC}/%.vo  : ${FUNC}/%.v
	coqc $< 		${FUNC_LIB}

${REL}/%.vo   : ${REL}/%.v
	coqc $< 		${REL_LIB}

${NAT}/%.vo   : ${NAT}/%.v
	coqc $< 		${NAT_LIB}

${BOOL}/%.vo  : ${BOOL}/%.v
	coqc $< 		${BOOL_LIB}

${LIST}/%.vo  : ${LIST}/%.v
	coqc $< 		${LIST_LIB}

${FOL}/%.vo   : ${FOL}/%.v
	coqc $< 		${FOL_LIB}

${FOL2}/%.vo   : ${FOL2}/%.v
	coqc $< 		${FOL2_LIB}

${LAM}/%.vo   : ${LAM}/%.v
	coqc $< 		${LAM_LIB}

${SET}/%.vo   : ${SET}/%.v
	coqc $< 		${LAM_LIB}

${LANG1}/%.vo : ${LANG1}/%.v
	coqc $< 		${LANG1_LIB}

${STLC}/%.vo  : ${STLC}/%.v
	coqc $< 		${STLC_LIB}

${PROP}/%.vo  : ${PROP}/%.v
	coqc $< 		${PROP_LIB}

${SET}/${NORM}/%.vo   : ${SET}/${NORM}/%.v
	coqc $< 	${NORM_LIB}

# Exception rules (for better output alignment)
${AXIOM}/Extensionality.vo : ${AXIOM}/Extensionality.v
	coqc $< 	${AXIOM_LIB}

${FUNC}/Composition.vo : ${FUNC}/Composition.v
	coqc $< 	${FUNC_LIB}

${REL}/R.vo : 		${REL}/R.v
	coqc $< 			${REL_LIB}

${REL}/Id.vo : 		${REL}/Id.v
	coqc $< 			${REL_LIB}

${REL}/Sum.vo : 	${REL}/Sum.v
	coqc $< 			${REL_LIB}

${NAT}/Eq.vo : ${NAT}/Eq.v
	coqc $<			${NAT_LIB}

${NAT}/Leq.vo : ${NAT}/Leq.v
	coqc $<			${NAT_LIB}

${NAT}/Wec.vo : ${NAT}/Wec.v
	coqc $<			${NAT_LIB}

${NAT}/Dec.vo : ${NAT}/Dec.v
	coqc $<			${NAT_LIB}

${NAT}/Ord.vo : ${NAT}/Ord.v
	coqc $<			${NAT_LIB}

${NAT}/Max.vo : ${NAT}/Max.v
	coqc $<			${NAT_LIB}

${NAT}/Seq.vo : ${NAT}/Seq.v
	coqc $<			${NAT_LIB}

${BOOL}/Eq.vo : ${BOOL}/Eq.v
	coqc $<			${BOOL_LIB}

${LIST}/In.vo : ${LIST}/In.v
	coqc $<			${LIST_LIB}

${LIST}/InjectiveOn.vo : ${LIST}/InjectiveOn.v
	coqc $<		${LIST_LIB}

${FOL}/Eq.vo : ${FOL}/Eq.v
	coqc $<			${FOL_LIB}

${LAM}/Eq.vo : ${LAM}/Eq.v
	coqc $<			${LAM_LIB}

${PROP}/Eq.vo : ${PROP}/Eq.v
	coqc $<			${PROP_LIB}

${SET}/Set.vo : ${SET}/Set.v
	coqc $<			${SET_LIB}

${SET}/Intersection.vo : ${SET}/Intersection.v
	coqc $<		${SET_LIB}

${SET}/Extensionality.vo : ${SET}/Extensionality.v
	coqc $<	${SET_LIB}

${SET}/Specification.vo : ${SET}/Specification.v
	coqc $<	${SET_LIB}

${LANG1}/Environment.vo : ${LANG1}/Environment.v
	coqc $<	${LANG1_LIB}

${LANG1}/Substitution.vo : ${LANG1}/Substitution.v
	coqc $<	${LANG1_LIB}

${LANG1}/Extensionality.vo : ${LANG1}/Extensionality.v
	coqc $<	${LANG1_LIB}

${LANG1}/Replacement.vo : ${LANG1}/Replacement.v
	coqc $<	${LANG1_LIB}

${LANG1}/Specification.vo : ${LANG1}/Specification.v
	coqc $<	${LANG1_LIB}

${LANG1}/Foundation.vo : ${LANG1}/Foundation.v
	coqc $<		${LANG1_LIB}

${LANG1}/Compatible.vo : ${LANG1}/Compatible.v
	coqc $<		${LANG1_LIB}

${SET}/${NORM}/Map.vo : ${SET}/${NORM}/Map.v
	coqc $<		${NORM_LIB}

${SET}/${NORM}/Leq.vo : ${SET}/${NORM}/Leq.v
	coqc $<		${NORM_LIB}

${SET}/${NORM}/Ord.vo : ${SET}/${NORM}/Ord.v
	coqc $<		${NORM_LIB}

${SET}/${NORM}/Nub.vo : ${SET}/${NORM}/Nub.v
	coqc $<		${NORM_LIB}

${SET}/${NORM}/Sort.vo : ${SET}/${NORM}/Sort.v
	coqc $<		${NORM_LIB}

deps :
	./deps.sh

include deps

clean :
	bash rm.sh
