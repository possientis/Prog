all:					void.agdai \
						level.agdai \
						maybe.agdai \
						func.agdai \
						prod.agdai \
   						id.agdai \
						nat.agdai \
						plus.agdai \
						mult.agdai \
						sum.agdai \
						le.agdai \
						lt.agdai \
						bool.agdai \
						list.agdai \
						vector.agdai \
						min-max.agdai \
						relations.agdai \
						sigma.agdai \
						square.agdai \
						rewrite-test.agdai \
						with-abstraction.agdai \
						bst.agdai \
						z.agdai \
						reflect-list.agdai \
						combinator.agdai \
						vcombinator.agdai \
						formula.agdai \
						kripke.agdai

void.agdai : 			void.agda
	agda -v0 void.agda

level.agdai : 			level.agda
	agda -v0 level.agda

maybe.agdai : 			maybe.agda
	agda -v0 maybe.agda

func.agdai : 			func.agda
	agda -v0 func.agda

prod.agdai :			prod.agda
	agda -v0 prod.agda

id.agdai : 				id.agda \
						void.agdai
	agda -v0 id.agda

nat.agdai :				nat.agda \
						id.agdai \
						sum.agdai \
						void.agdai 
	agda -v0 nat.agda

plus.agdai :			plus.agda \
						le.agdai \
						lt.agdai \
						id.agdai \
						nat.agdai
	agda -v0 plus.agda

mult.agdai :			mult.agda \
						id.agdai \
						nat.agdai \
						plus.agdai
	agda -v0 mult.agda

sum.agdai : 			sum.agda \
   						id.agdai \
						void.agdai	
	agda -v0 sum.agda

le.agdai :				le.agda \
						id.agdai \
						nat.agdai \
						sum.agdai \
						void.agdai \
						min-max.agdai
	agda -v0 le.agda

lt.agdai :				lt.agda \
						le.agdai \
						nat.agdai \
						void.agdai
	agda -v0 lt.agda

bool.agdai :			bool.agda \
			 			id.agdai \
						sum.agdai \
						void.agdai	
	agda -v0 bool.agda

list.agdai :			list.agda \
						id.agdai \
						le.agdai \
						nat.agdai \
						func.agdai \
						bool.agdai \
						void.agdai \
						plus.agdai \
						maybe.agdai
	agda -v0 list.agda

vector.agdai :			vector.agda \
						id.agdai \
						lt.agdai \
						nat.agdai \
						bool.agdai \
						plus.agdai \
						mult.agdai \
						list.agdai
	agda -v0 vector.agda

min-max.agdai :			min-max.agda \
						id.agdai \
						sum.agdai \
						relations.agdai
	agda -v0 min-max.agda

relations.agdai :		relations.agda \
						id.agdai \
						sum.agdai \
						void.agdai
	agda -v0 relations.agda

sigma.agdai :			sigma.agda \
						id.agdai \
						nat.agdai \
						plus.agdai \
						void.agdai \
						list.agdai \
						vector.agdai 
	agda -v0 sigma.agda

square.agdai :			square.agda \
						id.agdai \
						nat.agdai \
						mult.agdai
	agda -v0 square.agda

rewrite-test.agdai :	rewrite-test.agda \
						id.agdai \
						nat.agdai \
						plus.agdai
	agda -v0 rewrite-test.agda

with-abstraction.agdai:	with-abstraction.agda \
						bool.agdai \
						list.agdai
	agda -v0 with-abstraction.agda
						
bst.agdai :				bst.agda \
						id.agdai \
						sum.agdai \
						relations.agdai \
						maybe.agdai \
						min-max.agdai
	agda -v0 bst.agda

z.agdai :				z.agda \
						id.agdai \
						le.agdai \
						lt.agdai \
						nat.agdai \
						sum.agdai \
						plus.agdai \
						bool.agdai \
						void.agdai
	agda -v0 z.agda

reflect-list.agdai :	reflect-list.agda \
						id.agdai \
						nat.agdai \
						sum.agdai \
						func.agdai \
						bool.agdai \
						list.agdai \
						prod.agdai \
						level.agdai
	agda -v0 reflect-list.agda

combinator.agdai :		combinator.agda \
						le.agdai \
						lt.agdai \
						nat.agdai \
						bool.agdai
	agda -v0 combinator.agda

vcombinator.agdai :		vcombinator.agda \
						nat.agdai
	agda -v0 vcombinator.agda
	

formula.agdai : formula.agda \
				nat.agdai \
				list.agdai
	agda -v0 formula.agda

kripke.agdai : 	kripke.agda \
				level.agdai \
				nat.agdai
	agda -v0 kripke.agda	
