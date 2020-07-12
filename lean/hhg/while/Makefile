all:						Env.olean \
							AExp.olean \
							BExp.olean


Env.olean :					Env.lean
	lean --make Env.lean

AExp.olean :				AExp.lean \
							Env.olean	
	lean --make AExp.lean

BExp.olean :				BExp.lean \
							Env.olean	
	lean --make BExp.lean


