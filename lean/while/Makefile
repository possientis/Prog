all:						Env.olean \
							AExp.olean \
							BExp.olean \
							Stmt.olean \
							BigStep.olean \
							Reduction.olean


Env.olean :					Env.lean
	lean --make Env.lean

AExp.olean :				AExp.lean \
							Env.olean	
	lean --make AExp.lean

BExp.olean :				BExp.lean \
							Env.olean	
	lean --make BExp.lean

Stmt.olean :				Stmt.lean \
							Env.olean \
							AExp.olean \
							BExp.olean
	lean --make Stmt.lean

BigStep.olean : 			BigStep.lean \
							Stmt.olean
	lean --make BigStep.lean

Reduction.olean : 			Reduction.lean \
							Stmt.olean
	lean --make Reduction.lean


