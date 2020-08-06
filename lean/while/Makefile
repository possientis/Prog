all:						Env.olean \
							AExp.olean \
							BExp.olean \
							Stmt.olean \
							BigStep.olean \
							Reduce.olean \
							CloReduce.olean \
							BigStepEquiv.olean


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

Reduce.olean : 				Reduce.lean \
							Stmt.olean
	lean --make Reduce.lean

CloReduce.olean : 			CloReduce.lean \
							Stmt.olean \
							Reduce.olean
	lean --make CloReduce.lean

BigStepEquiv.olean : 		BigStepEquiv.lean \
							Stmt.olean \
							BigStep.olean \
							Reduce.olean \
							CloReduce.olean
	lean --make BigStepEquiv.lean
