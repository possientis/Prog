all:						Env.olean \
							AExp.olean \
							BExp.olean \
							Subst.olean \
							Stmt.olean \
							BigStep.olean \
							Reduce.olean \
							CloReduce.olean \
							BigStepEquiv.olean \
							HoareSyntax.olean \
							Soundness.olean


Env.olean :					Env.lean
	lean --make Env.lean

AExp.olean :				AExp.lean \
							Env.olean	
	lean --make AExp.lean

BExp.olean :				BExp.lean \
							Env.olean	
	lean --make BExp.lean

Subst.olean :				Subst.lean \
							Env.olean \
							AExp.olean
	lean --make Subst.lean

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



HoareSyntax.olean :			HoareSyntax.lean \
							Stmt.olean \
							Subst.olean
	lean --make HoareSyntax.lean

Soundness.olean : 			Soundness.lean \
							HoareSyntax.olean \
							BigStep.olean
	lean --make Soundness.lean
