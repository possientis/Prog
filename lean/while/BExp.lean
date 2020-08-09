import Env
import AExp

-- Shallow embedding for boolean expressions
def BExp : Type := Env -> Prop

-- A variable 'x' is read by a shallowly embedded boolean expression 'b', if and
-- only if, there is a environment 's' and an integer 'n' such that evaluating b in
-- s after binding x to n, makes a difference

def BRead (b:BExp) : set string :=
  {x | ∃ (s:Env)(n:ℕ), b (bindVar x (aNum n) s) ≠ b s }


