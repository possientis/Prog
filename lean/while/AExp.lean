import Env

-- Shallow embedding for arithmetic expressions
def AExp : Type := Env → ℕ

def bindVar (x : string) (n : AExp) (s:Env) : Env :=
  λ v, if v = x then n s else s v

def aNum (n : ℕ) : AExp := λ _, n
def aVar (x : string) : AExp := λ s, s x
def x : AExp := aVar "x"
def y : AExp := aVar "y"
def z : AExp := aVar "z"

def aPlus  (m n : AExp) : AExp := λ s, m s + n s

-- A variable 'x' is read by a shallowly embedded arithmetic expression 'a', if and
-- only if, there is a environment 's' and an integer 'n' such that evaluating a in
-- s after binding x to n, makes a difference

def ARead (a:AExp) : set string :=
  {x | ∃ (s:Env)(n:ℕ), a (bindVar x (aNum n) s) ≠ a s }


