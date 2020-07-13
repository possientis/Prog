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


