import Env
import AExp
import BExp

-- The WHILE language: deep embedding for actual language: full syntax and semantics specified
inductive Stmt : Type
| skip    : Stmt
| assign  : string → AExp → Stmt
| seq     : Stmt → Stmt → Stmt
| ite     : BExp → Stmt → Stmt → Stmt
| while   : BExp → Stmt → Stmt

open Stmt

infixr ` ;; `  : 70 := seq
infix ` :== `  : 80 := assign
infixl ` :+: ` : 90 := aPlus

-- set of variables written by a thread
def W  : Stmt → set string
| skip          := ∅
| (x :== _)     := {x}
| (e₁ ;; e₂)    := W e₁ ∪ W e₂
| (ite _ e₁ e₂) := W e₁ ∪ W e₂
| (while _ e₁)  := W e₁


