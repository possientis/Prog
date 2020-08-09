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

-- set of variables read by a thread
def R  : Stmt → set string
| skip          := ∅
| (_ :== a)     := ARead a
| (e₁ ;; e₂)    := R e₁ ∪ R e₂
| (ite b e₁ e₂) := BRead b ∪ R e₁ ∪ R e₂
| (while b e₁)  := BRead b ∪ R e₁

-- set of variables written or read by a thread
def V (e:Stmt) : set string := W e ∪ R e


