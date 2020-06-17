def State : Type := string → ℕ

def bind (x : string) (n : ℕ) (s:State) : State :=
  λ v, if v = x then n else s v

-- The WHILE language
inductive stmt : Type
| skip    : stmt
| assign  : string → (State → ℕ) → stmt
| seq     : stmt → stmt → stmt
| ite     : (State → Prop) → stmt → stmt → stmt
| while   : (State → Prop) → stmt → stmt

infixr ` ;; ` : 90 := stmt.seq

open stmt

inductive BigStep : stmt → State → State → Prop
| SKIP : ∀ (s:State), BigStep skip s s
| ASN  : ∀ (x:string) (a:State → ℕ) (s:State), BigStep (assign x a) s (bind x (a s) s)
| SEQ  : ∀ (e₁ e₂:stmt) (s t u:State), BigStep e₁ s t → BigStep e₂ t u → BigStep (e₁ ;; e₂) s u
