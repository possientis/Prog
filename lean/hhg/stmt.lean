def State : Type := string → ℕ

def bindVar (x : string) (n : ℕ) (s:State) : State :=
  λ v, if v = x then n else s v

open list

def env : list (string × ℕ) → State
| []        := λ s, 0
| ((v,n) :: xs) := λ s, if s = v then n else env xs s


-- The WHILE language: deep embedding for actual language: full syntax and semantics specified
inductive stmt : Type
| skip    : stmt
| assign  : string → (State → ℕ) → stmt         -- shallow embedding for arithmetic expressions. Some function State → ℕ, not interested in syntax, semantics etc
| seq     : stmt → stmt → stmt
| ite     : (State → Prop) → stmt → stmt → stmt -- shallow embedding for boolean expressions. Actually using Prop rather than bool
| while   : (State → Prop) → stmt → stmt

infixr ` ;; ` : 90 := stmt.seq


open stmt

-- Big step semantics as a relation over State
inductive BigStep : stmt → State → State → Prop
| SKIP    : ∀ (s:State), BigStep skip s s
| ASN     : ∀ (x:string) (a:State → ℕ) (s:State), BigStep (assign x a) s (bindVar x (a s) s)
| SEQ     : ∀ (e₁ e₂:stmt) (s u t:State), BigStep e₁ s u → BigStep e₂ u t → BigStep (e₁ ;; e₂) s t
| IF_T    : ∀ (p:State → Prop) (e₁ e₂:stmt) (s t:State), p s → BigStep e₁ s t → BigStep (ite p e₁ e₂) s t
| IF_F    : ∀ (p:State → Prop) (e₁ e₂:stmt) (s t:State), ¬(p s) → BigStep e₂ s t → BigStep (ite p e₁ e₂) s t
| WHILE_T : ∀ (p:State → Prop) (e₁:stmt) (s u t:State), p s → BigStep e₁ s u → BigStep (while p e₁) u t → BigStep (while p e₁) s t
| WHILE_F : ∀ (p:State → Prop) (e₁:stmt) (s:State), ¬(p s) → BigStep (while p e₁) s s

def s0 : State := env [("x",3),("y",5)]
def s1 : State := env [("x",8),("y",5)]
def s2 : State := env [("x",8),("y",0)]

def a0 : State → ℕ := λ s, s "x" + s "y"
def a1 : State → ℕ := λ _, 0

def e1 : stmt := assign "x" a0 ;; assign "y" a1

lemma L1 : s1 = bindVar "x" (a0 s0) s0 :=
begin
  apply funext, unfold s1, unfold s0, unfold a0, unfold env, unfold bindVar,
  intros s, cases decidable.em (s = "x") with H1 H1,
    {rewrite H1, simp, cases decidable.em ("y" = "x") with H2 H2,
      {cases H2},
      {simp *}},
    {simp *}
end

lemma L2 : s2 = bindVar "y" (a1 s1) s1 :=
begin
  apply funext, unfold s2, unfold s1, unfold a1, unfold env, unfold bindVar,
  intros s, cases decidable.em (s = "x") with H1 H1,
    {rewrite H1, simp, cases decidable.em ("x" = "y") with H2 H2,
      {cases H2},
      {simp *}},
    {simp *, cases decidable.em (s = "y") with H2 H2,
      {rewrite H2, simp},
      {simp *}}
end

open BigStep

lemma L3 : BigStep e1 s0 s2 :=
begin
  apply (SEQ _ _ s0 s1 s2),
    {rewrite L1, constructor},
    {rewrite L2, constructor}
end
