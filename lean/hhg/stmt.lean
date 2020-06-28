def Env  : Type := string → ℕ

lemma L0 : "x" ≠ "y" :=
begin
  from dec_trivial  -- remember this, do not use 'cases' tactic on string
end

-- Shallow embedding for arithmetic expressions. Some function Env → ℕ, not interested in syntax, semantics etc
def AExp : Type := Env → ℕ

-- Shallow embedding for boolean expressions. Actually using Prop rather than bool
def BExp : Type := Env → Prop

def bindVar (x : string) (n : AExp) (s:Env) : Env :=
  λ v, if v = x then n s else s v

open list

def env : list (string × ℕ) → Env
| []        := λ s, 0
| ((v,n) :: xs) := λ s, if s = v then n else env xs s

def aNum (n : ℕ) : AExp := λ _, n
def aVar (x : string) : AExp := λ s, s x
def x : AExp := aVar "x"
def y : AExp := aVar "y"
def z : AExp := aVar "z"

def aPlus  (m n : AExp) : AExp := λ s, m s + n s

-- The WHILE language: deep embedding for actual language: full syntax and semantics specified
inductive stmt : Type
| skip    : stmt
| assign  : string → AExp → stmt
| seq     : stmt → stmt → stmt
| ite     : BExp → stmt → stmt → stmt
| while   : BExp → stmt → stmt

open stmt

infixr ` ;; `  : 70 := seq
infix ` :== `  : 80 := assign
infixl ` :+: ` : 90 := aPlus

-- Big step semantics as a relation over Env
inductive BigStep : stmt → Env → Env → Prop
| SKIP    : ∀ (s:Env), BigStep skip s s
| ASN     : ∀ (x:string) (a:AExp) (s:Env), BigStep (assign x a) s (bindVar x a s)
| SEQ     : ∀ (e₁ e₂:stmt) (s u t:Env), BigStep e₁ s u → BigStep e₂ u t → BigStep (e₁ ;; e₂) s t
| IF_T    : ∀ (p:Env → Prop) (e₁ e₂:stmt) (s t:Env), p s → BigStep e₁ s t → BigStep (ite p e₁ e₂) s t
| IF_F    : ∀ (p:Env → Prop) (e₁ e₂:stmt) (s t:Env), ¬(p s) → BigStep e₂ s t → BigStep (ite p e₁ e₂) s t
| WHILE_T : ∀ (p:Env → Prop) (e₁:stmt) (s u t:Env), p s → BigStep e₁ s u → BigStep (while p e₁) u t → BigStep (while p e₁) s t
| WHILE_F : ∀ (p:Env → Prop) (e₁:stmt) (s:Env), ¬(p s) → BigStep (while p e₁) s s

def s0 : Env := env [("x",3),("y",5)]
def s1 : Env := env [("x",8),("y",5)]
def s2 : Env := env [("x",8),("y",0)]

lemma L1 : s1 = bindVar "x" (x :+: y) s0 :=
begin
  apply funext, unfold s1 s0 aPlus x y aVar env bindVar,
  intros s, cases decidable.em (s = "x") with H1 H1,
    {rewrite H1, simp, cases decidable.em ("y" = "x") with H2 H2,
      {exfalso, revert H2, from dec_trivial},
      {simp *}},
    {simp *}
end

lemma L2 : s2 = bindVar "y" (aNum 0) s1 :=
begin
  apply funext, unfold s2, unfold s1, unfold aNum, unfold env, unfold bindVar,
  intros s, cases decidable.em (s = "x") with H1 H1,
    {rewrite H1, simp, cases decidable.em ("x" = "y") with H2 H2,
      {exfalso, revert H2, from dec_trivial},
      {simp *}},
    {simp *, cases decidable.em (s = "y") with H2 H2,
      {rewrite H2, simp},
      {simp *}}
end

open BigStep

def e1 : stmt := "x" :== (x :+: y) ;; "y" :== aNum 0

lemma L3 : BigStep e1 s0 s2 :=
begin
  apply (SEQ _ _ s0 s1 s2),
    {rewrite L1, constructor},
    {rewrite L2, constructor}
end

theorem BigStepDeterministic : ∀ (e:stmt) (s s1 s2:Env),
  BigStep e s s1 → BigStep e s s2 → s1 = s2 :=
begin
  intros e s s1 s2 H1, revert s2,
  induction H1 with s2 x a s2 e1 e2 s1' s2 s3 H1 H2 IH1 IH2 b e1 e2 s1 s2 H1 H2 IH1,
    {intros s2' H, cases H, refl},
    {intros s2' H, cases H, refl},
    {intros s3' H, cases H, have H2 : s2 = H_u, -- not able to qualify cases with names so have to use generated namesi, seems like a bug
      {apply IH1, assumption},
      {rewrite ← H2 at H_a_1, apply IH2, assumption}},
    {intros s2' H, cases H,
      {apply IH1, assumption},
      {exfalso, apply H_a, assumption}},
    {},
    {},
    {},
end
