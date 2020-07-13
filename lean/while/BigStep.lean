import Stmt

open Stmt

-- Big step semantics as a relation over Env
inductive BigStep : Stmt → Env → Env → Prop
| SKIP    : ∀ (s:Env), BigStep skip s s
| ASN     : ∀ (x:string) (a:AExp) (s:Env), BigStep (x :== a) s (bindVar x a s)
| SEQ     : ∀ (e₁ e₂:Stmt) (s u t:Env),
    BigStep e₁ s u →
    BigStep e₂ u t →
    BigStep (e₁ ;; e₂) s t
| IF_T    : ∀ (b:BExp) (e₁ e₂:Stmt) (s t:Env),
    b s →
    BigStep e₁ s t
    → BigStep (ite b e₁ e₂) s t
| IF_F    : ∀ (b:BExp) (e₁ e₂:Stmt) (s t:Env),
    ¬(b s) →
    BigStep e₂ s t →
    BigStep (ite b e₁ e₂) s t
| WHILE_T : ∀ (b:BExp) (e₁:Stmt) (s u t:Env),
    b s →
    BigStep e₁ s u →
    BigStep (while b e₁) u t →
    BigStep (while b e₁) s t
| WHILE_F : ∀ (b:BExp) (e₁:Stmt) (s:Env),
    ¬(b s) →
    BigStep (while b e₁) s s

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

def e1 : Stmt := "x" :== (x :+: y) ;; "y" :== aNum 0

lemma L3 : BigStep e1 s0 s2 :=
begin
  apply (SEQ _ _ s0 s1 s2),
    {rewrite L1, constructor},
    {rewrite L2, constructor}
end

theorem BigStepDeterministic : ∀ (e:Stmt) (s s1 s2:Env),
  BigStep e s s1 → BigStep e s s2 → s1 = s2 :=
begin
  intros e s s1 s2 H1, revert s2,
  induction H1 with
    s2 x a
    s2 e1 e2
    s1' s2 s3 H1 H2 IH1 IH2
    b e1 e2 s1 s2 H1 H2 IH1
    b e1 e2 s1 s2 H1 H2 IH1
    b e1 s1 s2 s3 H1 H2 H3 IH1 IH2
    b e1 s1 H1,
    {intros s2' H, cases H, refl},
    {intros s2' H, cases H, refl},
    {intros s3' H, cases H with x x x x x x x s2' _ H1 H2,
     have H3 : s2 = s2',
      {apply IH1, assumption},
      {apply IH2, rewrite H3, assumption}
     },
    {intros s2' H, cases H,
      {apply IH1, assumption},
      {exfalso, apply H_a, assumption}},
    {intros s2' H, cases H,
      {exfalso, apply H1, assumption},
      {apply IH1, assumption}},
    {intros s3' H, cases H,
      {have H4 : s2 = H_u,
        {apply IH1, assumption},
        {rewrite ← H4 at H_a_2, apply IH2, assumption}},
      {exfalso, apply H_a, assumption}},
    {intros s2' H, cases H,
      {exfalso, apply H1, assumption},
      {refl}},
end
lemma BigStepDoesNotTerminate : ∀ (e : Stmt) (s1 s2 : Env),
  ¬BigStep (while (λ_, true) e) s1 s2 :=
begin
  intros e s1 s2 H, generalize H1 : while (λ_, true) e = e1,
  rewrite H1 at H, revert e, induction H with
    s1
    x a s1
    e1 e2 s1 s2 s3 H1 H2 IH1 IH2
    b e1 e2 s1 s2 H1 H2 IH1
    b e1 e2 s1 s2 H1 H2 IH1
    b e1 s1 s2 s3 H1 H2 H3 IH1 IH2
    b e1 s1 H2;
    intros e H1,
    {cases H1},
    {cases H1},
    {cases H1},
    {cases H1},
    {cases H1},
    {cases H1, apply IH2; refl},
    {cases H1, apply H2, trivial},
  end

-- inversion rules

@[simp] lemma BigStepSkipIff : ∀ {s t:Env}, BigStep skip s t ↔ s = t :=
begin
  intros s t, split; intros H,
    { cases H, refl },
    { rewrite H, constructor }
end

@[simp] lemma BigStepAssignIff : ∀ {x:string} {a:AExp} {s t:Env},
  BigStep (x :== a) s t ↔ t = bindVar x a s :=
begin
  intros x a s t, split; intros H,
    { cases H, unfold bindVar },
    { rewrite H, constructor }
end

@[simp] lemma BigStepSeqIff : ∀ {e1 e2:Stmt} {s t:Env},
  BigStep (e1 ;; e2) s t ↔ ∃ (u:Env), BigStep e1 s u ∧ BigStep e2 u t :=
begin
  intros e1 e2 s t, split; intros H,
    {cases H with _ _ _ _ _ _ _ u _ H1 H2, existsi u, split; assumption},
    {cases H with u H1, cases H1 with H1 H2, constructor; assumption}
end

@[simp] lemma BigStepIteIff : ∀ {b:BExp} {e1 e2:Stmt} {s t:Env},
  BigStep (ite b e1 e2) s t ↔ (b s ∧ BigStep e1 s t) ∨ (¬b s ∧ BigStep e2 s t) :=
begin
  intros b e1 e2 s t, split; intros H,
    {cases H with _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2,
      {left, split; assumption},
      {right, split; assumption}},
    {cases H with H H,
      {cases H with H1 H2, constructor; assumption},
      {cases H with H1 H2, apply IF_F; assumption}}
end

-- rhs has term which matches lhs, leaving out @[simp] to avoid potential loop
lemma BigStepWhileIff : ∀ {b:BExp} {e:Stmt} {s t: Env},
  BigStep (while b e) s t ↔
  (b s ∧ ∃ (u:Env), BigStep e s u ∧ BigStep (while b e) u t) ∨ (¬ b s ∧ s = t) :=
begin
  intros b e s t, split; intros H,
    { cases H with _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        u _ H1 H2 H3 _ _ _ H1,
      { left, split,
        { assumption },
        { existsi u, split; assumption }},
      { right, split,
        { assumption },
        { refl }}},
    { cases H with H H,
      { cases H with H1 H2, cases H2 with u H2, cases H2 with H2 H3,
        constructor; assumption },
      { cases H with H1 H2, rw H2, apply WHILE_F, rw H2 at H1, assumption}}
end

-- rhs has term which matches lhs, leaving out @[simp] to avoid potential loop
lemma BigStepWhileTrueIff : ∀ {b:BExp} {e:Stmt} {s t:Env}, b s →
  (BigStep (while b e) s t ↔ (∃ (u:Env), BigStep e s u ∧ BigStep (while b e) u t)) :=
begin
  intros b e s t H1, split; intros H2,
    { cases H2 with _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        u _ H2 H3 H4 _ _ _ H3,
      { existsi u, split; assumption },
      { exfalso, apply H3, assumption }},
    { cases H2 with u H2, cases H2 with H2 H3, constructor; assumption}
end

@[simp] lemma BigStepWhileFalseIff : ∀ {b:BExp} {e:Stmt} {s t:Env}, ¬ b s →
  (BigStep (while b e) s t ↔ s = t) :=
begin
  intros b e s t H1, split; intros H2,
    { cases H2 with _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
       u _ H2 H3 H4,
      { exfalso, apply H1, assumption },
      { refl }},
    { rw H2, apply WHILE_F, rw H2 at H1, assumption }
end

