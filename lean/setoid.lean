universe u

class setoid2 (α : Sort u) : Sort (max 1 u) :=
  (r : α → α → Prop) (iseqv : equivalence r)

--#check @setoid
--#check @setoid2
--#check (@setoid.iseqv α s).left

--#check @quot

def quotient2 {α : Sort u} (s : setoid α) := @quot α setoid.r

--#check @quotient
--#check @quotient2

--#check @quotient.mk
--#check @quotient.ind
--#check @quotient.lift   -- ≈ is \~~ or \approx
--#check @quotient.sound  -- ⟦ is \[[ , ⟧ is \]]
--#check @quotient.exact

def eqv {α : Type u} (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

infix `~` := eqv

lemma eqv_refl : ∀ {α : Type u} {p : α × α}, p ~ p :=
begin
  intros a p, left, split; reflexivity
end


lemma eqv_symm : ∀ {α : Type u} {p q : α × α}, p ~ q → q ~ p :=
begin
  intros α p q H, cases H with H H,
    {cases H with H1 H2, left, split; symmetry; assumption},
    {cases H with H1 H2, right, split; symmetry; assumption}
end

lemma eqv_trans : ∀ {α : Type u} {p q r : α × α}, p ~ q → q ~ r → p ~ r :=
begin
  intros α p q r H1 H2, cases H1 with H1 H1; cases H2 with H2 H2;
  cases H1 with H1 H3; cases H2 with H2 H4,
    { left,  split; apply eq.trans; assumption},
    { right, split; apply eq.trans; assumption},
    { right, split; apply eq.trans; assumption},
    { left,  split; apply eq.trans; assumption},
end

lemma eqv_equivalence : ∀ {α : Type u}, equivalence (@eqv α) :=
begin
  intros α, apply mk_equivalence,
    { apply eqv_refl},
    { apply eqv_symm},
    { apply eqv_trans},
end

instance uprod.setoid (α : Type u) : setoid (α × α) :=
  setoid.mk (@eqv α) (eqv_equivalence)

-- set of unordered pairs defined as a quotient set
definition uprod (α : Type u) : Type u := quotient (uprod.setoid α)

definition uprod.mk {α : Type u} (x y : α) : uprod α := ⟦(x,y)⟧

notation `{` x `,` y `}` := uprod.mk x y

lemma L1 : ∀ {α : Type u} (x y : α), { x , y } = { y , x } :=
begin
  intros α x y, apply quotient.sound, right, split; reflexivity
end

private definition mem_fn {α : Type u} (x : α) (p : α × α) : Prop :=
  match p with
    (x₁,x₂) := x = x₁ ∨ x = x₂
  end

private lemma mem_swap : ∀ {α : Type u} (x : α) (p : α × α),
  mem_fn x p = mem_fn x (p.2,p.1) :=
begin
  intros α x p, cases p with x₁ x₂, apply propext, split; intros H; cases H with H H,
  {right, assumption},
  {left, assumption},
  {right, assumption},
  {left, assumption}
end

private lemma mem_respect : ∀ {α : Type u} (p₁ p₂ : α × α) (x : α),
  p₁ ≈ p₂ → mem_fn x p₁ = mem_fn x p₂ :=
begin
  intros α p₁ p₂ x H, cases H with H H; cases H with H1 H2,
    {cases p₁ with x₁ y₁, cases p₂ with x₂ y₂, unfold mem_fn,
     simp at H1, simp at H2, rewrite H1, rewrite H2},
    {cases p₂ with x₂ y₂, simp at H1, simp at H2, rewrite ← H1, rewrite ← H2,
     apply mem_swap}
end




