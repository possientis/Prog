def is_not_zero (n : ℕ) : bool :=
  match n with
  | 0       := ff
  | (n + 1) := tt
  end

universe u

def filter {α : Type u} (p: α → bool): list α → list α
| [] := []
| (x :: xs) :=
  match p x with
  | tt  := x :: filter xs
  | ff  := filter xs
  end

example : filter is_not_zero [1,0,0,3,0] = [1,3] := rfl

def foo (n : ℕ) (b c : bool) : ℕ := 5 +
  match n - 5 , b && c with
  | 0,     tt := 0
  | m + 1, tt := m + 7
  | 0,     ff := 5
  | m + 1, ff := m + 3
  end

#eval foo 7 tt ff

example : foo 7 tt ff = 9 := rfl

def bar₁ : ℕ × ℕ → ℕ
| (m, n) := m + n

def bar₂ (p : ℕ × ℕ) : ℕ :=
  match p with (m, n) := m + n end

def bar₃ : ℕ × ℕ → ℕ :=
  λ ⟨m,n⟩, m + n

def bar₄ (p : ℕ × ℕ) : ℕ :=
  let ⟨m,n⟩ := p in m + n


example (p q : ℕ → Prop) : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y
| ⟨x, px⟩ ⟨y, qy⟩ := ⟨x, y, px, qy⟩


example (p q : ℕ → Prop) : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y
| ⟨x, px⟩ ⟨y, qy⟩ := ⟨x, ⟨y, ⟨px, qy⟩⟩⟩

example (p q : ℕ → Prop) (H1 : ∃ x, p x) (H2: ∃ y, q y) : ∃ x y, p x ∧ q y :=
  match H1, H2 with
  | ⟨x, px⟩, ⟨y, qy⟩ := ⟨x, y, px, qy⟩
  end

example (p q : ℕ → Prop) : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y :=
  λ ⟨x, px⟩ ⟨y, qy⟩, ⟨x, y, px, qy⟩

example (p q : ℕ → Prop) (H1 : ∃ x, p x) (H2: ∃ y, q y) : ∃ x y, p x ∧ q y :=
  let ⟨x, px⟩ := H1, ⟨y, qy⟩ := H2 in ⟨x, y, px, qy⟩

open function

#print surjective

universes v w

lemma surjective_comp : ∀ {α : Type u} {β : Type v} {γ : Type w} {f : α → β} {g: β → γ},
  surjective f → surjective g → surjective (g ∘ f) :=
    λ (α : Type u) (β : Type v) (γ : Type w) (f:α → β) (g:β → γ),
      λ (Hf: surjective f) (Hg: surjective g),
        λ (z:γ),
          match Hg z with
          | ⟨y, py⟩ :=
            match Hf y with
            | ⟨x , px⟩ := ⟨x, by simp [px,py]⟩
            end
          end
