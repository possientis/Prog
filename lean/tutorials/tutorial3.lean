import data.real.basic
import algebra.group.pi


def even_fun (f : ℝ → ℝ) := ∀ x, f(-x) = f x

def odd_fun (f : ℝ → ℝ) := ∀ x, f (-x) = - f x

example : ∀ (f g : ℝ → ℝ), even_fun f → even_fun g → even_fun (f + g) :=
begin
  intros f g Hf Hg x, calc
    (f + g)(-x) = f (-x) + g (-x) : by refl
    ...         = f (x) + g(x)    : by rw [Hf,Hg]
    ...         = (f + g)(x)      : by refl
end

example : ∀ (f g : ℝ → ℝ), even_fun f → even_fun (g ∘ f) :=
begin
  intros f g H₁ x, calc
    (g ∘ f) (-x) = g (f (-x))   : by refl
    ...          = g (f (x))    : by rw H₁
    ...          = (g ∘ f)(x)   : by refl
end

example : ∀ (f g : ℝ → ℝ), odd_fun f → odd_fun g → odd_fun (g ∘ f) :=
begin
  intros f g Hf Hg x, calc
    (g ∘ f) (-x) = g (f (-x))   : by refl
    ...          = g (- (f x))  : by rw Hf
    ...          = - (g (f x))  : by rw Hg
    ...          = - ((g ∘ f) x): by refl
end


def non_decreasing (f : ℝ → ℝ) := ∀ x y, x ≤ y → f x ≤ f y

def non_increasing (f : ℝ → ℝ) := ∀ x y, x ≤ y → f y ≤ f x

example : ∀ (f g : ℝ → ℝ),
  non_decreasing f →
  non_decreasing g →
  non_decreasing (g ∘ f) :=
begin
  intros f g Hf Hg x y H₁, calc
    (g ∘ f) (x) = g (f x)     : by refl
    ...         ≤ g (f y)     : by { apply Hg, apply Hf, assumption }
    ...         = (g ∘ f) (y) : by refl
end


example : ∀ (f g : ℝ → ℝ),
  non_decreasing f →
  non_increasing g →
  non_increasing (g ∘ f) :=
begin
  intros f g Hf Hg x y H₁, calc
    (g ∘ f) (y) = g (f y)       : by refl
    ...         ≤ g (f x)       : by { apply Hg, apply Hf, assumption }
    ...         = (g ∘ f) (x)   : by refl
end

example : ∀ (a b : ℝ), a = a*b → a = 0 ∨ b = 1 :=
begin
  intros a b H₁,
  have H₂ : a*(b - 1) = 0,
    { calc
      a*(b - 1) = a*b - a : by ring
      ...       = a - a   : by rw ← H₁
      ...       = 0       : by ring },
  rw mul_eq_zero at H₂, cases H₂ with H₂ H₂,
    { left, assumption },
    { right, linarith }
end

example : ∀ (x y : ℝ), x^2 = y^2 → x = y ∨ x = -y :=
begin
  intros x y H₁,
  have H₂ : (x - y)*(x + y) = 0, { calc
    (x - y)*(x + y) = x^2 - y^2  : by ring
    ...             = 0          : by linarith },
  rw mul_eq_zero at H₂, cases H₂ with H₂ H₂,
    {left, linarith },
    {right, linarith }
end

example : ∀ (f : ℝ → ℝ), non_decreasing f ↔ ∀ x y, x < y → f x ≤ f y :=
begin
  intros f, split; intros H₁,
    { intros x y H₂, apply H₁, linarith },
    { intros x y H₂, have H₃ : x = y ∨ x < y, {apply eq_or_lt_of_le, assumption },
      cases H₃ with H₃ H₃,
        { rw H₃ },
        { apply H₁, assumption }}
end

example : ∀ (f : ℝ → ℝ), non_decreasing f → (∀ x, f (f x) = x) → ∀ x, f x = x :=
begin
  intros f H₁ H₂ x, have H₃ : f x ≤ x ∨ x ≤ f x, { apply le_total },
  cases H₃ with H₃ H₃,
    { apply le_antisymm; try { assumption }, have H₄ : f (f x) ≤ f x,
      { apply H₁, assumption},  rw H₂ at H₄, assumption },
    { apply le_antisymm; try { assumption }, have H₄ : f x ≤ f (f x),
      {apply H₁, assumption }, rw H₂ at H₄, assumption }
end
