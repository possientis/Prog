open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; cong)

open import Data.String      using (String; _≟_) -- \?=
open import Data.Nat         using (ℕ; zero; suc)
open import Data.Empty       using (⊥; ⊥-elim)
open import Data.Product     using (_×_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Product     using () renaming (_,_ to ⟨_,_⟩)
open import Data.Sum         using (_⊎_; inj₁; inj₂)
open import Data.Bool        using (Bool; true; false)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Function         using (_∘_)

open import lambda
open import isomorphism

open import Lam.Id
open import Lam.Op
open import Lam.Type
open import Lam.Eval
open import Lam.Value
open import Lam.Typing
open import Lam.Syntax
open import Lam.Closure
open import Lam.Context
open import Lam.Progress
open import Lam.Canonical
open import Lam.Reduction
open import Lam.Preservation

V¬—→ : ∀ {M N : Term}
  → Value M
    ---------------
  → ¬ (M —→ N)

V¬—→ (V-suc p) (ξ-suc q) = V¬—→ p q


—→¬V : ∀ {M N : Term}
  →  M —→ N
    ----------
  →  ¬ Value M

—→¬V p q = V¬—→ q p

-- a value which is well-typed in the empty context is canonical
canonical : ∀ {V : Term} {A : Type}
  → ∅ ⊢ V ∶ A
  → Value V
    ---------------
  → Canonical V ∶ A

canonical (⊢ƛ p) V-ƛ = C-ƛ p
canonical ⊢zero V-zero = C-zero
canonical (⊢suc p) (V-suc q) = C-suc (canonical p q)
canonical ⊢Num V-Num = C-Num
canonical ⊢Bool V-Bool = C-Bool

-- a canonical term is a value and is well-typed in the empty context
value : ∀ {M : Term} {A : Type}
  → Canonical M ∶ A
    --------------
  → Value M

value (C-ƛ x) = V-ƛ
value C-zero = V-zero
value (C-suc p) = V-suc (value p)
value C-Num = V-Num
value C-Bool = V-Bool


typed : ∀ {M : Term} {A : Type}
  → Canonical M ∶ A
    --------------------
  → ∅ ⊢ M ∶ A

typed (C-ƛ p) = ⊢ƛ p
typed C-zero = ⊢zero
typed (C-suc p) = ⊢suc (typed p)
typed C-Num = ⊢Num
typed C-Bool = ⊢Bool


progress-≃ : ∀ {M : Term} → Progress M ≃ Value M ⊎ ∃[ N ](M —→ N)
progress-≃ =  record
  { to = to
  ; from = from
  ; from∘to = from∘to
  ; to∘from = to∘from
  }
  where
    to : ∀ {M : Term} → Progress M → Value M ⊎ ∃[ N ](M —→ N)
    to (step p) = inj₂ ⟨ _ , p ⟩
    to (done p) = inj₁ p

    from : ∀ {M : Term} → Value M ⊎ ∃[ N ](M —→ N) → Progress M
    from (inj₁ p) = done p
    from (inj₂ ⟨ N , p ⟩) = step p

    from∘to : ∀ {M : Term} → ∀ (p : Progress M) → from (to p) ≡ p
    from∘to (step p) = refl
    from∘to (done p) = refl

    to∘from : ∀ {M : Term} → ∀ (p : Value M ⊎ ∃[ N ](M —→ N)) → to (from p) ≡ p
    to∘from (inj₁ p) = refl
    to∘from (inj₂ ⟨ N , p ⟩) = refl

progress' : ∀ {M : Term} {A : Type} → ∅ ⊢ M ∶ A → Value M ⊎ ∃[ N ](M —→ N)
progress' (⊢ƛ p) = inj₁ V-ƛ
progress' (⊢· p q) with progress' p
progress' (⊢· p q) | inj₂ ⟨ N , r ⟩ = inj₂ ⟨  N · _ , ξ-·₁ r ⟩
... | inj₁ r with progress' q
... | inj₂ ⟨ N , s ⟩ = inj₂ ⟨ _ · N , ξ-·₂ r s ⟩
progress' (⊢· p q) | inj₁ V-ƛ | inj₁ s = inj₂ ⟨ _ , β-ƛ s ⟩
progress' ⊢zero = inj₁ V-zero
progress' (⊢suc p) with progress' p
... | inj₂ ⟨ N , q ⟩ = inj₂ ⟨ _ , ξ-suc q ⟩
... | inj₁ q = inj₁ (V-suc q)
progress' (⊢case p q r) with progress' p
... | inj₂ ⟨ N , s ⟩ = inj₂ ⟨ _ , ξ-case s ⟩
... | inj₁ V-zero = inj₂ ⟨ _ , β-zero ⟩
... | inj₁ (V-suc s) = inj₂ ⟨ _ , β-suc s ⟩
progress' (⊢if p q r) with progress' p
... | inj₂ ⟨ N , s ⟩ = inj₂ ⟨ _ , ξ-if₀ s ⟩
progress' (⊢if p q r) | inj₁ (V-Bool {false}) = inj₂ ⟨ _ , β-if₂ ⟩
progress' (⊢if p q r) | inj₁ (V-Bool {true}) = inj₂ ⟨ _ , β-if₁ ⟩
progress' (⊢μ p) = inj₂ ⟨ _ , β-μ ⟩
progress' ⊢Num = inj₁ V-Num
progress' (⊢+ p q) with progress' p
... | inj₂ ⟨ N , r ⟩ = inj₂ ⟨ _ , ξ-op₁ r ⟩
... | inj₁ r with progress' q
... | inj₂ ⟨ N , s ⟩ = inj₂ ⟨ _ , ξ-op₂ r s ⟩
progress' (⊢+ p q) | inj₁ V-Num | inj₁ V-Num = inj₂ ⟨ _ , β-+ ⟩
progress' (⊢* p q) with progress' p
... | inj₂ ⟨ N , r ⟩ = inj₂ ⟨ _ , ξ-op₁ r ⟩
... | inj₁ r with progress' q
... | inj₂ ⟨ N , s ⟩ = inj₂  ⟨ _ , ξ-op₂ r s ⟩
progress' (⊢* p q) | inj₁ V-Num | inj₁ V-Num = inj₂ ⟨ _ , β-* ⟩
progress' ⊢Bool = inj₁ V-Bool
progress' (⊢= p q) with progress' p
... | inj₂ ⟨ N , r ⟩ = inj₂ ⟨ _ , ξ-op₁ r ⟩
... | inj₁ r with progress' q
... | inj₂ ⟨ N , s ⟩ = inj₂ ⟨ _ , ξ-op₂ r s ⟩
progress' (⊢= p q) | inj₁ V-Num | inj₁ V-Num = inj₂ ⟨ _ , β-= ⟩
progress' (⊢< p q) with progress' p
... | inj₂ ⟨ N , r ⟩ = inj₂ ⟨ _ , ξ-op₁ r ⟩
... | inj₁ r with progress' q
... | inj₂ ⟨ N , s ⟩ = inj₂ ⟨ _ , ξ-op₂ r s ⟩
progress' (⊢< p q) | inj₁ V-Num | inj₁ V-Num = inj₂ ⟨ _ , β-< ⟩
progress' (⊢∧ p q) with progress' p
... | inj₂ ⟨ N , r ⟩ = inj₂ ⟨ _ , ξ-op₁ r ⟩
... | inj₁ r with progress' q
... | inj₂ ⟨ N , s ⟩ = inj₂ ⟨ _ , ξ-op₂ r s ⟩
progress' (⊢∧ p q) | inj₁ V-Bool | inj₁ V-Bool = inj₂ ⟨ _ , β-∧ ⟩
progress' (⊢∨ p q) with progress' p
... | inj₂ ⟨ N , r ⟩ = inj₂ ⟨ _ , ξ-op₁ r ⟩
... | inj₁ r with progress' q
... | inj₂ ⟨ N , s ⟩ = inj₂ ⟨ _ , ξ-op₂ r s ⟩
progress' (⊢∨ p q) | inj₁ V-Bool | inj₁ V-Bool = inj₂ ⟨ _ , β-∨ ⟩

value? : ∀ {M : Term} {A : Type} → ∅ ⊢ M ∶ A → Dec (Value M)
value? p with progress p
... | step q = no (—→¬V q)
... | done q = yes q

sucμ : Term
sucμ = μ "x" ⇒ `suc ` "x"

_ =
  begin
    sucμ
    —→⟨ β-μ ⟩
    `suc sucμ
    —→⟨ ξ-suc β-μ ⟩
    `suc `suc sucμ
    —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc `suc `suc sucμ
    -- ...
    ∎

⊢sucμ : ∅ ⊢ sucμ ∶ `ℕ
⊢sucμ = ⊢μ (⊢suc (⊢` Z))

res : Steps sucμ
res = eval (gas 1) ⊢sucμ

_ : eval (gas 3) ⊢sucμ ≡ steps
  (sucμ
    —→⟨ β-μ ⟩
    `suc sucμ
    —→⟨ ξ-suc β-μ ⟩
    `suc `suc sucμ
    —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc `suc `suc sucμ
    ∎)
  out-of-gas

_ = refl

twoᶜ-sucᶜ-zero : ∅ ⊢ twoᶜ · sucᶜ · `zero ∶ `ℕ
twoᶜ-sucᶜ-zero = ⊢· (⊢· ⊢twoᶜ ⊢sucᶜ) ⊢zero

_ : Steps (twoᶜ · sucᶜ · `zero)
_ = eval (gas 100) twoᶜ-sucᶜ-zero

_ : eval (gas 100) twoᶜ-sucᶜ-zero ≡ steps
  ( twoᶜ · sucᶜ · `zero
    —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    _
    —→⟨ β-ƛ V-zero ⟩
    _
    —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    _
    —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc `suc `zero ∎)
  (done (V-suc (V-suc V-zero)))

_ = refl

_ : Steps (plus · two · two)
_ = eval (gas 100) ⊢2+2

_ : eval (gas 100) ⊢2+2 ≡ steps
    (plus · two · two
    —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    _
    —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    _
    —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    _
    —→⟨ β-suc (V-suc V-zero) ⟩
    _
    —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    _
    —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero)) ) ⟩
    _
    —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    _
    —→⟨ ξ-suc (β-suc V-zero) ⟩
    _
    —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    _
    —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    _
    —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    _
    —→⟨ ξ-suc (ξ-suc β-zero) ⟩
    `suc (`suc (`suc (`suc `zero)))
    ∎)

    (done (V-suc (V-suc (V-suc (V-suc V-zero)))))

_ = refl


_ : Steps (plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero)
_ = eval (gas 100) ⊢2+2ᶜ

_ : eval (gas 100) ⊢2+2ᶜ ≡ steps

  (plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
    —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    _
    —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    _
    —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    _
    —→⟨ β-ƛ V-zero ⟩
    _
    —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    _
    —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    _
    —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    _
    —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    _
    —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    _
    —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    _
    —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    _
    —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
    `suc `suc `suc `suc `zero
    ∎)

  (done (V-suc (V-suc (V-suc (V-suc V-zero)))))

_ = refl

⊢2*2 : ∀ {Γ : Context} → Γ ⊢ mul · two · two ∶ `ℕ
⊢2*2 = ⊢· (⊢· (⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` (S' Z)) ⊢zero
  (⊢· (⊢· ⊢plus (⊢` (S' Z)))
  (⊢· (⊢· (⊢` (S' (S' (S' Z)))) (⊢` Z)) (⊢` (S' Z))))))))
  (⊢suc (⊢suc ⊢zero))) (⊢suc (⊢suc ⊢zero))

_ : Steps (mul · two · two)
_ = eval (gas 100) ⊢2*2

_ : eval (gas 100) ⊢2*2 ≡ steps
  (mul · two · two
    —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    _
    —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    _
    —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    _
    —→⟨ β-suc (V-suc V-zero) ⟩
    _
    —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    _
    —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    _
    —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    _
    —→⟨ {!!} ⟩
    {!!})

  {!!}

_ = {!!}


