import Relation.Binary.PropositionalEquality as Eq
open Eq                         using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning             using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat            using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-suc; +-assoc)
open import Relation.Nullary    using (¬_)
open import Data.Product        using (_×_; proj₁; proj₂; _,_)
open import Data.Sum            using (_⊎_; inj₁; inj₂; [_,_])
open import isomorphism         using (_≃_; ∀-extensionality; extensionality)
open import Function            using (_∘_)
open import bin

∀-elim : ∀ {a : Set} {b : a → Set}
  → (L : ∀ (x : a) → b x)
  → (M : a)
    -------------------
  → b M

∀-elim L M = L M


∀-distrib-×-l : ∀ {a : Set} {p q : a → Set} →
  (∀ (x : a) → p x × q x) ≃ (∀ (x : a) → p x) × (∀ (x : a) → q x)

∀-distrib-×-l =  record
  { to = λ{f → ( (λ{x → proj₁ (f x)}) , (λ{x → proj₂ (f x)}) )}
  ; from = λ{( f , g ) → λ{x → ( f x , g x )}}
  ; from∘to = λ{f → ∀-extensionality (λ{x → refl})}
  ; to∘from = λ{( f , g ) → refl}
  }


⊎∀-implies-∀⊎ : ∀ {a : Set} {p q : a → Set} →
  (∀ (x : a) → p x) ⊎ (∀ (x : a) → q x) → ∀ (x : a) → p x ⊎ q x
⊎∀-implies-∀⊎ (inj₁ px) = inj₁ ∘ px
⊎∀-implies-∀⊎ (inj₂ qx) = inj₂ ∘ qx


data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

iso-Tri-× : ∀ {p : Tri → Set} → (∀ (x : Tri) → p x) ≃ p aa × p bb × p cc
iso-Tri-× = record
  { to = λ{f → ( f aa , ( f bb , f cc ) )}
  ; from = λ{( x , ( y , z ) ) → λ{aa → x ; bb → y; cc → z}}
  ; from∘to = λ{f → ∀-extensionality (λ{aa → refl; bb → refl; cc → refl})}
  ; to∘from = λ{( x , ( y , z ) ) → refl}

  }


data Σ (a : Set) (p : a → Set) : Set where
  _,_ : (x : a) → p x → Σ a p

sig₁ : {a : Set} → {p : a → Set} → Σ a p → a
sig₁ ( x , px ) = x

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax a (λ x → p) = Σ[ x ∈ a ] p

record Σ' (a : Set) (p : a → Set) : Set where
  field
    proj₁' : a
    proj₂' : p proj₁'

∃ : ∀ {a : Set} (p : a → Set) → Set
∃ {a} p = Σ a p

∃-syntax = ∃
syntax ∃-syntax (λ x → p) = ∃[ x ] p

∃-elim : ∀ {a : Set} {p : a → Set} {b : Set}
  → (∀ (x : a) → p x → b)
  → ∃[ x ] p x
    ----------------------
  →      b
∃-elim f ( x , px ) = f x px

∀∃-currying : ∀ {a : Set} {p : a → Set} {b : Set}
  → (∀ (x : a) → (p x → b)) ≃ ((∃[ x ] p x) → b)

∀∃-currying = record
  { to = λ{f → λ{( x , q ) → f x q}}
  ; from = λ{f → λ{x → λ{q → f ( x , q )}}}
  ; from∘to = λ{f → ∀-extensionality (λ{x → extensionality λ{q → refl}})}
  ; to∘from = λ{f → extensionality (λ{( x , q ) → refl})}
  }


∃-distrib-⊎-l : ∀ {a : Set} {p q : a → Set} →
  ∃[ x ] (p x ⊎ q x) ≃ (∃[ x ] p x) ⊎ (∃[ x ] q x)

∃-distrib-⊎-l = record
  { to = λ{(x , (inj₁ px)) → inj₁ (x , px) ; (x , (inj₂ qx)) → inj₂ (x , qx)}
  ; from = λ{(inj₁ ( x , px )) → ( x , inj₁ px ) ; (inj₂ ( x , qx )) → ( x , inj₂ qx )}
  ; from∘to = λ{( x , inj₁ px ) → refl; ( x , inj₂ qx ) → refl}
  ; to∘from = λ{(inj₁ ( x , px )) → refl; (inj₂ ( x , qx )) → refl}
  }

∃×-implies-×∃ : ∀ {a : Set} {p q : a → Set} →
  ∃[ x ] (p x × q x ) → (∃[ x ] p x) × (∃[ x ] q x)
∃×-implies-×∃ ( x , ( px , qx ) ) = ( ( x , px ) , ( x , qx ) )

iso-Tri-⊎ : ∀ {p : Tri → Set} → (∃[ x ] p x) ≃ p aa ⊎ p bb ⊎ p cc
iso-Tri-⊎ = record
  { to      = λ{ (aa , paa) → inj₁ paa
               ; (bb , pbb) → inj₂ (inj₁ pbb)
               ; (cc , pcc) → inj₂ (inj₂ pcc)}
  ; from    = λ{ (inj₁ paa) → (aa , paa)
               ; (inj₂ (inj₁ pbb)) → (bb , pbb)
               ; (inj₂ (inj₂ pcc)) → (cc , pcc)}
  ; from∘to = λ{ (aa , paa) → refl
               ; (bb , pbb) → refl
               ; (cc , pcc) → refl}
  ; to∘from = λ{ (inj₁ paa) → refl
               ; (inj₂ (inj₁ pbb)) → refl
               ; (inj₂ (inj₂ pcc)) → refl}
  }


data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even 0

  even-suc  : ∀ {n : ℕ}
    → odd n
      -----------
    → even (suc n)

data odd where

  odd-suc : ∀ {n : ℕ}
    → even n
      ----------
    → odd (suc n)


even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} → odd n  → ∃[ m ] (1 + m * 2 ≡ n)


even-∃ even-zero = (0 , refl)
even-∃ (even-suc oddn) with odd-∃ oddn
even-∃ (even-suc oddn) | (m , p) = (suc m , cong suc p)

odd-∃ (odd-suc evenn) with even-∃ evenn
odd-∃ (odd-suc evenn) | (m , p) = (m , cong suc p)

-- more difficult
even-∃' : ∀ {n : ℕ} → even n → ∃[ m ] (2 * m     ≡ n)
odd-∃'  : ∀ {n : ℕ} → odd n  → ∃[ m ] (2 * m + 1 ≡ n)

+-identity-r : ∀ {n : ℕ} → n + 0 ≡ n
+-identity-r {zero} = refl
+-identity-r {suc n} = cong suc +-identity-r

even-∃' even-zero =  (0 , refl)
even-∃' (even-suc oddn) with odd-∃' oddn
even-∃' (even-suc {m} oddn) | (n , p) =  (suc n , cong suc (
  begin
    n + suc (n + 0)
    ≡⟨ sym +-identity-r ⟩
    n + suc (n + 0) + 0
    ≡⟨ +-assoc n (suc (n + 0)) 0 ⟩
    n + (suc (n + 0) + 0)
    ≡⟨ sym (cong (n +_) (+-suc (n + 0) 0)) ⟩
    n + ((n + 0) + 1)
    ≡⟨ sym (+-assoc n (n + 0) 1) ⟩
    n + (n + 0) + 1
    ≡⟨ p ⟩
     m
    ∎) )

odd-∃' (odd-suc evenn) with even-∃' evenn
odd-∃' (odd-suc {m} evenn) | (n , p) = (n ,
  (begin
    n + (n + 0) + 1
    ≡⟨ +-suc (n + (n + 0)) 0 ⟩
    suc (n + (n + 0)) + 0
    ≡⟨ cong suc +-identity-r ⟩
    suc (n + (n + 0))
    ≡⟨ cong suc p ⟩
    suc m
    ∎) )

Lemma0 : ∀ {m n : ℕ} → suc n ≡ suc m → n ≡ m
Lemma0 refl = refl

Lemma1 : ∀ {m n : ℕ} → m ≤ n → ∃[ p ] (m + p ≡ n)
Lemma1 z≤n = (_ , refl)
Lemma1 (s≤s m≤n) with Lemma1 m≤n
Lemma1 (s≤s m≤n) | (p , e) = (p , cong suc e)

Lemma2 : ∀ {m n : ℕ} → ∃[ p ] (m + p ≡ n) → m ≤ n
Lemma2 {zero} (p , e) = z≤n
Lemma2 {suc m} {suc n} (p , e) = s≤s (Lemma2 (p , Lemma0 e))

¬∃≃∀¬ : ∀ {a : Set} {p : a → Set} → ¬ ∃[ x ] p x ≃ ∀ x → ¬ p x
¬∃≃∀¬ = record
  { to = λ{f → λ{x → λ{q → f (x , q)}}}
  ; from = λ{f → λ{(x , q) → f x q}}
  ; from∘to = λ{f → extensionality (λ{ (x , q) → refl})}
  ; to∘from = λ{f → refl}
  }

∃¬-implies-¬∀ : ∀ {a : Set} {p : a → Set} → ∃[ x ] (¬ p x) → ¬ ∀ x → p x
∃¬-implies-¬∀ (x , q) = λ{f → q (f x)}

≡One : ∀ {b : Bin} (o o' : One b) → o ≡ o'
≡One justOne justOne = refl
≡One (oneO o) (oneO o') = cong oneO (≡One o o')
≡One (oneI o) (oneI o') = cong oneI (≡One o o')

≡Can : ∀ {b : Bin} (c c' : Can b) → c ≡ c'
≡Can canZero canZero = refl
≡Can canZero (canOne (oneO ()))
≡Can (canOne (oneO ())) canZero
≡Can (canOne justOne) (canOne justOne) = refl
≡Can (canOne (oneO x)) (canOne (oneO y)) = cong canOne (cong oneO (≡One x y))
≡Can (canOne (oneI x)) (canOne (oneI y)) = cong canOne (cong oneI (≡One x y))


Lemma3 : ∀ {p q : ∃[ b ](Can b)} → sig₁ p ≡ sig₁ q → p ≡ q
Lemma3 {(x , px)} {(.x , py)} refl = cong (x ,_) (≡Can px py)


cast : ∀ {b b' : Bin} → b ≡ b' → Can b → Can b'
cast refl cb = cb

ℕ-iso-Can : ℕ ≃ ∃[ b ] (Can b)
ℕ-iso-Can = record
  { to = λ{n → (to n , can-to n)}
  ; from = λ{(b , cb) → from b}
  ; from∘to = λ{n → from-to n}
  ; to∘from = λ{(b , cb) →
    begin
      (to (from b) , can-to (from b))
      ≡⟨ Lemma3 (can-to-from cb) ⟩
      (b , cb)
      ∎}
