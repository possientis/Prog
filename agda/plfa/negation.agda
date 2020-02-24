open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import isomorphism using (_≃_; extensionality)

¬_ : Set → Set
¬ x = x → ⊥


¬-elim : ∀ {a : Set}
  → ¬ a
  →   a
    -----
  →   ⊥

¬-elim ¬x x = ¬x x

infix 3 ¬_ -- binds more tightly than ⊎ and ×, but less than everything else

¬¬-intro : ∀ {a : Set}
  →   a
    -----
  →  ¬ ¬ a

¬¬-intro x = λ{¬x → ¬x x}

¬¬-intro' : ∀ {a : Set}
  →   a
    -----
  →  ¬ ¬ a

¬¬-intro' x ¬x = ¬x x

¬¬¬-elim : ∀ {a : Set}
  →   ¬ ¬ ¬ a
     ---------
  →    ¬ a

¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬¬-intro x)

contraposition : ∀ {a b : Set}
  →     (a → b)
     -------------
  →   (¬ b → ¬ a)

contraposition a→b ¬b x = ¬b (a→b x)

_≢_ : ∀ {a : Set} → a → a → Set
x ≢ y = ¬ x ≡ y

ex1 : 1 ≢ 2
ex1 ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ ()

id : ⊥ → ⊥
id x = x

id' : ⊥ → ⊥
id' ()

id≡id' : id ≡ id'
id≡id' = extensionality (λ ())

-- Two proofs of a negation are equal
assimilation : ∀ {a : Set} (¬x ¬x' : ¬ a) → ¬x ≡ ¬x'
assimilation ¬x ¬x' = extensionality λ{x → ⊥-elim (¬x x)}

irreflexivity : ∀ (n : ℕ) → ¬(n < n)
irreflexivity (suc n) (s≤s p) = irreflexivity n p

<-not-≡ : ∀ {m n : ℕ} → m < n → ¬(m ≡ n)
<-not-≡ (s≤s p) refl = <-not-≡ p refl

<-not-> : ∀ {m n : ℕ} → m < n → ¬(n < m)
<-not-> (s≤s p) (s≤s q) = <-not-> p q

≡-not-< : ∀ {m n : ℕ} → m ≡ n → ¬(m < n)
≡-not-< refl (s≤s p) = ≡-not-< refl p

≡-not-> : ∀ {m n : ℕ} → m ≡ n → ¬(n < m)
≡-not-> refl (s≤s q) = ≡-not-> refl q

>-not-≡ : ∀ {m n : ℕ} → n < m → ¬(m ≡ n)
>-not-≡ (s≤s p) refl = >-not-≡ p refl

>-not-< : ∀ {m n : ℕ} → n < m → ¬(m < n)
>-not-< n<m = <-not-> n<m

data Trichotomy (m n : ℕ) : Set where
  Less  : m < n → Trichotomy m n
  Equal : m ≡ n → Trichotomy m n
  More  : n < m → Trichotomy m n


data Trichotomy' (m n : ℕ) : Set where
  Less'  : m < n    → ¬(m ≡ n) → ¬(n < m) → Trichotomy' m n
  Equal' : ¬(m < n) → m ≡ n    → ¬(n < m) → Trichotomy' m n
  More'  : ¬(m < n) → ¬(m ≡ n) → n < m    → Trichotomy' m n

toTrichotomy' : ∀ {m n : ℕ} → Trichotomy m n → Trichotomy' m n
toTrichotomy' (Less  m<n) = Less' m<n (<-not-≡ m<n) (<-not-> m<n)
toTrichotomy' (Equal m≡n) = Equal' (≡-not-< m≡n) m≡n (≡-not-> m≡n)
toTrichotomy' (More  n<m) = More' (>-not-< n<m) (>-not-≡ n<m) n<m

fromTrichotomy' : ∀ {m n : ℕ} → Trichotomy' m n → Trichotomy m n
fromTrichotomy' (Less'  m<n _ _) = Less m<n
fromTrichotomy' (Equal' _ m≡n _) = Equal m≡n
fromTrichotomy' (More'  _ _ n<m) = More n<m

isoTrichotomy : ∀ {m n : ℕ} → Trichotomy m n ≃ Trichotomy' m n
isoTrichotomy = record
  { to = toTrichotomy'
  ; from = fromTrichotomy'
  ; from∘to = λ{(Less n<m) → refl; (Equal m≡n) → refl; (More n<m) → refl}
  ; to∘from = {!!}   -- actually not true, unless proof irrelevance
  }
