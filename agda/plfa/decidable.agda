module decidable where

import Relation.Binary.PropositionalEquality.Core as Eq

open        Eq                        using (_≡_; refl; sym; cong)
open import Data.Nat                  using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Sum                  using (_⊎_; inj₁; inj₂)
open import Data.Unit                 using (⊤; tt)
open import Data.Empty                using (⊥; ⊥-elim)
open import Data.Product              using (_×_; proj₁; proj₂; _,_)
open        Eq.≡-Reasoning            using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Relation.Nullary          using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import relations                 using (_<_; z<s; s<s)
open import isomorphism               using (_⇔_)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))

data Bool : Set where
  true  : Bool
  false : Bool

infix 4 _≤b_

_≤b_ : ℕ → ℕ → Bool
zero ≤b n = true
suc m ≤b zero = false
suc m ≤b suc n = m ≤b n

_ : (2 ≤b 4) ≡ true
_ =
  begin
    2 ≤b 4
    ≡⟨⟩
    1 ≤b 3
    ≡⟨⟩
    0 ≤b 2
    ≡⟨⟩
    true
    ∎

_ : (4 ≤b 2) ≡ false
_ =
  begin
    4 ≤b 2
    ≡⟨⟩
    3 ≤b 1
    ≡⟨⟩
    2 ≤b 0
    ≡⟨⟩
    false
    ∎

T : Bool -> Set
T true  = ⊤
T false = ⊥


T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt = refl

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl = tt

≤b→≤ : ∀ (m n : ℕ) → T (m ≤b n) → m ≤ n
≤b→≤ zero n _ = z≤n
≤b→≤ (suc m) (suc n) p = s≤s (≤b→≤ m n p)

≤→≤b : ∀ {m n : ℕ} → m ≤ n → T (m ≤b n)
≤→≤b z≤n = tt
≤→≤b (s≤s m≤n) = ≤→≤b m≤n

data Dec (a : Set) : Set where
  yes : a   → Dec a
  no  : ¬ a → Dec a

¬s≤z : ∀ {n : ℕ} → ¬ (suc n ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s f (s≤s m≤n) = f m≤n

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤? n  = yes z≤n
suc m ≤? zero = no ¬s≤z
suc m ≤? suc n with m ≤? n
(suc m ≤? suc n) | yes m≤n = yes (s≤s m≤n)
(suc m ≤? suc n) | no ¬m≤n = no (¬s≤s ¬m≤n)

_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_ = refl

¬n<z : ∀ {n : ℕ} → ¬ (n < zero)
¬n<z ()

¬s<s : ∀ {m n : ℕ} → ¬ m < n → ¬ (suc m) < (suc n)
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
m <? zero  = no ¬n<z
zero <? suc n = yes z<s
suc m <? suc n with m <? n
(suc m <? suc n) | yes m<n = yes (s<s m<n)
(suc m <? suc n) | no ¬m<n = no (¬s<s ¬m<n)

¬z≡s : ∀ {n : ℕ} → ¬ zero ≡ suc n
¬z≡s ()

¬s≡s : ∀ {m n : ℕ} → ¬ m ≡ n → ¬ (suc m) ≡ (suc n)
¬s≡s ¬m≡n refl = ¬m≡n refl

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc n = no ¬z≡s
suc m ≡ℕ? zero = no (λ{s≡z → ¬z≡s (sym s≡z)})
suc m ≡ℕ? suc n with m ≡ℕ? n
(suc m ≡ℕ? suc n) | yes m≡n = yes (cong suc m≡n)
(suc m ≡ℕ? suc n) | no ¬m≡n = no (¬s≡s ¬m≡n)


_≤?'_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?' n with m ≤b n | ≤b→≤ m n | ≤→≤b {m} {n}
(m ≤?' n) | true  | q | _ = yes (q tt)
(m ≤?' n) | false | _ | r = no r

-- erasure: discards the proof
⌞_⌟ : ∀ {a : Set} → Dec a → Bool
⌞ yes _ ⌟ = true
⌞ no _ ⌟ = false


_≤b'_ : ∀ (m n : ℕ) → Bool
m ≤b' n = ⌞ m ≤? n ⌟

L0 : ∀ {b : Bool} → ¬ b ≡ true → b ≡ false
L0 {true} ¬btrue = contradiction refl ¬btrue
L0 {false} ¬btrue = refl

-- proving correctness of _≤b'_ not that simple
L1 : ∀ (m n : ℕ) → (m ≤b n) ≡ (m ≤b' n)
L1 zero n = refl
L1 (suc m) zero = refl
L1 (suc m) (suc n) with m ≤? n | ≤→≤b | ≤b→≤
L1 (suc m) (suc n) | yes x | q | _ = T→≡ (m ≤b n) (q x)
L1 (suc m) (suc n) | no x  | _ | q = L0 (λ{p → x (q m n (≡→T p))})

toWitness : ∀ {a : Set} {d : Dec a} → T ⌞ d ⌟ → a
toWitness {a} {yes p} _ = p

fromWitness : ∀ {a : Set} {d : Dec a} → a → T ⌞ d ⌟
fromWitness {a} {yes _} x = tt
fromWitness {a} {no ¬p} p = ¬p p

≤b'→≤ : ∀ {m n : ℕ} → T (m ≤b' n) → m ≤ n
≤b'→≤ = toWitness

≤→≤b' : ∀ {m n : ℕ} → m ≤ n → T (m ≤b' n)
≤→≤b' = fromWitness

infixr 6 _∧_

_∧_ : Bool -> Bool -> Bool
true ∧ y  = y
false ∧ y = false

infix 6 _⊗_

_⊗_ : ∀ {a b : Set} → Dec a → Dec b → Dec (a × b)
yes pa ⊗ yes pb = yes (pa , pb)
yes _ ⊗ no p¬b = no (λ{(_ , pb) → p¬b pb})
no p¬a ⊗ _ = no λ{(pa , _) → p¬a pa}


infixr 5 _∨_

_∨_ : Bool → Bool → Bool
false ∨ y = y
true ∨ y = true

infix 5 _⊕_

_⊕_ : ∀ {a b : Set} → Dec a → Dec b → Dec (a ⊎ b)
yes pa ⊕ _ = yes (inj₁ pa)
no _ ⊕ yes pb = yes (inj₂ pb)
no p¬a ⊕ no p¬b = no λ{(inj₁ pa) → p¬a pa; (inj₂ pb) → p¬b pb}

not : Bool → Bool
not true = false
not false = true

¬? : ∀ {a : Set} → Dec a → Dec (¬ a)
¬? (yes pa) = no (λ{p¬a → p¬a pa})
¬? (no p¬a) = yes p¬a

{-
-- actually can't do this
¬?-rev : ∀ {a : Set} → Dec (¬ a) → Dec a
¬?-rev (yes p¬a) = no p¬a
¬?-rev (no p¬¬a) = yes {!!}
-}

_⊃_ : Bool → Bool → Bool
true  ⊃ true  = true
true  ⊃ false = false
false ⊃ _     = true

_⊃?_ : ∀ {a b : Set} → Dec a → Dec b → Dec (a → b)
yes _ ⊃? yes pb = yes λ{_ → pb}
yes pa ⊃? no p¬b = no (λ{f → p¬b (f pa)})
no p¬a ⊃? _ = yes λ{pa → ⊥-elim (p¬a pa)}

∧-⊗ : ∀ {a b : Set} (x : Dec a) (y : Dec b) → ⌞ x ⌟ ∧ ⌞ y ⌟ ≡ ⌞ x ⊗ y ⌟
∧-⊗ (yes _) (yes _) = refl
∧-⊗ (yes _) (no _) = refl
∧-⊗ (no _) _ = refl

∨-⊕ : ∀ {a b : Set} (x : Dec a) (y : Dec b) → ⌞ x ⌟ ∨ ⌞ y ⌟ ≡ ⌞ x ⊕ y ⌟
∨-⊕ (yes _) _ = refl
∨-⊕ (no _) (yes _) = refl
∨-⊕ (no _) (no _) = refl

not-¬? : ∀ {a : Set} (x : Dec a) → not (⌞ x ⌟) ≡ ⌞ ¬? x ⌟
not-¬? (yes _) = refl
not-¬? (no _) = refl

⊃-⊃? : ∀ {a b : Set} (x : Dec a) (y : Dec b) → ⌞ x ⌟ ⊃ ⌞ y ⌟ ≡ ⌞ x ⊃? y ⌟
⊃-⊃? (yes _) (yes _) = refl
⊃-⊃? (yes _) (no _) = refl
⊃-⊃? (no _) _ = refl

_iff_ : Bool → Bool → Bool
true iff true = true
true iff false = false
false iff true = false
false iff false = true

open _⇔_

_iff?_ : ∀ {a b : Set} (x : Dec a) (y : Dec b) → Dec (a ⇔ b)
yes pa iff? yes pb = yes record { to = λ{_ → pb}; from = λ{_ → pa}}
yes pa iff? no p¬b = no (λ{i → p¬b (to i pa)})
no p¬a iff? yes pb = no (λ{i → p¬a (from i pb)})
no p¬a iff? no p¬b = yes record
  { to = λ{pa → ⊥-elim (p¬a pa)}
  ; from = λ{pb → ⊥-elim (p¬b pb)}
  }



