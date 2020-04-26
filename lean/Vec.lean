universe u

open nat

inductive Vec (α : Type u) : ℕ → Type u
| nil {} : Vec 0
| cons {n : ℕ} (x : α) (xs : Vec n) : Vec (succ n)


inductive eq' (α : Sort u) (a : α) : α → Prop
| refl : eq' a

--#check @eq.rec_on
--#check @eq.rec

lemma L1 : ∀ (α : Type u) (a b : α) (p : α → Prop), a = b → p a → p b :=
  λ α a b p E H, eq.rec_on E H

--#check L1

definition subst {α : Type u} {a b : α} (p : α → Prop)(E : a = b) (H:p a) : p b :=
  eq.rec_on E H

--#check @subst
--#check@eq.refl

definition P {α : Type u} (a : α) (x : α) : Prop := x = a

definition symm2 {α : Type u} {a b : α} (E:a = b) : b = a :=
@subst α a b (λ (x:α), x = a) E (eq.refl a)

definition trans2 {α : Type u} (a b c : α) (Eab : a = b) (Ebc : b = c) : a = c :=
  @subst α b c (λ x, a = x) Ebc Eab

definition congr2 {α β : Type u} {a b : α} (f : α → β) (E : a = b) : f a = f b :=
  @subst α a b (λ x, f a = f x) E (eq.refl (f a))

open Vec

local notation x :: xs := cons x xs

--#check @Vec.cases_on

def tail_aux {α : Type u} {n m : ℕ} (v : Vec α m) :
  m = n + 1 → Vec α n :=
    Vec.cases_on v
      (begin assume H, cases H end)
      (begin assume m x w H, cases H, exact w end)

def tail1 {α : Type u} {n : ℕ} (v : Vec α (n+1)) : Vec α n := tail_aux v rfl

--#check @nat.no_confusion

def head {α : Type u} : ∀ {n : ℕ}, Vec α (n + 1) → α
| _ (x :: xs) := x

def tail {α : Type u} : ∀ {n : ℕ}, Vec α (n + 1) → Vec α n
| _ (x :: xs) := xs


lemma eta : ∀ {α : Type u} {n : ℕ} (vs : Vec α (n + 1)), head vs :: tail vs = vs :=
begin
  intros α n vs, cases vs with v vs,
  reflexivity
end

def map2 {α β γ : Type u} (f : α → β → γ) : ∀ {n : ℕ}, Vec α n → Vec β n → Vec γ n
| 0 nil nil := nil
| (n + 1) (a :: as) (b :: bs) := f a b :: map2 as bs


def zip {α β : Type u} : ∀ {n : ℕ}, Vec α n → Vec β n → Vec (α × β) n
| 0 nil nil := nil
| (n + 1) (a :: as) (b :: bs) := (a, b) :: zip as bs

--#print map2
--#print map2._main -- scary stuff


def map {α β : Type u} (f : α → β) : ∀ {n : ℕ}, Vec α n → Vec β n
| 0 nil := nil
| (n + 1) (x :: xs) := f x :: map xs

--#print map
--#print map._main
--#check @map._main

/- How do we do this?
def map1 : ∀ {α β : Type u}, (α → β) → ∀ {n : ℕ}, Vec α n → Vec β n :=
  λ (α β:Type u) (f:α → β), nat.rec
    (λ (_:Vec α 0), _)
    _
-/
--#check @nat.rec
--#check @nat.rec_on
--#check @nat.brec_on




