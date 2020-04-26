namespace hidden1

universe u

constant list : Type u → Type u

constant cons   : Π α : Type u, α → list α → list α
constant nil    : Π α : Type u, list α
constant head   : Π α : Type u, list α → α
constant tail   : Π α : Type u, list α → list α
constant append : Π α : Type u, list α → list α → list α

end hidden1


open list
open nat

--#check [1,2,3,4,5]



lemma L1 : ∀ (p : ℕ -> Prop), p 0 → (∀ n, p (succ n)) → ∀ n, p n :=
  assume p H0 H1 n,
    begin
      cases n with n,
        apply H0,
        apply H1
    end

--#check L1


lemma L2 : ∀ (n : ℕ), n ≠ 0 → succ (pred n) = n :=
  assume n H,
    begin
      cases n with n,
      { apply (absurd rfl H) },
      { reflexivity }
    end

--#check L2

def f (n : ℕ) : ℕ :=
  begin
    cases n with n,
      {exact 3},
      {exact 7}
  end

--#check f

universe u

def tuple (α : Type u) (n : ℕ) :=
  { l : list α // list.length l = n}

variables {α : Type u} {n : ℕ}

def g {n : ℕ} (t : tuple α n) : ℕ :=
  begin
    cases n, exact 3, exact 7
  end

def my_tuple : tuple ℕ 3 := ⟨ [0,1,2], rfl⟩


example : g my_tuple = 7 := rfl

