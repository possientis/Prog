structure Point (α : Type) :=
mk :: (x : α) (y : α)

#check Point
#check @Point.rec_on
#check @Point.x
#check @Point.y

#print prefix Point

#reduce Point.x (Point.mk 10 20)
#reduce Point.y (Point.mk 10 20)

open Point

example (α : Type) (a b : α) : x (mk a b) = a := rfl
example (α : Type) (a b : α) : x {x := a, y := b} = a := rfl

example (α : Type) (a b : α) : y (mk a b) = b := rfl
example (α : Type) (a b : α) : y {x := a, y := b} = b := rfl

def p : Point ℕ := {x := 10, y := 20} -- mk 10 20

#check p.x
#reduce p.x
#reduce p.y


structure Prod (α : Type) (β : Type) : Type := (pr₁ : α) (pr₂ : β)

#check @Prod.mk

namespace Point

def add (p q : Point ℕ) : Point ℕ := {x := p.x + q.x, y := p.y + q.y}

end Point

#check Point.add


def q : Point ℕ := { x := 15, y := 20}

#reduce p.add q

open Point

#reduce add p q

def Point.smul (n : ℕ) (p : Point ℕ) : Point ℕ := {x := n * p.x, y := n * p.y}

#reduce p.smul 3

#check @list.map

def xs : list ℕ := [1, 2, 3]
def f  : ℕ → ℕ := λ n, n * n

#reduce xs.map f
#reduce list.map f xs
#eval xs.map f
#eval list.map f xs


--3 ways of making things polymorphic over universe level
universe u
structure Point1 (α : Type u) : Type u :=
mk :: (x : α) (y : α)

structure {v} Point2 (α : Type v) :=
mk :: (x : α) (y : α)

structure Point3 (α : Type _) :=
mk :: (x : α) (y : α)

#check @Point1
#check @Point2
#check @Point3

-- max 1 u : result can never be a Prop = Type 0 (I thought Type 0 = Sort 1 and Prop = Sort 0)
structure {v} Prod1 (α : Type v) (β : Type v) : Type (max 1 v) :=
mk :: (pr1 : α) (pr2 : β)

set_option pp.universes true -- forces Lean to display universes
#check @Prod1.mk


-- using anonymous constructor
structure {v} Prod2 (α : Type v) (β : Type v) : Type (max 1 v) :=
  (pr1 : α) (pr2 : β)

example : Prod2 ℕ ℕ := ⟨1,2⟩

#check (⟨1,2⟩ : Prod2 ℕ ℕ)
















