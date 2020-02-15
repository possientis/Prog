open nat

def sub1 : ℕ → ℕ
| zero     := zero
| (succ x) := x


def is_zero : ℕ → Prop
| zero     := true
| (succ x) := false


example : sub1 0 = 0 := rfl
example (n : ℕ) : sub1 (succ n) = n := rfl

example : is_zero 0 = true := rfl
example (n : ℕ) : is_zero (succ n) = false := rfl


example : sub1 7 = 6 := rfl
example (n : ℕ) : ¬ is_zero (n + 3) := begin  simp [is_zero]end

def sub1' : ℕ → ℕ
| 0 := 0
| (n+1) := n

universes u v
variables {α : Type u} {β : Type v}

def swap : α × β → β × α
| (x,y) := (y,x)

def foo : ℕ × ℕ → ℕ
| (m,n) := m + n

def bar : option ℕ → ℕ
| (some n) := n + 1
| none     := 0



