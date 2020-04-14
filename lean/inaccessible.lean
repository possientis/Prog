universe u

inductive ImageOf {α β : Type u} (f : α → β) : β → Type u
| Imf : ∀ (x : α), ImageOf (f x)

open ImageOf

def inverse {α β : Type u} {f : α → β} : ∀ (y : β), ImageOf f y → α
| .(f x) (Imf .(f) x) := x

inductive Vec (α : Type u) : ℕ → Type u
| Nil {} : Vec 0
| Cons   : ∀ {n : ℕ}, α → Vec n → Vec (n + 1)

open Vec

namespace Vec
local notation x :: xs := Cons x xs

variable {α : Type u}

def add [has_add α] : ∀ {n : ℕ}, Vec α n → Vec  α n → Vec α n
| 0 Nil Nil := Nil
| (n + 1) (Cons x xs) (Cons y ys) := Cons (x + y) (add xs ys)



end Vec
