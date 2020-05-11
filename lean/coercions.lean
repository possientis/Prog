variables m n : ℕ
variables i j : ℤ
universe u

universe v

--#check i + j
--#check i + m + j
--#check i + m + n

-- ↑ is \u 

--#check ↑m + i
--#check coe m + i

instance bool_to_Prop : has_coe bool Prop := ⟨λ b, b = tt⟩

--#reduce if tt then 3 else 5
--#reduce if ff then 3 else 5

open list

def toSet {α : Type u} : list α → set α
| [] := ∅
| (x :: xs) := toSet xs

instance toSetCoe (α : Type u) : has_coe (list α) (set α) := ⟨toSet⟩

def s₁ : set ℕ  := {1,2}
def l₁ : list ℕ := [3,4]

--#check s₁ ∪ l₁
--#reduce s₁ ∪ l₁

--#check s₁ ∪ [3,4]           -- error
--#check s₁ ∪ [(3:ℕ),4]       -- ok
--#check s₁ ∪ ([3,4]:list ℕ)  -- ok
--#check s₁ ∪ ↑ [3,4]         -- ok

instance coe_subtype2 {α : Type u} {p:α → Prop} : has_coe {x // p x} α :=
  ⟨λ s,subtype.val s⟩

--has_coe_t is the transitive closure if has_coe

namespace hidden
instance lift_list {α : Type u} {β : Type v} [has_lift α β] :
  has_lift (list α) (list β) := ⟨ λ xs, list.map (@coe α β _) xs⟩
  variables xs : list ℕ
  variables ys : list ℤ
--  #check ↑ xs ++ ys
end hidden

structure Semigroup : Type (u+1) :=
  (carrier : Type u)
  (mul : carrier -> carrier -> carrier)
  (mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c))

