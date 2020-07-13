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

instance Semigroup_has_mul (S : Semigroup) : has_mul (S.carrier) := ⟨S.mul⟩

--#check Semigroup.carrier

instance Semigroup_to_sort : has_coe_to_sort Semigroup := {S := _, coe := λ S, S.carrier}

example (S : Semigroup) (a b c : S) : (a * b) * c = a * (b * c) := Semigroup.mul_assoc _ a b c

structure morphism (S1 S2: Semigroup) :=
(mor : S1 → S2)
(resp_mul: ∀ a b : S1, mor (a * b) = mor a * mor b)

--#check @morphism.mor

instance morphism_to_fun (S1 S2 : Semigroup) : has_coe_to_fun (morphism S1 S2) :=
  {F := λ _, S1 → S2, coe := λ m, m.mor}

lemma resp_mul {S1 S2 : Semigroup} (f : morphism S1 S2) (a b : S1) :
  f (a * b) = f a * f b := f.resp_mul a b

lemma L1 (S1 S2 : Semigroup) (f : morphism S1 S2) (a : S1) :
  f (a * a * a) = f a * f a * f a := calc
    f (a * a * a) = f (a * a) * f a : by rw resp_mul
      ...         = f a * f a * f a : by rw resp_mul

--#check @L1
--set_option pp.coercions false
--#check @L1
