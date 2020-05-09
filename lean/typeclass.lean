namespace hidden

class inhabited (α : Type _) :=
  (default : α)

-- syntactic sugar for
@[class] structure inhabited2 (α : Type _) :=
  (default : α)

instance Prop_inhabited : inhabited Prop :=
  inhabited.mk true

instance Prop_inhabited2 : inhabited Prop :=
  { default := true}

instance Prop_inhabited3 : inhabited Prop :=
  ⟨true⟩

instance bool_inhabited : inhabited bool :=
  { default := tt}

instance nat_inhabited : inhabited ℕ :=
  { default := 0}

instance unit_inhabited : inhabited unit :=
  { default := ()}

def default (α : Type _) [s : inhabited α] : α :=
  @inhabited.default α s

def defaul2 (α : Type _) [s : inhabited α] : α :=
  inhabited.default α

--#check default Prop
--#reduce default Prop

instance prod_inhabited {α : Type _} {β : Type _} [inhabited α] [inhabited β] : inhabited (α × β) :=
  { default := (default α, default β)}

--#reduce default (Prop × bool)

instance fun_inhabited (α : Type _) {β : Type _} [inhabited β] : inhabited (α → β) :=
  {default := λ _, default β}

--#reduce default (ℕ → ℕ)

universe u

-- just a structure
class has_add (α : Type u) :=
mk :: (add : α → α → α)

def add {α : Type u} [has_add α] : α → α → α := has_add.add

notation x `+` y := add x y

instance add_nat : has_add ℕ :=
  {add := nat.add}

instance add_prod {α β : Type u} [has_add α] [has_add β] : has_add (α × β) :=
  { add := λ ⟨x₁,x₂⟩ ⟨y₁,y₂⟩, (x₁ + y₁, x₂ + y₂)}

instance add_fun {α β : Type} [has_add β] : has_add (α → β) :=
  {add := λ f g x, f x + g x}

--#reduce (λ (x:ℕ), 1) + (λ x, 2)

end hidden

--#print classes
--#print instances inhabited

def foo : has_add ℕ := by apply_instance
def bar : inhabited (ℕ → ℕ) := by apply_instance

def baz : has_add ℕ := infer_instance
def bla : inhabited (ℕ → ℕ) := infer_instance

--#print foo
--#reduce foo

--#print bar
--#reduce bar

--#reduce (by apply_instance : inhabited ℕ)
--#reduce (infer_instance : inhabited ℕ)

-- example {α : Type} : inhabited (set α) := by apply_instance

def inhabited.set (α : Type) : inhabited (set α) := ⟨∅⟩

-- #print inhabited.set
-- #reduce inhabited.set ℕ

