mutual inductive even, odd
with even : ℕ → Prop
| even_zero : even 0
| even_succ : ∀ n, odd n → even (n + 1)
with odd : ℕ → Prop
| odd_succ : ∀ n, even n → odd (n + 1)

universe u

namespace hidden

mutual inductive tree, list_tree (α : Type u)
with tree : Type u
| node : α → list_tree → tree
with list_tree : Type u
| nil {} : list_tree
| cons : tree → list_tree → list_tree

open list_tree

#check @nil

end hidden

-- nested inductive type, 'tree' appears inside the 'list' type constructor
inductive tree (α : Type u)
| mk : α → list tree → tree



