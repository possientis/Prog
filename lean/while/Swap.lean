import Stmt
import Hoare

def Swap : Stmt :=
  "t" :== x ;;
  "x" :== y ;;
  "y" :== aVar "t"


lemma Swap_Correct : ∀ (n m:ℕ), Hoare
  (λ s, s "x" = n ∧ s "y" = m)
  Swap
  (λ s, s "x" = m ∧ s "x" = n) :=
begin
  intros n m,
end
