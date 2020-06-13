inductive nat2 : Type
| zero : nat2
| succ : nat2 -> nat2

--#print nat2

inductive aexp : Type
| num : nat -> aexp         -- TODO: need Z
| var : string -> aexp
| add : aexp -> aexp -> aexp
| sub : aexp -> aexp -> aexp
| mul : aexp -> aexp -> aexp
| div : aexp -> aexp -> aexp

lemma add_zero2 : ∀ (n : ℕ), 0 + n = n :=
begin
  intros n,
  induction n with n IH,
    {reflexivity},
    {simp}
end



