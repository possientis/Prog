universe u

def LEM   : Prop := ∀ (A:Prop), A ∨ ¬A
def IRREL : Prop := ∀ (A:Prop) (p q:A), p = q

-- Proof irrelevance is true in lean by default, unlike Coq
lemma L1 : IRREL :=
  assume A p q,
    begin
      simp
    end

lemma L2 : IRREL := λ (A:Prop) (p:A) (q:A), rfl

inductive Accessible {α : Sort u} (r : α → α → Prop) : α → Prop
| MkAcc : ∀ (x:α), (∀ (y:α), r y x → Accessible y) → Accessible x

def WellFounded {α : Sort u} (r : α → α → Prop) : Prop := ∀ (x:α), Accessible r x

lemma LessThanAccIsAcc : ∀ {α : Sort u} (r : α → α → Prop) (x y : α),
  r y x → Accessible r x → Accessible r y :=
  assume α r x y R Ax,
    begin
      cases Ax with x H,
      apply H, assumption
    end

open nat
open has_lt

lemma AllNatsAccessible : ∀ (n : ℕ), Accessible (<) n :=
  assume n,
    begin
      induction n with n IH; constructor,
        {from assume n H, by cases H},
        {from assume m H, begin cases decidable.em (m = n) with H' H',
              {rewrite H', assumption},
              {unfold has_lt.lt at H, unfold nat.lt at H, from sorry}
        end}
    end


lemma AccessibleInv' : ∀ (α : Sort u) (r : α → α → Prop) (x : α),
  Accessible r x -> ∀ (y:α), r y x -> Accessible r y :=
    assume a r x H,
      begin
        cases H with x H,
        assumption
      end

