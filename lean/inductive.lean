open tactic.interactive

inductive WeekDay : Type
| Sunday    : WeekDay
| Monday    : WeekDay
| Tuesday   : WeekDay
| Wednesday : WeekDay
| Thursday  : WeekDay
| Friday    : WeekDay
| Saturday  : WeekDay

--#check @WeekDay.Sunday

open WeekDay

--#check @Sunday

--#check @WeekDay.rec
--#check @WeekDay.rec_on


def numberOfDay1 (d : WeekDay) : ℕ := WeekDay.rec_on d 1 2 3 4 5 6 7
def numberOfDay2 (d : WeekDay) : ℕ := WeekDay.rec 1 2 3 4 5 6 7 d
def numberOfDay3 (d : WeekDay) : ℕ := WeekDay.cases_on d 1 2 3 4 5 6 7

--#reduce numberOfDay1 Sunday
--#reduce numberOfDay1 Monday
--#reduce numberOfDay2 Sunday
--#reduce numberOfDay2 Monday
--#reduce numberOfDay3 Tuesday
--#reduce numberOfDay3 Wednesday


def next (d : WeekDay) : WeekDay := WeekDay.cases_on d
  Monday
  Tuesday
  Wednesday
  Thursday
  Friday
  Saturday
  Sunday


def previous (d : WeekDay) : WeekDay := WeekDay.cases_on d
  Saturday
  Sunday
  Monday
  Tuesday
  Wednesday
  Thursday
  Friday

--#reduce (next (next Tuesday))
--#reduce (next (previous Tuesday))


lemma L1 : ∀ (d : WeekDay), next (previous d) = d :=
  assume d, WeekDay.cases_on d
    (show next (previous Sunday)     = Sunday     , from rfl)
    (show next (previous Monday)     = Monday     , from rfl)
    (show next (previous Tuesday)    = Tuesday    , from rfl)
    (show next (previous Wednesday)  = Wednesday  , from rfl)
    (show next (previous Thursday)   = Thursday   , from rfl)
    (show next (previous Friday)     = Friday     , from rfl)
    (show next (previous Saturday)   = Saturday   , from rfl)


--#check L1


lemma L2 : ∀ (d : WeekDay), next (previous d) = d :=
  assume d,
    begin
      apply WeekDay.cases_on d;
      refl
    end

--#check L2

namespace hidden1

universes u v

inductive prod (α : Type u) (β : Type v)
| mk : α → β → prod

--#check @prod
--#check @prod.mk

inductive sum (α : Type u) (β : Type v)
| inl {} : α → sum
| inr {} : β → sum


end hidden1

namespace hidden2
universes u v

def fst {α : Type u} {β : Type v} (p : α × β) : α :=
  prod.rec_on p (λ a b,  a)

def snd {α : Type u} {β : Type v} (p : α × β) : β :=
  prod.rec_on p (λ a b, b)

end hidden2


def prod_example (p: bool × ℕ) : ℕ :=
  prod.rec_on p (λ b n, cond b (2*n) (2*n +1))

--#reduce prod_example (tt,3)
--#reduce prod_example (ff,3)

def sum_example (s : ℕ ⊕ ℕ) : ℕ :=
  sum.cases_on s (λ n, 2 * n) (λ n, 2 * n +1)

--#reduce sum_example (sum.inl 3)
--#reduce sum_example (sum.inr 3)

--#check @sum.inl
--#check @sum.inr


namespace hidden3

  universes u v

  inductive prod (α : Type u) (β : Type v)
  | mk (fst : α) (snd : β) : prod

  --#check @prod.mk
  --#check @prod.fst
  --#check @prod.snd
end hidden3

namespace hidden4
  structure prod1 (α β: Type) :=
    mk :: (fst : α) (snd : β)

  --#check @prod1.mk
  --#check @prod1.fst
  --#check @prod1.snd

end hidden4


structure color := (red : ℕ) (green : ℕ) (blue : ℕ)
def yellow := color.mk 255 255 0

--#reduce color.red yellow
--#reduce color.green yellow
--#reduce color.blue yellow


namespace hidden5
universes u v

inductive sigma {α : Type u} (β : α → Type v)
| dpair : Π a : α, β a → sigma

inductive option (α : Type u)
| none {} : option
| some : α → option

inductive inhabited (α : Type u) : Prop
| mk : α → inhabited

--#check @inhabited
end hidden5


namespace hidden6

inductive false : Prop

inductive true : Prop
| intro : true

inductive and (a b:Prop) : Prop
| intro : a → b → and

inductive or (a b:Prop) : Prop
| intro_left  : a → or
| intro_right : b → or

universe u
inductive Exists {α : Type u} (p:α → Prop) : Prop
| intro : ∀ (a:α), p a → Exists

def exists.intro := @Exists.intro


inductive subtype {α : Type u} (p : α → Prop)
| mk : Π x : α, p x → subtype

structure subtype2 {α : Sort u} (p : α → Prop) :=
  (val : α) (property : p val)

variables {α : Type u} (p : α → Prop)

--#check subtype p
--#check subtype2 p
--#check { x : α // p x}


end hidden6


inductive foo : Type
| bar1 : ℕ → ℕ → foo
| bar2 : ℕ → ℕ → ℕ → foo

--#check @foo

def silly1 (x : foo) : ℕ :=
  begin
    cases x with a b c d e,
      {exact (a + b)},
      {exact (c + d + e)}
  end

--#check @silly1

open foo

def silly2 (x : foo) : ℕ :=
begin
  cases x,
    case bar1 : a b
      {exact b},
    case bar2 : c d e
      {exact e}
end

--#check @silly2

def silly3 (x : foo) : ℕ :=
begin
  cases x,
    case bar2 : c d e
      {exact e},
    case bar1 : a b
      {exact b}
end

--#check @silly3


open nat

variable p : ℕ → Prop

lemma L3 : p 0 → (∀ n, p (succ n)) → ∀(m k : ℕ),  p (m + 3 * k) :=
  assume hz hs m k,
    begin
      cases (m + 3 * k),
        {exact hz},
        {apply hs}
    end

--#check L3

lemma L4 : p 0 → (∀ n, p (succ n)) → ∀(m k : ℕ),  p (m + 3 * k) :=
  assume hz hs m k,
    begin
      generalize : m + 3 * k = n,
      cases n,
        {exact hz},
        {apply hs}
    end


--#check L4

lemma L5 : ∀ (p : Prop) (m n : ℕ), (m < n → p) → (m ≥ n → p) → p :=
  assume p m n H1 H2,
    begin
      cases lt_or_ge m n with H H,
        {apply H1, assumption},
        {apply H2, assumption}
    end

--#check L5


lemma L6 : ∀ (p : Prop) (m n : ℕ), (m < n → p) → (m ≥ n → p) → p :=
  assume p m n H1 H2,
    begin
      have H : m < n ∨ m ≥ n,
        {apply lt_or_ge},
        {cases H with H H,
          {apply H1, assumption},
          {apply H2, assumption}}
    end

--#check L6

--#check @nat.sub_self

lemma L7 : ∀ (m n : ℕ), m - n = 0 ∨ m ≠ n :=
  assume m n,
    begin
      cases decidable.em (m = n) with H H,
        {rewrite H, left, apply nat.sub_self},
        {right, assumption}
    end

--#check L7


def f (m k : ℕ) : ℕ :=
  begin
    cases m - k,  -- hmmmm 
      {exact 3},  -- ≤ 0 it seems
      {exact 7}   -- > 0 it seems
  end

example : f 5 5 = 3  := rfl
example : f 5 7 = 3  := rfl
example : f 10 2 = 7 := rfl


lemma L8 : ∀ (n : ℕ), 0 + n = n :=
  assume n,
    begin
      induction n with n IH,
        {reflexivity},
        {simp}
    end

lemma L9 : ∀ (m n : ℕ), succ m + n = succ (m + n) :=
  assume m n,
    begin
      induction n with n IH,
        { by calc
             succ m + 0 = succ m       : rfl
               ...      = succ (m + 0) : rfl
        },
        { by calc
             succ m + succ n = succ (succ m + n)   : by refl
                    ...      = succ (succ (m + n)) : by rw IH
                    ...      = succ (m + succ n)   : by refl
        }
    end

--#check L9

--#check @zero_add

lemma L10 : ∀ (m n : ℕ), m + n = n + m :=
  assume m n,
    begin
      induction n with n IH,
        by calc
             m + 0  = m     : by refl
             ...    = 0 + m : by begin symmetry, apply zero_add end,
        by calc
            m + succ n = succ (m + n) : by refl
              ...      = succ (n + m) : by rw IH
              ...      = succ n + m   : by begin symmetry, apply L9 end
    end

--#check L10

lemma L11 : ∀ (n : ℕ), 0 + n = n :=
  assume n,
    by induction n; simp only [*, add_zero, add_succ]

--#check L11


lemma L12 : ∀ (m n p : ℕ), (m + n) + p = m + (n + p) :=
  assume m n p,
    begin
      induction p with p IH,
        by calc
          (m + n) + 0 = m + n       : by refl
            ...       = m + (n + 0) : by refl,
        by calc
          (m + n) + succ p = succ ((m + n) + p) : by refl
               ...         = succ (m + (n + p)) : by rw IH
               ...         = m + succ (n + p)   : by refl
               ...         = m + (n + succ p)   : by refl
    end

--#check L12


lemma L13 : ∀ (m n p : ℕ), succ (succ m) = succ (succ n) → n + p = m + p :=
  assume m n p H,
    begin
      injection H with H', clear H, injection H' with H, rewrite H
    end

--#check L13


lemma L14 : ∀ (m n p : ℕ), succ (succ m) = succ (succ n) → n + p = m + p :=
  assume m n p H,
    begin
      injections with H1 H2,
      rewrite H2
    end

--#check L14

lemma L15 : ∀ (m n p : ℕ), succ (succ m) = succ (succ n) → n + p = m + p :=
  assume m n p H, by injections; simp *

--#check L15


lemma L16 : ∀ (m n : ℕ), succ m = 0 → n = n + 7 :=
  assume m n H, by injections

--#check L16


lemma L17 : ∀ (m n : ℕ), succ m = 0 → n = n + 7 :=
  assume m n H, by contradiction

--#check L17


lemma L18 : 7 = 4 → false :=
  assume H, by injections

--#check L18




