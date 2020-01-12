inductive WeekDay : Type
| Sunday    : WeekDay
| Monday    : WeekDay
| Tuesday   : WeekDay
| Wednesday : WeekDay
| Thursday  : WeekDay
| Friday    : WeekDay
| Saturday  : WeekDay

#check @WeekDay.Sunday

open WeekDay

#check @Sunday

#check @WeekDay.rec
#check @WeekDay.rec_on


def numberOfDay1 (d : WeekDay) : ℕ := WeekDay.rec_on d 1 2 3 4 5 6 7
def numberOfDay2 (d : WeekDay) : ℕ := WeekDay.rec 1 2 3 4 5 6 7 d
def numberOfDay3 (d : WeekDay) : ℕ := WeekDay.cases_on d 1 2 3 4 5 6 7

#reduce numberOfDay1 Sunday
#reduce numberOfDay1 Monday
#reduce numberOfDay2 Sunday
#reduce numberOfDay2 Monday
#reduce numberOfDay3 Tuesday
#reduce numberOfDay3 Wednesday


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

#reduce (next (next Tuesday))
#reduce (next (previous Tuesday))


lemma L1 : ∀ (d : WeekDay), next (previous d) = d :=
  assume d, WeekDay.cases_on d
    (show next (previous Sunday)     = Sunday     , from rfl)
    (show next (previous Monday)     = Monday     , from rfl)
    (show next (previous Tuesday)    = Tuesday    , from rfl)
    (show next (previous Wednesday)  = Wednesday  , from rfl)
    (show next (previous Thursday)   = Thursday   , from rfl)
    (show next (previous Friday)     = Friday     , from rfl)
    (show next (previous Saturday)   = Saturday   , from rfl)


#check L1


lemma L2 : ∀ (d : WeekDay), next (previous d) = d :=
  assume d,
    begin
      apply WeekDay.cases_on d;
      refl
    end

#check L2

namespace hidden1

universes u v

inductive prod (α : Type u) (β : Type v)
| mk : α → β → prod

#check @prod
#check @prod.mk

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

#reduce prod_example (tt,3)
#reduce prod_example (ff,3)

def sum_example (s : ℕ ⊕ ℕ) : ℕ :=
  sum.cases_on s (λ n, 2 * n) (λ n, 2 * n +1)

#reduce sum_example (sum.inl 3)
#reduce sum_example (sum.inr 3)

#check @sum.inl
#check @sum.inr


namespace hidden3

  universes u v

  inductive prod (α : Type u) (β : Type v)
  | mk (fst : α) (snd : β) : prod

  #check @prod.mk
  #check @prod.fst
  #check @prod.snd
end hidden3

namespace hidden4
  structure prod1 (α β: Type) :=
    mk :: (fst : α) (snd : β)

  #check @prod1.mk
  #check @prod1.fst
  #check @prod1.snd

end hidden4


structure color := (red : ℕ) (green : ℕ) (blue : ℕ)
def yellow := color.mk 255 255 0

#reduce color.red yellow
#reduce color.green yellow
#reduce color.blue yellow


namespace hidden5
universes u v

inductive sigma {α : Type u} (β : α → Type v)
| dpair : Π a : α, β a → sigma

inductive option (α : Type u)
| none {} : option
| some : α → option

inductive inhabited (α : Type u) : Prop
| mk : α → inhabited

#check @inhabited
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

#check subtype p
#check subtype2 p
#check { x : α // p x}


end hidden6






