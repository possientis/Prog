open nat

def sub1 : ℕ → ℕ
| zero     := zero
| (succ x) := x


def is_zero : ℕ → Prop
| zero     := true
| (succ x) := false


example : sub1 0 = 0 := rfl
example (n : ℕ) : sub1 (succ n) = n := rfl

example : is_zero 0 = true := rfl
example (n : ℕ) : is_zero (succ n) = false := rfl


example : sub1 7 = 6 := rfl
example (n : ℕ) : ¬ is_zero (n + 3) := begin  simp [is_zero]end

def sub1' : ℕ → ℕ
| 0 := 0
| (n+1) := n

universes u v
variables {α : Type u} {β : Type v}

def swap : α × β → β × α
| (x,y) := (y,x)

def foo : ℕ × ℕ → ℕ
| (m,n) := m + n

def bar : option ℕ → ℕ
| (some n) := n + 1
| none     := 0

def nbot : bool → bool
| tt := ff
| ff := tt

lemma bnot_invol : ∀ (b : bool), bnot (bnot b) = b
| tt := rfl
| ff := rfl

example (p q:Prop) : p ∧ q → q ∧ p
| ⟨x,y⟩ := ⟨y,x⟩

open or

example (p q:Prop) : p ∨ q → q ∨ p
| (inl x) := inr x
| (inr y) := inl y

open nat

def sub2 : ℕ → ℕ
| zero             := 0
| (succ zero)      := 0
| (succ (succ x))  := x

def sub2' : ℕ → ℕ
| 0       := 0
| 1       := 0
| (x + 2) := x

example : ∀ (n : ℕ), sub2 n = sub2' n
| 0     := rfl
| 1     := rfl
| (n+2) := rfl

#print sub2
#print sub2._main

example {α : Type u} (p q: α → Prop) : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
| ⟨x,(inl px)⟩ := inl ⟨x,px⟩
| ⟨x,(inr qx)⟩ := inr ⟨x,qx⟩

def foo2 : ℕ × ℕ → ℕ
| (0,n)     := 0
| (m+1,0)   := 1
| (m+1,n+1) := 2


def foo3 : ℕ → ℕ → ℕ
| 0 n             := 0
| (m + 1) 0       := 1
| (m + 1) (n + 1) := 2

def bar2 : list ℕ → list ℕ → ℕ
| []            []        := 0
| (x :: xs)     []        := x
| []            (y :: ys) := y
| (x :: xs)     (y :: ys) := x + y


def band2 : bool → bool → bool
| tt b := b
| ff _ := ff

def bor2 : bool → bool → bool
| ff b := b
| tt _ := tt


def {w} cond2 {a : Type u} : bool → a → a → a
| tt x _ := x
| ff _ y := y

def tail1 {α : Type u} : list α → list α
| []         := []
| (x :: xs)  := xs


def tail2 : Π {α : Type u}, list α → list α
| α []        := []
| α (x :: xs) := xs


lemma tail_same : ∀ (α : Type u) (xs : list α), tail1 xs = tail2 xs
| α []        := rfl
| α (x :: xs) := rfl

lemma tail_same2 {α : Type u} : ∀ (xs : list α), tail1 xs = tail2 xs
| []        := rfl
| (x :: xs) := rfl

def tail_same3 {α : Type u} : ∀ (xs : list α), tail1 xs = tail2 xs
| []        := rfl
| (x :: xs) := rfl

def tail_same4 : ∀ (α : Type u) (xs : list α), tail1 xs = tail2 xs
| α []        := rfl
| α (x :: xs) := rfl

def tail_same5 : Π (α : Type u) (xs : list α), tail1 xs = tail2 xs
| α []        := rfl
| α (x :: xs) := rfl

#check @tail_same
#check @tail_same2
#check @tail_same3
#check @tail_same4
#check @tail_same5


lemma L1 : @tail_same3 = @tail_same4 := rfl

#check L1

-- overallping pattern
def foo4 : ℕ → ℕ → ℕ
| 0 n := 0
| m 0 := 1
| m n := 2


example : foo4 0 0 = 0 := rfl
example : ∀ (n:ℕ), foo4 0 (n + 1) = 0 := assume n, rfl
example : ∀ (n:ℕ), foo4 (n+1) 0 = 1 := assume n, rfl
example : ∀ (n m:ℕ), foo4 (n+1) (m+1) = 2 := assume n m, rfl

-- overallping pattern
def foo5 : ℕ → ℕ → ℕ
| 0 _ := 0
| _ 0 := 1
| _ _ := 2


-- arbitrary is not a random value
def foo6 : ℕ → ℕ → ℕ
| 0 _ := 1
| _ 0 := 2
| _ _ := arbitrary ℕ

variables (a b : ℕ)

example : foo6 0 0 = 1 := rfl

example : foo6 0 (a + 1) = 1 := rfl

example : foo6 (a + 1) 0 = 2 := rfl

example : foo6 (a + 1) (b + 1) = arbitrary ℕ := rfl

#check arbitrary ℕ

#reduce arbitrary ℕ


-- option a
def foo7 : ℕ → ℕ → option ℕ
| 0 _ := some 1
| _ 0 := some 2
| _ _ := none

example : foo7 0 0 = some 1 := rfl

example : foo7 0 (a + 1) = some 1 := rfl

example : foo7 (a + 1) 0 = some 2 := rfl

example : foo7 (a + 1) (b + 1) = none := rfl


-- can tell whether pattern match is complete or not
def foo8 : ℕ → list ℕ → bool → ℕ
| 0      _       ff := 0
| 0     (b :: _) _  := b
| 0     []       tt := 7
| (a+1) []       ff := a
| (a+1) []       tt := a + 1
| (a+1) (b :: _) _  := a + b


def foo9 : char → ℕ
| 'A' := 1
| 'B' := 2
| _   := 3


#check foo9
#print foo9._main

def add2 : ℕ → ℕ → ℕ
| n 0        := n
| n (succ m) := succ (add2 n m)


local infix `⊕` : 50 := add2


lemma add_zero2 : ∀ (n : ℕ), n ⊕ 0 = n := assume n, rfl
lemma add_succ2 : ∀ (n m : ℕ), n ⊕ (succ m) = succ (n ⊕ m) := assume n m, rfl

#check @congr_arg

lemma zero_add2 : ∀ (n : ℕ), 0 ⊕ n = n
| 0        := rfl
| (succ n) := congr_arg succ (zero_add2 _)


lemma zero_add3 : ∀ (n : ℕ), 0 ⊕ n = n :=
  assume n,
    begin
      induction n with n IH,
        {by refl},
        {by calc
          0 ⊕ (succ n)  = succ (0 ⊕ n)  : by refl
              ...       = succ n        : by rw IH}
    end

