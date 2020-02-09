namespace hidden

open list

universe u

def length {α : Type u} (xs : list α) : ℕ :=
  begin
    induction xs with x xs n,
      {exact 0},
      {exact (n + 1)}
  end

#check @length

def reverse {α : Type u} (xs : list α) : list α :=
  begin
    induction xs with x xs rs,
      {exact []},
      {exact (rs ++ [x])}
  end



lemma length_app : ∀ (α : Type u) (xs ys : list α),
  length (xs ++ ys) = length xs + length ys :=
  assume α xs ys,
    begin
      induction xs with x xs IH,
        {by calc
          length ([] ++ ys) = length ys             : by refl
                 ...        = 0 + length ys         : by rw zero_add
                 ...        = length [] + length ys : by refl},
        {by calc
          length ((x :: xs) ++ ys) = length (x :: (xs ++ ys))     : by refl
                     ...           = length (xs ++ ys) + 1        : by refl
                     ...           = length xs + length ys + 1    : by rw IH
                     ...           = length xs + (length ys + 1)  : by rw add_assoc
                     ...           = length xs + (1 + length ys)  : by rw (add_comm 1)
                     ...           = length xs + 1 + length ys    : by rw add_assoc
                     ...           = length (x :: xs) + length ys : by refl}
    end

lemma length_rev : ∀ (α : Type u) (xs : list α),
  length (reverse xs) = length xs :=
  assume α xs,
    begin
      induction xs with x xs IH,
        {by calc
          length (reverse []) = length [] : by refl},
        {by calc
          length (reverse (x :: xs))=length (reverse xs ++ [x])      :by refl
                 ...                =length (reverse xs) + length [x]:by rw length_app
                 ...                =length xs + length [x]          :by rw IH
                 ...                =length xs + 1                   :by refl
                 ...                =length (x :: xs)                :by refl}
    end


lemma rev_rev : ∀ { α : Type u} (xs : list α),
  reverse (reverse xs) = xs :=
  assume α xs,
    begin
      induction xs with x xs IH,
        {by calc
          reverse (reverse []) = reverse [] : _
                  ...          = []         : by refl},
        {}
    end


end hidden
