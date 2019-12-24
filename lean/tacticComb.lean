lemma L1 : ∀ (p q:Prop), p → p ∨ q :=
  begin intros p q H, left, assumption end

#check L1

lemma L2 : ∀ (p q:Prop), p → p ∨ q :=
  assume p q (H : p), by {left, assumption}

#check L2

lemma L3 : ∀ (p q:Prop), p → q → p ∧ q :=
  assume p q Hp Hq, by {split; assumption}

#check L3

lemma L4 : ∀ (p q:Prop), p → p ∨ q :=
  assume p q Hp, by {left, assumption} <|> {right, assumption}

#check L4

lemma L5 : ∀ (p q:Prop), q → p ∨ q :=
  assume p q Hq, by {left, assumption} <|> {right, assumption}

#check L5


lemma L6 : ∀ (p q r:Prop), p → p ∨ q ∨ r :=
  assume p q r H, by repeat {{left, assumption} <|> right <|> assumption}

#check L6


lemma L7 : ∀ (p q r:Prop), q → p ∨ q ∨ r :=
  assume p q r H, by repeat {{left, assumption} <|> right <|> assumption}

#check L7


lemma L8 : ∀ (p q r:Prop), r → p ∨ q ∨ r :=
  assume p q r H, by repeat {{left, assumption} <|> right <|> assumption}

#check L8

meta def my_tac : tactic unit :=
  `[ repeat { {left, assumption} <|> right <|> assumption}]

#check my_tac


lemma L9 : ∀ (p q r:Prop), p → p ∨ q ∨ r :=
  assume p q r H, by my_tac

#check L9


lemma L10 : ∀ (p q r:Prop), q → p ∨ q ∨ r :=
  assume p q r H, by my_tac

#check L10

lemma L11 : ∀ (p q r:Prop), r → p ∨ q ∨ r :=
  assume p q r H, by my_tac

#check L11


lemma L12 : ∀ (p q r:Prop), p → q → r → p ∧ q ∧ r :=
  assume p q r Hp Hq Hr, by split; try {split}; assumption

#check L12


lemma L13 : ∀ (p q r:Prop), p → q → r → p ∧ q ∧ r :=
  assume p q r Hp Hq Hr, by
    begin
      split,
      all_goals {try {split}},
      all_goals {assumption}
    end

#check L13


lemma L14 : ∀ (p q r:Prop), p → q → r → p ∧ q ∧ r :=
  assume p q r Hp Hq Hr, by
    begin
      split,
      any_goals {split},
      any_goals {assumption}
    end

#check L14


lemma L15 : ∀ (p q r:Prop), p → q → r → p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) :=
  assume p q r Hp Hq Hr,
    begin
      repeat {any_goals {split}},
      all_goals {assumption}
    end

#check L15


lemma L16 : ∀ (p q r:Prop), p → q → r → p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) :=
  assume p q r Hp Hq Hr,
    begin
      repeat {any_goals {split <|> assumption}}
    end

#check L16
