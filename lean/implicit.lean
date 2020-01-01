namespace hidden
variables {α : Type} (r : α → α → Prop)

definition reflexive : Prop := ∀ (a:α), r a a

#check @reflexive
#print reflexive

definition symmetric : Prop := ∀ {a b : α}, r a b → r b a

#check @symmetric
#print symmetric

definition transitive : Prop := ∀ {a b c : α}, r a b → r b c → r a c

#check @transitive
#print transitive

definition euclidean : Prop := ∀ {a b c : α}, r a b → r a c → r b c

#check @euclidean
#print euclidean

theorem T1 : reflexive r → euclidean r → symmetric r :=
  assume R E a b, assume : r a b,
    begin
      apply E,
        assumption,
        begin apply R end,
    end

#check T1

end hidden
