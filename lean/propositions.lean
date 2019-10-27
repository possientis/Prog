constants p q:Prop

theorem t1 : p → q → p := λ hp:p, λ hq:q, hp

#print t1


theorem t2 : p → q → p :=
assume hp : p,
assume hq : q,
show p, from hp

#print t2

theorem t3 (hp:p) (hq:q) : p := hp

#print t3

axiom hp : p

theorem t4 : q → p := t1 hp

#print t4

theorem t5 : ∀ (p q:Prop), p → q → p :=
λ (p q:Prop) (hp:p) (hq:q), hp

#print t5




