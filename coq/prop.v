Inductive bot : Prop :=.


Definition not : Prop -> Prop :=  fun A:Prop => A -> bot.


Proposition not_bot : not bot.
Proof.
  unfold not. intro H. exact H.
Qed.

Inductive and(A B:Prop) : Prop := conj : A -> B -> and A B.

Inductive or(A B: Prop) : Prop :=
  | or_introl : A -> or A B
  | or_intror : B -> or A B.

Inductive ex(A:Type)(P:A->Prop) : Prop :=
  ex_intro: forall x:A, P x -> ex A P.

Inductive eq(A:Type): A -> A -> Prop :=
  eq_refl: forall x:A, eq A x x.


