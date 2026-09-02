Inductive bot : Prop :=.
Inductive empty : Type := .


Definition not : Prop -> Prop :=  fun A:Prop => A -> bot.
Definition not': Type -> Type :=  fun A:Type => A -> empty.


Proposition not_bot : not bot.
Proof.
  unfold not. intro H. exact H.
Qed.

Proposition not_bot' : not' empty.
Proof.
  unfold not'. intro H. exact H.
Qed.


Inductive and(A B:Prop) : Prop := conj : A -> B -> and A B.
Inductive prod(A B:Type) : Type := pair : A -> B -> prod A B.

Inductive or(A B: Prop) : Prop :=
  | or_introl : A -> or A B
  | or_intror : B -> or A B.

Inductive sum(A B: Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.


Inductive ex(A:Type)(P:A->Prop) : Prop :=
  ex_intro: forall x:A, P x -> ex A P.

Inductive sig(A:Type)(P:A->Prop) : Type :=
  exist : forall x:A, P x -> sig A P.

Inductive eq(A:Type): A -> A -> Prop :=
  eq_refl: forall x:A, eq A x x.

(* law of excluded middle *)
Definition LEM : Prop := forall (p:Prop), ~p\/p.

Axiom classic: LEM.

Inductive inhabited (A:Type) : Prop := inhabits : A -> inhabited A.

Axiom e_statement: forall {A:Type}(P:A->Prop),
  inhabited A -> {x:A | (exists x, P x) -> P x}.

Definition e {A:Type}(i: inhabited A)(P:A-> Prop) : A :=
  proj1_sig (e_statement P i).

Definition e_spec {A:Type}(i:inhabited A)(P: A-> Prop) : 
  (exists x, P x) -> P(e i P) := proj2_sig (e_statement P i).

Definition type1 : Type := forall (A:Type)(P:A->Prop),
  inhabited A -> {x:A | (exists x, P x) -> P x}.

Definition type2 : Type := forall (A:Type)(P:A->Prop),
  (exists x, P x) -> {x:A | P x}.

Proposition exist_inhabited : forall (A:Type)(P:A->Prop),
  (exists x, P x) -> inhabited A.
Proof.
  intros A P H. elim H. clear H. intros x H. apply inhabits. exact x.
Qed.




