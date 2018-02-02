Require Import Axiom_Extensionality.

Definition Relation (a b:Type) : Type := a -> b -> Prop.

Definition Total (a b:Type) (r:Relation a b) : Prop :=
    forall (x:a), exists (y:b), r x y.

Arguments Total {a} {b} _.

Definition Functional (a b:Type) (r:Relation a b) : Prop :=
    forall (x:a) (y y':b), r x y -> r x y' -> y = y'.

Arguments Functional {a} {b} _.

Inductive Func (a b:Type) : Type :=
    func : forall (r:Relation a b), Total r -> Functional r -> Func a b.

Arguments func {a} {b} _ _ _.

Definition toRel (a b:Type) (f:a -> b): Relation a b :=
    fun (x:a) (y:b) => f x = y.

Arguments toRel {a} {b} _.

Lemma toRelTotal : forall (a b:Type) (f:a -> b), Total (toRel f).
Proof.
    intros a b f. unfold Total. intros x. unfold toRel. 
    exists (f x). reflexivity.
Qed.

Arguments toRelTotal {a} {b} _.

Lemma toRelFunctional : forall (a b:Type) (f:a -> b), Functional (toRel f).
Proof.
    intros a b f. unfold Functional. intros x y y' Hy Hy'.
    unfold toRel in Hy. unfold toRel in Hy'. rewrite <- Hy, <-Hy'.
    reflexivity.
Qed.

Arguments toRelFunctional {a} {b} _.

Notation "a => b" := (Func a b) (at level 60, right associativity).

Definition toFunc (a b:Type) (f:a -> b) : a => b :=
    func (toRel f) (toRelTotal f) (toRelFunctional f).

Arguments toFunc {a} {b} _.

Lemma toFuncEmbedding : forall (a b:Type)(f g:a -> b),
    toFunc f = toFunc g -> f = g.
Proof.
    intros a b f g H. apply extensionality. intros x.
    inversion H as [H']. clear H. assert (toRel f x (g x)) as H0.
    { rewrite H'. unfold toRel. reflexivity. }
    unfold toRel in H0. exact H0.
Qed.



