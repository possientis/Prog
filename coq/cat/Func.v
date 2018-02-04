Require Import Axiom_Extensionality.
Require Import Axiom_PropEqual.

Definition Relation (a b:Type) : Type := a -> b -> Prop.

Lemma eqRelation : forall (a b:Type) (r s:Relation a b),
    (forall x y, r x y <-> s x y) -> r = s.
Proof.
    intros a b r s H. apply extensionality2. intros x y.
    apply eqProp. apply H. apply H.
Qed.

Definition Total (a b:Type) (r:Relation a b) : Prop :=
    forall (x:a), exists (y:b), r x y.

Arguments Total {a} {b} _.

Definition Functional (a b:Type) (r:Relation a b) : Prop :=
    forall (x:a) (y y':b), r x y -> r x y' -> y = y'.

Arguments Functional {a} {b} _.

Inductive Func (a b:Type) : Type :=
    func : forall (r:Relation a b), Total r -> Functional r -> Func a b.

Arguments func {a} {b} _ _ _.

Notation "a ==> b" := (Func a b) (at level 60, right associativity).

Definition rel (a b:Type) (f:a ==> b) : Relation a b :=
    match f with
    | func r _ _ => r
    end.

Arguments rel {a} {b} _.

Lemma Func_exists : forall (a b:Type) (f:a ==> b) (x:a), 
    exists y, (rel f) x y. 
Proof.
    intros a b [r fTot fFunc] x. destruct (fTot x) as [y Hy].
    exists y. exact Hy.
Qed.

Arguments Func_exists {a} {b} _ _.

Lemma Func_unique : forall (a b:Type) (f:a ==> b) (x:a) (y y':b),
    (rel f) x y -> (rel f) x y' -> y = y'.
Proof.

Show.




(*
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


Definition toFunc (a b:Type) (f:a -> b) : a ==> b :=
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

Definition toRelComp (a b c:Type) (f:a ==> b) (g:b ==> c) : Relation a c :=
    match f with
      func r _ _  =>  
        match g with
          func s _ _  => 
            fun (x:a) => 
              fun (z:c) => 
                exists (y:b), r x y /\ s y z 
        end
    end.

Arguments toRelComp {a} {b} {c} _ _.

Lemma toRelCompTotal : forall (a b c:Type) (f:a ==> b) (g:b ==> c),
    Total(toRelComp f g).
Proof.
    intros a b c [r fTot fFunc] [s gTot gFunc]. unfold Total. intros x. 
    unfold toRelComp. destruct (fTot x) as [y Hy]. destruct (gTot y) as [z Hz].
    exists z, y. split.
    - exact Hy.
    - exact Hz.
Qed.

Arguments toRelCompTotal {a} {b} {c} _ _.

Lemma toRelCompFunctional : forall (a b c:Type) (f:a ==> b) (g:b ==> c),
    Functional(toRelComp f g).
Proof.
    intros a b c [r fTot fFunc] [s gTot gFunc]. unfold Functional.
    intros x z z'. unfold toRelComp. intros [y [Hy Hz]] [y' [Hy' Hz']].
    assert (y = y') as E. { apply (fFunc x y y' Hy Hy'). }
    apply (gFunc y z z' Hz). rewrite E. exact Hz'. 
Qed.

Arguments toRelCompFunctional {a} {b} {c} _ _.

Definition composeFunc (a b c:Type) (f:a ==> b) (g:b ==> c) : a ==> c :=
    func (toRelComp f g) (toRelCompTotal f g) (toRelCompFunctional f g).

Arguments composeFunc {a} {b} {c} _ _.


Notation "f ; g" := (composeFunc f g) (at level 40, left associativity).

(*
Lemma composeFunc_assoc:forall (a b c d:Type)(f:a ==> b)(g:b ==> c)(h: c ==> d),
    f;g;h = f;(g;h).
Proof.
    intros a b c d f g h.

Show.
*)
*)
