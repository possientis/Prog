Require Import Axiom_Extensionality.
Require Import Axiom_ProofIrrelevance.
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

Arguments rel {a} {b} _ _ _.

Lemma eqFunc : forall (a b:Type) (f g:a ==> b), rel f = rel g -> f = g.
Proof.
    intros a b f g H. destruct f as [r fTot fFunc]. destruct g as [s gTot gFunc].
    simpl in H. revert gTot gFunc fTot fFunc. rewrite H. clear H r.
    intros gTot gFunc fTot fFunc.
    rewrite (proof_irrelevance _ gTot fTot).
    rewrite (proof_irrelevance _ gFunc fFunc).
    reflexivity.
Qed.

Lemma eqFunc2 : forall (a b:Type) (f g:a ==> b), 
    (forall (x:a) (y:b), rel f x y <-> rel g x y) <-> f = g.
Proof.
    intros a b f g. split.
    - intros H. apply eqFunc. apply eqRelation. exact H.
    - intros H x y. split.
        + intros H'. rewrite <- H. exact H'.
        + intros H'. rewrite H. exact H'.
Qed.


Lemma Func_exists : forall (a b:Type) (f:a ==> b) (x:a), 
    exists y, rel f x y. 
Proof.
    intros a b [r fTot fFunc] x. destruct (fTot x) as [y Hy].
    exists y. exact Hy.
Qed.

Arguments Func_exists {a} {b} _ _.

Lemma Func_unique : forall (a b:Type) (f:a ==> b) (x:a) (y y':b),
    rel f x y -> rel f x y' -> y = y'.
Proof.
    intros a b [r fTot fFunc] x y y' Hy Hy'. simpl in Hy, Hy'.
    apply (fFunc x). exact Hy. exact Hy'.
Qed.

Arguments Func_unique {a} {b} _ _ _ _ _ _.

Definition toRel (a b:Type) (f:a -> b): Relation a b :=
    fun (x:a) (y:b) => f x = y.

Arguments toRel {a} {b} _ _ _.

Lemma toRelTotal : forall (a b:Type) (f:a -> b), Total (toRel f).
Proof.
    intros a b f. unfold Total. intros x. unfold toRel. 
    exists (f x). reflexivity.
Qed.

Arguments toRelTotal {a} {b} _ _.

Lemma toRelFunctional : forall (a b:Type) (f:a -> b), Functional (toRel f).
Proof.
    intros a b f. unfold Functional. intros x y y' Hy Hy'.
    unfold toRel in Hy. unfold toRel in Hy'. rewrite <- Hy, <-Hy'.
    reflexivity.
Qed.

Arguments toRelFunctional {a} {b} _ _ _ _ _ _.


Definition toFunc (a b:Type) (f:a -> b) : a ==> b :=
    func (toRel f) (toRelTotal f) (toRelFunctional f).

Arguments toFunc {a} {b} _.

Lemma relToFunc : forall (a b:Type) (f:a -> b) (x:a) (y:b),
    rel (toFunc f) x y = (f x = y).
Proof.
    intros a b f x y. unfold toFunc. simpl. unfold toRel. reflexivity.
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

Arguments toRelComp {a} {b} {c} _ _ _ _.

Lemma toRelCompTotal : forall (a b c:Type) (f:a ==> b) (g:b ==> c),
    Total(toRelComp f g).
Proof.
    intros a b c [r fTot fFunc] [s gTot gFunc]. unfold Total. intros x. 
    unfold toRelComp. destruct (fTot x) as [y Hy]. destruct (gTot y) as [z Hz].
    exists z, y. split.
    - exact Hy.
    - exact Hz.
Qed.

Arguments toRelCompTotal {a} {b} {c} _ _ _.

Lemma toRelCompFunctional : forall (a b c:Type) (f:a ==> b) (g:b ==> c),
    Functional(toRelComp f g).
Proof.
    intros a b c [r fTot fFunc] [s gTot gFunc]. unfold Functional.
    intros x z z'. unfold toRelComp. intros [y [Hy Hz]] [y' [Hy' Hz']].
    assert (y = y') as E. { apply (fFunc x y y' Hy Hy'). }
    apply (gFunc y z z' Hz). rewrite E. exact Hz'. 
Qed.

Arguments toRelCompFunctional {a} {b} {c} _ _ _ _ _ _ _.

Definition composeFunc (a b c:Type) (f:a ==> b) (g:b ==> c) : a ==> c :=
    func (toRelComp f g) (toRelCompTotal f g) (toRelCompFunctional f g).

Arguments composeFunc {a} {b} {c} _ _.


Notation "f ; g" := (composeFunc f g) (at level 40, left associativity).


Lemma composeFunc_assoc:forall (a b c d:Type)(f:a ==> b)(g:b ==> c)(h: c ==> d),
    f;g;h = f;(g;h).
Proof.
    intros a b c d f g h. apply eqFunc2. intros x t.
    destruct f as [rf fTot fFunc].
    destruct g as [rg gTot gFunc].
    destruct h as [rh hTot hFunc].
    simpl. split.
    - intros [z [[y [H1 H2]] H3]]. exists y. split.
        + exact H1.
        + exists z. split.
            { exact H2. }
            { exact H3. }
    - intros [y [H1 [z [H2 H3]]]]. exists z. split.
        + exists y. split.
            { exact H1. }
            { exact H2. }
        + exact H3.
Qed.

Definition idRel (a:Type) : Relation a a := fun (x y:a) => y = x.

Lemma idRelTotal : forall (a:Type), Total (idRel a).
Proof. intros a. unfold Total. intros x. exists x. reflexivity. Qed.


Lemma idRelFunctional : forall (a:Type), Functional (idRel a).
Proof.
    intros a. unfold Functional. intros x y y'. unfold idRel. intros Hy Hy'.
    rewrite Hy, Hy'. reflexivity.
Qed.

Definition idFunc (a:Type) : a ==> a :=
    func (idRel a) (idRelTotal a) (idRelFunctional a).

Definition compose (a b c:Type) (f:a -> b) (g:b -> c) : a -> c :=
    fun (x:a) => g (f x).

Arguments compose {a} {b} {c} _ _ _.

Notation "g @ f" := (compose f g) (at level 60, right associativity).

Lemma compose_assoc : forall (a b c d:Type) (f:a -> b) (g:b-> c) (h:c -> d),
    h @ g @ f = (h @ g) @ f.
Proof.
    intros a b c d f g h. apply extensionality. intros x. reflexivity.
Qed.

Definition id (a:Type) : a-> a := fun (x:a) => x.

Arguments id {a} _.


Lemma toFunc_compose : forall (a b c:Type) (f:a -> b) (g:b -> c),
    toFunc (g @ f) = toFunc f ; toFunc g.
Proof.
    intros a b c f g. apply eqFunc. unfold compose, composeFunc. simpl.
    apply eqRelation. unfold toRel. intros x z. split.
    - intros H. exists (f x). split.
        + reflexivity.
        + exact H.
    - intros [y [H1 H2]]. rewrite H1. exact H2.
Qed.


Lemma toFunc_id : forall (a:Type), toFunc (id) = idFunc a.
Proof.
    intros a. apply eqFunc2. intros x y. simpl. unfold idRel, toRel, id. split.
    - intros H. symmetry. exact H.
    - intros H. symmetry. exact H.
Qed.





