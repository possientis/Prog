Require Import Axiom_Extensionality.
Require Import Axiom_PropEqual.
Require Import Axiom_Skolem.
Require Import Axiom_ProofIrrelevance.

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

Lemma eqFunc : forall (a b:Type) (f g:a ==> b), rel f = rel g -> f = g.
Proof.
    intros a b f g H. destruct f as [r fTot fFunc]. destruct g as [s gTot gFunc].
    simpl in H. revert gTot gFunc fTot fFunc. rewrite H. clear H r.
    intros gTot gFunc fTot fFunc.
    rewrite (proof_irrelevance _ gTot fTot).
    rewrite (proof_irrelevance _ gFunc fFunc).
    reflexivity.
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

Definition Func_app (a b:Type) (f:a ==> b) (x:a) : b :=
    proj1_sig (skolem (rel f x) (Func_exists f x) (Func_unique f x)).


Arguments Func_app {a} {b} _ _.

 
Definition fromFunc (a b:Type) (f:a ==> b) : a -> b :=
    fun (x:a) => Func_app f x.

Arguments fromFunc {a} {b} _ _.

Lemma fromFunc_correct : forall (a b:Type) (f:a ==> b) (x:a),
    rel f x (fromFunc f x).
Proof.
    intros a b [r fTot fFunc] x. simpl. unfold fromFunc, Func_app.
    remember (skolem (rel (func r fTot fFunc) x)
              (Func_exists (func r fTot fFunc) x)
              (Func_unique (func r fTot fFunc) x)) as sk eqn:H.
    exact (proj2_sig sk).
Qed.

Lemma fromFunc_eval : forall (a b:Type) (f:a ==> b) (x:a) (y:b),
    y = fromFunc f x <-> rel f x y.
Proof.
    intros a b f x y. split.
    - intros H. rewrite H. apply fromFunc_correct.
    - intros H. apply (Func_unique f x).
        + exact H.
        + apply fromFunc_correct.
Qed.

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

Lemma relToFunc : forall (a b:Type) (f:a -> b) (x:a) (y:b),
    rel (toFunc f) x y = (f x = y).
Proof.
    intros a b f x y. unfold toFunc. simpl. unfold toRel. reflexivity.
Qed.

Lemma fromTo : forall (a b:Type) (f:a -> b), fromFunc (toFunc f) = f.
Proof.
    intros a b f. apply extensionality. intros x.
    apply (Func_unique (toFunc f) x).
    rewrite relToFunc. apply fromFunc_eval.
    - simpl. unfold toRel. reflexivity.
    - simpl. unfold toRel. reflexivity.
Qed.

Lemma toFrom : forall (a b:Type) (f:a ==> b), toFunc (fromFunc f) = f.
Proof.
    intros a b f. apply eqFunc. apply eqRelation. intros x y. split.
    - intros H. rewrite relToFunc in H. symmetry in H.
        apply fromFunc_eval. exact H.
    - intros H. rewrite relToFunc. symmetry. apply fromFunc_eval. exact H.
Qed.


Corollary toFuncEmbedding : forall (a b:Type) (f g:a -> b),
    toFunc f = toFunc g -> f = g.
Proof.
    intros a b f g H. assert (fromFunc (toFunc f) = fromFunc (toFunc g)) as H'.
    { rewrite H. reflexivity. }
    rewrite fromTo in H'. rewrite fromTo in H'. exact H'.
Qed.

Corollary fromFuncEmbedding : forall (a b:Type) (f g:a ==> b), 
    fromFunc f = fromFunc g -> f = g.
Proof.
    intros a b f g H. assert (toFunc (fromFunc f) = toFunc (fromFunc g)) as H'.
    { rewrite H. reflexivity. }
    rewrite toFrom in H'. rewrite toFrom in H'. exact H'.
Qed.

(* With the skolem axiom, we have a bijection between a ==> b and a -> b.
   Hence we could define function composition by transporting argument
   into the type a -> b. We attempt here to define it directly
*)

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

(* we need to check our 'direct' definition coincides what we expect *)

Lemma composeFunc_correct : forall (a b c:Type) (f:a ==> b) (g:b ==> c) (x:a),
    fromFunc (f ; g) x = fromFunc g (fromFunc f x).
Proof.
    intros a b c f g x. symmetry. apply fromFunc_eval.
    destruct f as [r fTot fFunc] eqn:Hf. destruct g as [s gTot gFunc] eqn:Hg.
    simpl. rewrite <- Hf. rewrite <- Hg. exists (fromFunc f x). split.
    - assert (r = rel f) as Hr. { rewrite Hf. reflexivity. } 
        rewrite Hr. apply fromFunc_correct. 
    - remember (fromFunc f x) as y eqn:Hy.
        assert (s = rel g) as Hs. { rewrite Hg. reflexivity. }
        rewrite Hs. apply fromFunc_correct. 
Qed.

Definition compose (a b c:Type) (f:a -> b) (g:b -> c) : a -> c :=
    fun (x:a) => g (f x).

Arguments compose {a} {b} {c} _ _.

Notation "g @ f" := (compose f g) (at level 60, right associativity).

Definition id (a:Type) : a-> a := fun (x:a) => x.

Arguments id {a} _.

Definition idFunc (a:Type) : a ==> a := toFunc id.

Lemma fromFunc_compose : forall (a b c:Type) (f:a ==> b) (g:b ==> c),
    fromFunc (f ; g) = fromFunc g @ fromFunc f.
Proof.
    intros a b c f g. apply extensionality. intros x. unfold compose.
    apply composeFunc_correct.
Qed.

Lemma fromFunc_id : forall (a:Type), fromFunc (idFunc a) = id.
Proof. intros a. unfold idFunc. apply fromTo. Qed.


Lemma toFunc_compose : forall (a b c:Type) (f:a -> b) (g:b -> c),
    toFunc (g @ f) = toFunc f ; toFunc g.
Proof.
    intros a b c f g.

Show.



(*
(* this leads to an easy proof of associativity *)

Lemma composeFunc_assoc:forall (a b c d:Type)(f:a ==> b)(g:b ==> c)(h: c ==> d),
    f;g;h = f;(g;h).
Proof.
    intros a b c d f g h.

Show.
*)
