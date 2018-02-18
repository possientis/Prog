Require Import Axiom_Extensionality.
Require Import Axiom_Skolem.
Require Import Func.

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


Lemma fromFunc_compose : forall (a b c:Type) (f:a ==> b) (g:b ==> c),
    fromFunc (f ; g) = fromFunc g @ fromFunc f.
Proof.
    intros a b c f g. apply extensionality. intros x. unfold compose.
    apply composeFunc_correct.
Qed.

Lemma fromFunc_id : forall (a:Type), fromFunc (idFunc a) = id.
Proof. 
    intros a. apply extensionality. intros x. symmetry.
    apply fromFunc_eval. simpl. unfold idRel. unfold id. reflexivity.
Qed.



