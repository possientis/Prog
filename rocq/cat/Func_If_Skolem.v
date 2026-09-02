Require Import Axiom_Skolem.


Definition lem (p:Prop) : Prop := p \/ ~p.


Definition ifRel (a b:Type) (p:Prop) (f g:a -> b) (x:a) (y:b) : Prop :=
    (p /\ y = f x) \/ (~p /\ y = g x).

Arguments ifRel {a} {b} _ _ _ _ _.


Lemma ifRelFunctional : forall (a b:Type) (p:Prop) (f g:a -> b) (x:a) (y y':b),
    (ifRel p f g x y) -> (ifRel p f g x y') -> y = y'.
Proof.
    intros a b p f g x y y'.
    unfold ifRel. intros [[Hp H1]|[Hp H1]] [[Hq H2]|[Hq H2]].
    - rewrite <- H2 in H1. exact H1. 
    - exfalso. apply Hq. exact Hp.
    - exfalso. apply Hp. exact Hq.
    - rewrite <- H2 in H1. exact H1.
Qed.

Arguments ifRelFunctional {a} {b} _ _ _ _ _ _ _ _.


Lemma ifRelTotal : forall (a b:Type) (p:Prop) (f g:a -> b),
    lem p -> forall (x:a), exists (y:b), (ifRel p f g x y).
Proof.
    unfold ifRel. intros a b p f g [H|H] x.
    - exists (f x). left. split.
        + exact H.
        + reflexivity.
    - exists (g x). right. split.
        + exact H.
        + reflexivity.
Qed.

Arguments ifRelTotal {a} {b} _ _ _ _ _.


Definition ifFunc (a b:Type) (p:Prop) (q:lem p) (f g:a -> b) (x:a) : b :=
    proj1_sig (skolem 
        (ifRel p f g x) 
        (ifRelTotal p f g q x) 
        (ifRelFunctional p f g x)).



Arguments ifFunc {a} {b} _ _ _ _ _.

Definition ifFunc_proof (a b:Type) (p:Prop) (q:lem p) (f g:a -> b) (x:a) :
    (ifRel p f g x (ifFunc p q f g x)) 
:=
    proj2_sig (skolem 
        (ifRel p f g x) 
        (ifRelTotal p f g q x) 
        (ifRelFunctional p f g x)).


Arguments ifFunc_proof {a} {b} _ _ _ _ _.


Lemma ifFunc_correct_true : forall (a b:Type)(p:Prop)(q:lem p)(f g:a -> b)(x:a),
    p -> ifFunc p q f g x = f x.
Proof.
    intros a b p q f g x Hp. 
    assert (ifRel p f g x (ifFunc p q f g x)) as [[H1 H2]|[H1 H2]]. 
        { exact (ifFunc_proof p q f g x). }
    - exact H2.
    - exfalso. apply H1. exact Hp.
Qed.
    
Lemma ifFunc_correct_false : forall (a b:Type)(p:Prop)(q:lem p)(f g:a -> b)(x:a),
    ~p -> ifFunc p q f g x = g x.
Proof.
    intros a b p q f g x Hp. 
    assert (ifRel p f g x (ifFunc p q f g x)) as [[H1 H2]|[H1 H2]]. 
        { exact (ifFunc_proof p q f g x). }
    - exfalso. apply Hp. exact H1.
    - exact H2.
Qed.

    
