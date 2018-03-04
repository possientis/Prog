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

