Require Import Axiom_Extensionality.
Require Import Axiom_ProofIrrelevance.
Require Import Cast.
Require Import Category5.
 

Lemma eq_Category5 : forall (C C':Category5) (p:Obj C = Obj C'),
    forall (q:forall a b: Obj C, Hom a b = Hom (cast p a) (cast p b)),
    (forall (a b c:Obj C) (f:Hom a b) (g:Hom b c),
        cast (q a c) (f ; g) = cast (q a b) f ; cast (q b c) g) ->
    (forall (a:Obj C), cast (q a a) (id a) = id (cast p a)) -> C = C'.
Proof.
    intros C1 C2 p q Hc Hi.
    destruct C1 as [Obj1 Hom1 cmp1 i1 pl1 pr1 pa1].
    destruct C2 as [Obj2 Hom2 cmp2 i2 pl2 pr2 pa2].
    simpl in p. simpl in q. simpl in Hc. simpl in Hi.
    revert pl1 pr1 pa1.
    revert Hc Hi. revert cmp1 i1. revert q. revert Hom1.
    rewrite p.
    intros Hom1 q. simpl in q.
    intros cmp1 i1 Hc Hi. simpl in Hc. simpl in Hi.

Show.
