Require Import Axiom_Extensionality.
Require Import Axiom_ProofIrrelevance.
Require Import Cast.
Require Import Category5.
Require Import Setoid.
 

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
    assert (Hom1 = Hom2) as H. { apply extensionality2. exact q. }
    revert q. rewrite H. clear H. simpl. intros q. 
    assert (forall a b, q a b = eq_refl) as Hq. 
        { intros a b. apply proof_irrelevance. }
    intros cmp1 i1 Hc Hi. 
    assert (i1 = i2) as Hi'.
        { apply extensionality. intros a. rewrite <- (Hi a).
            rewrite (proof_irrelevance _ (q a a) eq_refl).
            reflexivity.
        }
    rewrite Hi'.
    assert (cmp1 = cmp2) as Hc'.
    { apply extensionality3. intros a b c. 
      apply extensionality2. intros f g.
      assert (cast (q a b) f = f) as Hf.
        { rewrite (proof_irrelevance _ (q a b) eq_refl). reflexivity. }
      assert (cast (q b c) g = g) as Hg.
        { rewrite (proof_irrelevance _ (q b c) eq_refl). reflexivity. }
        rewrite <- Hf at 2. (* need 'Setoid' for some reason *)
        rewrite <- Hg at 2. 
        rewrite <- (Hc a b c).
        rewrite (proof_irrelevance _ (q a c) eq_refl). reflexivity.
    }
    rewrite Hc'.
    intros pl1 pr1 pa1.
    rewrite (proof_irrelevance _ pl1 pl2).
    rewrite (proof_irrelevance _ pr1 pr2).
    rewrite (proof_irrelevance _ pa1 pa2).
    reflexivity.
Qed.
        
