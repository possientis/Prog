Require Import Axiom_Extensionality.
Require Import Axiom_ProofIrrelevance.
Require Import Category2.

Lemma eq_Category2 : forall (Obj Mor:Type) (c c':Category2 Obj Mor),
    (forall f:Mor, dom c f = dom c' f) ->
    (forall f:Mor, cod c f = cod c' f) ->
    (forall a:Obj, id c a = id c' a)   ->
    (forall f g:Mor, compose2 c f g = compose2 c' f g) -> c = c'.
Proof.
    intros Obj Mor c1 c2 Hs Ht Hi Hc.
    destruct c1 as [s1 t1 cmp1 i1 psi1 pti1 pd1 ps1 pt1 pl1 pr1 pa1].
    destruct c2 as [s2 t2 cmp2 i2 psi2 pti2 pd2 ps2 pt2 pl2 pr2 pa2].
    simpl in Hs. simpl in Ht. simpl in Hc. simpl in Hi.
    apply extensionality  in Hs.
    apply extensionality  in Ht.
    apply extensionality  in Hi.
    apply extensionality2 in Hc.
    revert psi1 pti1 pd1 ps1 pt1 pl1 pr1 pa1.
    rewrite Hs, Ht, Hi, Hc.
    intros psi1 pti1 pd1 ps1 pt1 pl1 pr1 pa1.
    rewrite (proof_irrelevance _ psi1 psi2).
    rewrite (proof_irrelevance _ pti1 pti2).
    rewrite (proof_irrelevance _ pd1 pd2).
    rewrite (proof_irrelevance _ ps1 ps2).
    rewrite (proof_irrelevance _ pt1 pt2).
    rewrite (proof_irrelevance _ pl1 pl2).
    rewrite (proof_irrelevance _ pr1 pr2).
    rewrite (proof_irrelevance _ pa1 pa2).
    reflexivity.
Qed.


