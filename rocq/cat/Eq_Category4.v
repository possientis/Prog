Require Import Axiom_Extensionality.
Require Import Axiom_ProofIrrelevance.
Require Import Cast.
Require Import JMEq.
Require Import Category4.

Lemma eq_Category4:forall (c c':Category4),
    forall  (p : Obj4 c = Obj4 c') (q: Mor4 c = Mor4 c'),
    (forall f:Mor4 c, cast p (dom4 c f) = dom4 c' (cast q f)) ->
    (forall f:Mor4 c, cast p (cod4 c f) = cod4 c' (cast q f)) ->
    (forall a:Obj4 c, cast q (id4 c a)  = id4  c' (cast p a)) ->
    (forall f g:Mor4 c, 
    cast (toOption q) (compose4 c f g) = compose4 c' (cast q f) (cast q g)) ->
    c = c'.
Proof.
    intros c1 c2 p q Hs Ht Hi Hc.
    destruct c1 as [O1 M1 s1 t1 cmp1 i1 psi1 pti1 pd1 ps1 pt1 pl1 pr1 pa1].
    destruct c2 as [O2 M2 s2 t2 cmp2 i2 psi2 pti2 pd2 ps2 pt2 pl2 pr2 pa2].
    simpl in p. simpl in q. simpl in Hs. simpl in Ht. simpl in Hi. simpl in Hc.
    revert psi1 pti1 pd1 ps1 pt1 pl1 pr1 pa1.
    revert Hs Ht Hi Hc. revert s1 t1 cmp1 i1.
    rewrite p, q.
    intros s1 t1 cmp1 i1 Hs Ht Hi Hc.
    simpl in Hs. simpl in Ht. simpl in Hi. simpl in Hc.
    rewrite (proof_irrelevance _ (toOption eq_refl) eq_refl) in Hc. simpl in Hc.
    apply extensionality  in Hs.
    apply extensionality  in Ht.
    apply extensionality  in Hi.
    apply extensionality2 in Hc.
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

   


