Require Import Axiom_Extensionality.
Require Import Axiom_ProofIrrelevance.
Require Import Cast.
Require Import JMEq.
Require Import Category3.



Lemma eq_Category3 : forall (c c':Category3) (p: A3 c = A3 c'),
    (forall f:A3 c, cast p (source3 c f) = source3 c' (cast p f)) ->
    (forall f:A3 c, cast p (target3 c f) = target3 c' (cast p f)) ->
    (forall f g:A3 c, 
    cast (toOption p) (compose3 c f g) = compose3 c' (cast p f) (cast p g)) -> 
    c = c'. 
Proof.
    intros c1 c2 p Hs Ht Hc.
    destruct c1 as [A1 s1 t1 cmp1 pss1 pts1 ptt1 pst1 pd1 ps1 pt1 pl1 pr1 pa1]. 
    destruct c2 as [A2 s2 t2 cmp2 pss2 pts2 ptt2 pst2 pd2 ps2 pt2 pl2 pr2 pa2]. 
    simpl in p. simpl in Hs. simpl in Ht. simpl in Hc.
    revert pss1 pts1 ptt1 pst1 pd1 ps1 pt1 pl1 pr1 pa1.
    revert Hs Ht Hc. revert s1 t1 cmp1. 
    rewrite p.
    intros s1 t1 cmp1 Hs Ht Hc.
    simpl in Hs. simpl in Ht. simpl in Hc.
    rewrite (proof_irrelevance _ (toOption eq_refl) eq_refl) in Hc. simpl in Hc.
    apply extensionality in Hs.
    apply extensionality in Ht.
    apply extensionality2 in Hc.
    rewrite Hs, Ht, Hc.
    intros pss1 pts1 ptt1 pst1 pd1 ps1 pt1 pl1 pr1 pa1.
    rewrite (proof_irrelevance _ pss1 pss2).
    rewrite (proof_irrelevance _ pts1 pts2).
    rewrite (proof_irrelevance _ ptt1 ptt2).
    rewrite (proof_irrelevance _ pst1 pst2).
    rewrite (proof_irrelevance _ pd1 pd2).
    rewrite (proof_irrelevance _ ps1 ps2).
    rewrite (proof_irrelevance _ pt1 pt2).
    rewrite (proof_irrelevance _ pl1 pl2).
    rewrite (proof_irrelevance _ pr1 pr2).
    rewrite (proof_irrelevance _ pa1 pa2).
    reflexivity.
Qed.

