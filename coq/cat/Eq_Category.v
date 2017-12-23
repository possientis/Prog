Require Import Axiom_Extensionality.
Require Import Axiom_ProofIrrelevance.
Require Import Category.

Lemma eq_Category : forall (A:Type) (c c':Category A),
    (forall f:A, source c f = source c' f) ->
    (forall f:A, target c f = target c' f) ->
    (forall f g:A, compose c f g = compose c' f g) -> c = c'. 
Proof.
    intros A c1 c2 Hs Ht Hc. 
    destruct c1 as [s1 t1 cmp1 pss1 pts1 ptt1 pst1 pd1 ps1 pt1 pl1 pr1 pa1].
    destruct c2 as [s2 t2 cmp2 pss2 pts2 ptt2 pst2 pd2 ps2 pt2 pl2 pr2 pa2].
    simpl in Hs. simpl in Ht. simpl in Hc.
    apply extensionality in Hs.
    apply extensionality in Ht.
    apply extensionality2 in Hc.
    revert pss1 pts1 ptt1 pst1 pd1 ps1 pt1 pl1 pr1 pa1.
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


