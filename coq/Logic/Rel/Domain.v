Require Import Logic.Axiom.Extensionality.

Require Import Logic.Rel.R.
Require Import Logic.Rel.Id.
Require Import Logic.Rel.Range.
Require Import Logic.Rel.Include.
Require Import Logic.Rel.Converse.
Require Import Logic.Rel.Composition.
Require Import Logic.Rel.Coreflexive.

(* Domain of a relation defined as coreflexive relation rather than set         *)
Inductive dom (a b:Type) (r:R a b) : Rel a :=
| mkDom : forall (x:a), (exists (y:b), r x y) -> dom a b r x x
.

Arguments dom {a} {b}.

Lemma dom_corefl : forall (a b:Type) (r:R a b), coreflexive (dom r).
Proof.
    unfold coreflexive. intros a b r. apply incl_charac. intros x y H1.
    destruct H1. constructor.
Qed.


Lemma dom_universal : forall (a b:Type) (r:R a b) (s:Rel a), s <= id -> 
    dom r <= s <-> r <= r ; s.
Proof.
    intros a b r s H1. split; intros H2; apply incl_charac; intros x y H3.
    - unfold comp. exists x. split; try assumption.
      assert (dom r x x) as H4.
        { constructor. exists y. assumption. }
      apply incl_charac_to with (dom r); assumption.
    - destruct H3 as [x [y H3]].
      apply (incl_charac_to _ _ _ (r ; s)) in H3; try assumption.
      unfold comp in H3. destruct H3 as [z [H3 H4]]. generalize H3. intros H3'.
      apply (incl_charac_to _ _ _ id) in H3'; try assumption. 
      destruct H3'. assumption.
Qed.

Lemma dom_rng_conv : forall (a b:Type) (r:R a b), dom r = rng (conv r).
Proof.
    intros a b r. apply Ext. intros x y. split; intros H1;
    destruct H1 as [x [y H1]]; constructor; exists y; assumption.
Qed.

Lemma rng_dom_conv : forall (a b:Type) (r:R a b), rng r = dom (conv r).
Proof.
    intros a b r. apply Ext. intros x y. split; intros H1;
    destruct H1 as [y [x H1]]; constructor; exists x; assumption.
Qed.



