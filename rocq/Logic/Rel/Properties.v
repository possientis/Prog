Require Import Logic.Axiom.Extensionality.

Require Import Logic.Rel.R. 
Require Import Logic.Rel.Converse.
Require Import Logic.Rel.Composition.

(* Reflexive predicate on Rel a                                                 *)
Definition reflexive (a:Type) (r:Rel a) : Prop := forall (x:a), 
    r x x.

Arguments reflexive {a}.

(* Symmetric predicate on Rel a                                                 *)
Definition symmetric (a:Type) (r:Rel a) : Prop := forall (x y:a), 
    r x y -> r y x.

Arguments symmetric {a}.

(* Transitive predicate on Rel a                                                *)
Definition transitive (a:Type) (r:Rel a) : Prop := forall (x y z:a), 
    r x y -> r y z -> r x z.

Arguments transitive {a}.

Definition antisymmetric (a:Type) (r:Rel a) : Prop := forall (x y:a),
    r x y -> r y x -> x = y.

Arguments antisymmetric {a}.

(* Equivalence predicate on Rel a                                               *)
Definition equivalence (a:Type) (r:Rel a) : Prop := 
    reflexive r /\ symmetric r /\ transitive r.

Arguments equivalence {a}.

Definition partial_order (a:Type) (r:Rel a) : Prop :=
    reflexive r /\ antisymmetric r /\ transitive r.

Arguments partial_order {a}.

Definition idempotent (a:Type) (r:Rel a) : Prop := 
    r ; r = r.

Arguments idempotent {a}.

Lemma sym_trans_idem : forall (a:Type) (r:Rel a), 
    symmetric r -> transitive r -> idempotent r.
Proof.
    intros a r H1 H2. apply Ext. intros x y. split; intros H3.
    - destruct H3 as [z [H3 H4]]. apply H2 with z; assumption.
    - exists x. split; try assumption.
      apply H2 with y; try assumption. apply H1. assumption.
Qed.

Lemma sym_trans_conv : forall (a:Type) (r:Rel a),
    (symmetric r /\ transitive r) <-> r = r ; conv r.
Proof.
    intros a r. split; intros H1.
    - destruct H1 as [H1 H2]. apply Ext. intros x y. split; intros H3.
        + exists x. split; try assumption. apply H2 with y; try assumption.
          apply H1. assumption.
        + destruct H3 as [z [H3 H4]]. apply H2 with z; try assumption.
          apply H1. assumption.
    - assert (symmetric r) as H2.
        { intros x y H3. rewrite H1 in H3. destruct H3 as [z [H3 H4]].
          rewrite H1. exists z. split; assumption. }
      split; try assumption. intros x y z H3 H4. rewrite H1. exists y.
      split; try assumption. apply H2. assumption.
Qed.
