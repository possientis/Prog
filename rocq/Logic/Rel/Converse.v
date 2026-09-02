Require Import Logic.Axiom.Extensionality.

Require Import Logic.Rel.R.
Require Import Logic.Rel.Id.
Require Import Logic.Rel.Composition.

(* Converse operator. Needed for Rel to be an allegory.                         *)
Definition conv (a b:Type) (r:R a b) : R b a := fun y x => r x y.
Arguments conv {a} {b}.

Lemma conv_charac : forall (a b:Type) (r:R a b) (x:a) (y:b),
    conv r y x <-> r x y.
Proof.
    intros a b r x y. unfold conv. split; auto.
Qed.

Lemma conv_conv : forall (a b:Type) (r:R a b), conv (conv r) = r.
Proof.
    intros a b r. apply Ext. intros x y. unfold conv. split; auto.
Qed.

Lemma conv_comp : forall (a b c:Type) (r:R a b) (s:R b c),
    conv (s ; r) = conv r ; conv s.
Proof.
    intros a b c r s. apply Ext. intros x y. unfold conv, comp. 
    split; intros [z [H1 H2]]; exists z; split; assumption.
Qed.

Lemma conv_id : forall (a:Type), conv (@id a) = id.
Proof.
    intros a. apply Ext. intros x y. split; intros H1; 
    inversion H1; subst; constructor.
Qed.



