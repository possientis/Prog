Require Import Logic.Class.Eq.

Require Import Logic.List.In.
Require Import Logic.List.Append.

Require Import Logic.Fol.Free.
Require Import Logic.Fol.Valid.
Require Import Logic.Fol.Syntax.

(* A map f:v -> v is admissible for a formula p if and only if it is valid      *)
(* for p and keeps all its free variables unchanged. An admissible mapping      *)
(* has the property of not altering the alpha-equivalence class of a formula    *)
Definition admissible (v:Type) (e:Eq v) (f:v -> v) (p:P v) : Prop :=
  valid f p /\ forall (x:v), x :: Fr p -> f x = x.

Arguments admissible {v} {e}.

Lemma admissible_valid : forall (v:Type) (e:Eq v) (f:v -> v) (p:P v),
  admissible f p -> valid f p. 
Proof.
  intros v e f p H1. destruct H1 as [H1 H2]. assumption.
Qed.

Arguments admissible_valid {v} {e}.

Lemma admissible_free : forall (v:Type) (e:Eq v) (f:v -> v) (p:P v),
  admissible f p -> forall (x:v), x :: Fr p -> f x = x.
Proof.
  intros v e f p H1. destruct H1 as [H1 H2]. assumption.
Qed.

Arguments admissible_free {v} {e}.

Lemma admissible_imp : forall (v:Type) (e:Eq v) (f:v -> v) (p1 p2:P v),
  admissible f (Imp p1 p2) <-> admissible f p1 /\ admissible f p2.
Proof.
  intros v e f p1 p2. split; intros H1.
  - split; unfold admissible in H1; destruct H1 as [H1 H3]; 
    apply valid_imp in H1; destruct H1 as [H1 H2]; unfold admissible.
    + split.
      * assumption.
      * intros x H4. apply H3. simpl. apply app_charac. left. assumption.
    + split.
      * assumption.
      * intros x H4. apply H3. simpl. apply app_charac. right. assumption.
  - destruct H1 as [[H1 H2] [H3 H4]]. unfold admissible. split.
    + apply valid_imp. split; assumption.
    + intros x H5. simpl in H5. apply app_charac in H5. destruct H5 as [H5|H5].
      * apply H2. assumption.
      * apply H4. assumption. 
Qed.
