Require Import Logic.Class.Eq.

Require Import Logic.Func.Permute.

Require Import Logic.List.In.
Require Import Logic.List.Append.

Require Import Logic.Lam.Free.
Require Import Logic.Lam.Valid.
Require Import Logic.Lam.Syntax.

(* A map f:v -> v is admissible for a term t if and only if it is valid         *)
(* for t and keeps all its free variables unchanged. An admissible mapping      *)
(* has the property of not altering the alpha-equivalence class of a term       *)
Definition admissible (v:Type) (e:Eq v) (f:v -> v) (t:T v) : Prop :=
  valid f t /\ forall (x:v), x :: Fr t -> f x = x.

Arguments admissible {v} {e}.

Lemma admissible_valid : forall (v:Type) (e:Eq v) (f:v -> v) (t:T v),
  admissible f t -> valid f t. 
Proof.
  intros v e f t H1. destruct H1 as [H1 H2]. assumption.
Qed.

Arguments admissible_valid {v} {e}.

Lemma admissible_free : forall (v:Type) (e:Eq v) (f:v -> v) (t:T v),
  admissible f t -> forall (x:v), x :: Fr t -> f x = x.
Proof.
  intros v e f p H1. destruct H1 as [H1 H2]. assumption.
Qed.

Arguments admissible_free {v} {e}.

Lemma admissible_app : forall (v:Type) (e:Eq v) (f:v -> v) (t1 t2:T v),
  admissible f (App t1 t2) <-> admissible f t1 /\ admissible f t2.
Proof.
  intros v e f t1 t2. split; intros H1.
  - split; unfold admissible in H1; destruct H1 as [H1 H3]; 
    apply valid_app in H1; destruct H1 as [H1 H2]; unfold admissible.
    + split.
      * assumption.
      * intros x H4. apply H3. simpl. apply app_charac. left. assumption.
    + split.
      * assumption.
      * intros x H4. apply H3. simpl. apply app_charac. right. assumption.
  - destruct H1 as [[H1 H2] [H3 H4]]. unfold admissible. split.
    + apply valid_app. split; assumption.
    + intros x H5. simpl in H5. apply app_charac in H5. destruct H5 as [H5|H5].
      * apply H2. assumption.
      * apply H4. assumption. 
Qed.

Lemma admissible_permute: forall (v:Type) (e:Eq v) (x y:v) (t:T v),
  ~ x :: Fr t -> ~ y :: Fr t -> admissible (y <:> x) t.
Proof.
  intros v e x y t Hx Hy. split.
  - apply valid_permute.
  - apply free_permute2; assumption.
Qed.

