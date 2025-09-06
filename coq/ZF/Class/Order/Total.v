Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that R is a total class on A.                  *)
Definition Total (R A:Class) : Prop := forall (x y:U), A x -> A y ->
  x = y \/ R :(x,y): \/ R :(y,x):.

Proposition TotalIncl : forall (R A B:Class),
  Total R A -> B :<=: A -> Total R B.
Proof.
  intros R A B H1 H2 x y H3 H4. apply H1; apply H2; assumption.
Qed.

Proposition TotalIsom : forall (F R S A B:Class),
  Isom F R S A B -> Total R A <-> Total S B.
Proof.
  (* It is sufficient to prove -> *)
  assert (forall (F R S A B:Class),
    Isom F R S A B -> Total R A -> Total S B) as L. {
    intros F R S A B H1 H2 y1 y2 H3 H4. assert (H5 := H1). destruct H5 as [H5 H6].
    remember (F^:-1:!y1) as x1 eqn:H7. remember (F^:-1:!y2) as x2 eqn:H8.
    assert (A x1) as H9.  { rewrite H7.
      apply Bij.ConverseEvalIsInDomain with B; assumption. }
    assert (A x2) as H10. { rewrite H8.
      apply Bij.ConverseEvalIsInDomain with B; assumption. }
    assert (y1 = F!x1) as H11. { rewrite H7. symmetry.
      apply Bij.EvalOfConverseEval with A B; assumption. }
    assert (y2 = F!x2) as H12. { rewrite H8. symmetry.
      apply Bij.EvalOfConverseEval with A B; assumption. }
    specialize (H2 x1 x2 H9 H10).
    destruct H2 as [H2|[H2|H2]].
    - left. rewrite H11, H12, H2. reflexivity.
    - right. left.  rewrite H11, H12. specialize (H6 x1 x2 H9 H10). apply H6. assumption.
    - right. right. rewrite H11, H12. specialize (H6 x2 x1 H10 H9). apply H6. assumption.
  }
  (* The proof of the equivalence follows. *)
  intros F R S A B H1. split.
  - apply L with F. assumption.
  - apply L with F^:-1:, Isom.Converse. assumption.
Qed.

(* If R is total on A the minimal element of a subclass of A is unique.         *)
Proposition IsUnique : forall (R A B:Class) (x y:U),
  Total R A       ->
  B :<=: A        ->
  Minimal R B x   ->
  Minimal R B y   ->
  x = y.
Proof.

  (* Let R A B be arbitrary classes and x y arbitrary sets. *)
  intros R A B x y.

  (* We assume that R is a total on A. *)
  intros H1. assert (Total R A) as X. apply H1. clear X.

  (* We assume that B is a subclass of A. *)
  intros H2. assert (B :<=: A) as X. apply H2. clear X.

  (* We assume that x is R-minimal in B. *)
  intros H3. assert (Minimal R B x) as X. apply H3. clear X.

  (* And we assume that y is R-minimal in B. *)
  intros H4. assert (Minimal R B y) as X. apply H4. clear X.

  (* We need to show that x = y. *)
  assert (x = y) as X. 2: apply X.

  (* x is also an element of A. *)
  assert (A x) as H5. { apply H2. apply Minimal.IsIn with R. assumption. }

  (* And y is an element of A. *)
  assert (A y) as H6. { apply H2. apply Minimal.IsIn with R. assumption. }

  (* From the totality of R on A we see that x = y \/  x R y \/ y R x. *)
  specialize (H1 x y H5 H6).
  assert (x = y \/ R :(x,y): \/ R :(y,x):) as X. apply H1. clear X.

  (* We consider these three cases separately. *)
  destruct H1 as [H1|[H1|H1]].

  (* We first consider the case when x = y. *)
  - assert (x = y) as X. { apply H1. } clear X.

    (* Then we are done. *)
    assumption.

  (* We then consider the case x R y. *)
  - assert (R :(x,y):) as X. { apply H1. } clear X.

 (* This contradicts the minimality of y. *)
    assert (~R :(x,y):) as H7. {
      apply (Minimal.NotLess _ B). 2: assumption.
      apply (Minimal.IsIn R). assumption.
    }

    contradiction.

  (* We finally consider the case y R x. *)
  - assert (R :(y,x):) as X. { apply H1. } clear X.

 (* This contradicts the minimality of x. *)
    assert (~R :(y,x):) as H7. {
      apply (Minimal.NotLess _ B). 2: assumption.
      apply (Minimal.IsIn R). assumption.
    } contradiction.
Qed.
