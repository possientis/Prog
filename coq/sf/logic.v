Require Import not.

Definition LEM          := forall (P:Prop), P \/ ¬P. 
Definition Double_Neg   := forall (P:Prop), (¬¬P) -> P.
Definition Peirce       := forall (P Q:Prop), ((P -> Q) -> P) -> P.
Definition DeMorgan     := forall (P Q:Prop), ¬(¬P /\ ¬Q) -> P \/ Q.
Definition Implies      := forall (P Q: Prop), (P -> Q) -> (¬P \/ Q).

Theorem LEM_irrefutable : forall (P:Prop), 
    ¬ ¬ (P \/ ¬ P).
Proof.
    intros P H. 
    assert ( ¬P ) as H'. { intro Hp. apply H. left. exact Hp. }
    apply H. right. exact H'.
Qed.


Theorem LEM_Double_Neg : LEM <-> Double_Neg.
Proof.
    unfold LEM, Double_Neg. split.
    - intros H P H'. destruct (H P) as [H1|H1].
        + exact H1.
        + exfalso. apply H'. exact H1.
    - intros H P. apply H. apply LEM_irrefutable.
Qed.

Theorem LEM_Peirce : LEM <-> Peirce.
Proof.
    unfold LEM, Peirce. split.
    - intros H P Q H'. destruct (H P) as [H1|H1].
        + exact H1.
        + apply H'. intros H0. exfalso. apply H1. exact H0.
    - intros H P. apply H with (Q := False).
        intros H'. right. intros H0. apply H'. left. exact H0.
Qed.


Theorem LEM_DeMorgan : LEM <-> DeMorgan.
Proof.
    unfold LEM, DeMorgan. split.
    - intros H P Q H'. 
        assert ((P \/ Q) \/ ¬(P \/Q)) as H0. { apply H. }
        destruct H0 as [H1|H1].
            + exact H1.
            + exfalso. apply H'. split.
                { intros H0. apply H1. left. exact H0. }
                { intros H0. apply H1. right. exact H0. }
    - intros H P. apply H. intros [H1 H2]. apply H2. exact H1.
Qed.


Theorem LEM_Implies : LEM <-> Implies.
Proof.
    unfold LEM, Implies. split.
    - intros H P Q H'. destruct (H P) as [H1|H1].
        + right. apply H'. exact H1.
        + left. exact H1.
    - intros H P. assert (¬P \/ P) as H0.
        { apply H. intros H'. exact H'. }
        destruct H0 as [H1|H1].
            + right. exact H1.
            + left. exact H1.
Qed.


Theorem restricted_LEM : forall (P:Prop) (b:bool),
    (P <-> b = true) -> P \/ ¬P.
Proof.
    intros P b [H1 H2]. destruct b eqn:H.
    - left. apply H2. reflexivity.
    - right. intros H'. apply H1 in H'. inversion H'.
Qed.

Theorem not_exists_forall : forall (a:Type) (P:a -> Prop),
    ¬ (exists x, P x) -> forall x, ¬ P x.
Proof. intros a P H x Px. apply H. exists x. exact Px. Qed.

(* we need LEM for this one *)
Theorem not_exists_forall_strong : LEM ->
    forall (a:Type) (P:a -> Prop), ¬ (exists x, ¬ P x) -> forall x, P x.
Proof.
    intros H a P H' x. assert (Double_Neg) as H0. { apply LEM_Double_Neg. exact H. }
    apply H0. set (Q := fun x => ¬ P x). apply (not_exists_forall a Q). exact H'.
Qed.








