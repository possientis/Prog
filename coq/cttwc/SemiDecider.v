Require Import Coq.Bool.Bool.

Inductive Sig (a:Type) (p:a -> Type) : Type :=
| Ex : forall (x:a), p x -> Sig a p
.

Arguments Sig {a}.
Arguments Ex {a} {p}.

Definition prj1 (a:Type) (p:a -> Type) (q:Sig p) : a :=
    match q with
    | Ex x _    => x
    end.


Arguments prj1 {a} {p}.

Definition prj2 (a:Type) (p:a -> Type) (q:Sig p) : p (prj1 q) :=
    match q with
    | Ex _ r    => r
    end.

Arguments prj2 {a} {p}.

(* f is a decider for p                                                         *)
Definition Decider (a:Type) (f:a -> bool) (p:a -> Prop) : Prop :=
    forall (x:a), p x <-> f x = true.

Arguments Decider {a}.

Definition Decidable (a:Type) (p:a -> Prop) : Prop :=
    exists (f:a -> bool), Decider f p.

Arguments Decidable {a}.


(* f is a semi-decider for p                                                    *)
Definition SemiDecider (a:Type) (p:a -> Prop) (f:a -> nat -> bool) : Prop :=
    forall (x:a), p x <-> exists (n:nat), f x n = true.

Arguments SemiDecider {a}.

Definition SemiDecidable (a:Type) (p:a -> Prop) : Prop :=
    exists (f:a -> nat -> bool), SemiDecider p f.

Arguments SemiDecidable {a}.

Lemma L1 : forall (a:Type) (p:a -> Prop), Decidable p -> SemiDecidable p.
Proof.
    intros a p. unfold Decidable, SemiDecidable, Decider, SemiDecider.
    intros [f H1]. exists (fun x _ => f x). intros x. split.
    - intros H2. exists 0. apply H1. assumption.
    - intros [_ H2]. apply H1. assumption.
Qed.

Definition tsat (f: nat -> bool) : Prop := exists (n:nat), f n = true.

Lemma L2 : SemiDecidable tsat.
Proof.
    unfold SemiDecidable, tsat, SemiDecider. exists (fun g n => g n).
    intros f. split; auto.
Qed.

(* semi-decision type S(X) associated with proposition X.                       *)
Definition S (X:Prop) : Type := Sig (fun f => X <-> tsat f).

Definition D (X:Prop) : Type := {X} + {~X}.

Definition toSemi : forall (X:Prop), D X -> S X.
Proof.
    unfold D, S. intros X [q|q]. 
    - remember (fun (n:nat) => true) as f eqn:F. assert (X <-> tsat f) as H1.
        { split. 
            { intros H1. exists 0. rewrite F. reflexivity. }
            { intros H1. assumption. }}
      exact (Ex f H1).
    - remember (fun (n:nat) => false) as f eqn:F. assert (X <-> tsat f) as H1.
        { split.
            { intros H1. apply q in H1. contradiction. }
            { intros [n H1]. rewrite F in H1. inversion H1. }}
      exact (Ex f H1).
Defined.

Definition transport : forall (X Y:Prop), (X <-> Y) -> S X -> S Y.
Proof.
    intros X Y [H1 H2] [f [H3 H4]]. assert (Y <-> tsat f) as H5.
        { split.
            { intros H5. apply H3, H2. assumption. }
            { intros H5. apply H1, H4. assumption. }}
    exact (Ex f H5).
Defined.

Definition toSemiOr : forall (X Y:Prop), S X -> S Y -> S (X \/ Y).
Proof.
    intros X Y [f [H1 H2]] [g [G1 G2]]. 
    remember (fun n => orb (f n) (g n)) as h eqn:H.
    assert (X \/ Y <-> tsat h) as H3.
        { split.
            { intros [H3|H3]. 
                { apply H1 in H3. destruct H3 as [n H3].
                  exists n. rewrite H, H3. reflexivity. }
                { apply G1 in H3. destruct H3 as [n H3].
                  exists n. rewrite H, H3. destruct (f n); reflexivity. }}
            { intros [n H3]. destruct (f n) eqn:F; destruct (g n) eqn:G.
                { left. apply H2. exists n. assumption. }
                { left. apply H2. exists n. assumption. }
                { right. apply G2. exists n. assumption. }
                { rewrite H in H3. rewrite F in H3. rewrite G in H3. inversion H3. }}}
    exact (Ex h H3).
Defined.

Variable toNat : nat * nat -> nat.
Variable fromNat : nat -> nat * nat.

Axiom toNatFromNat : forall (n:nat), toNat (fromNat n) = n.
Axiom fromNatToNat : forall (p:nat*nat), fromNat (toNat p) = p. 

Definition fromNat1 (n:nat) : nat := fst (fromNat n).
Definition fromNat2 (n:nat) : nat := snd (fromNat n).


Definition toSemiAnd : forall (X Y:Prop), S X -> S Y -> S (X /\ Y).
Proof.
    intros X Y [f [H1 H2]] [g [G1 G2]]. 
    remember (fun n => andb (f (fromNat1 n)) (g (fromNat2 n))) as h eqn:E. 
    apply Ex with h. split.
    - intros [H3 H4]. apply H1 in H3. apply G1 in H4.
      destruct H3 as [n H3]. destruct H4 as [m H4]. exists (toNat (n,m)).
      rewrite E. unfold fromNat1, fromNat2. rewrite fromNatToNat. simpl.
      rewrite H3, H4. reflexivity.
    - intros [n H3]. rewrite E in H3. apply andb_true_iff in H3.
      destruct H3 as [H3 H4]. split.
        + apply H2. exists (fromNat1 n). assumption.
        + apply G2. exists (fromNat2 n). assumption.
Qed.

(* Certifying semi-decider                                                      *)
Definition CertSemiDecider (a:Type) (p:a -> Prop) : Type := forall (x:a), S (p x).

Arguments CertSemiDecider {a}.

Definition fromCertSD : forall (a:Type) (p:a -> Prop), 
    CertSemiDecider p -> 
    Sig (fun (F:a -> nat -> bool) => forall (x:a), p x <-> tsat (F x)).
Proof.
    unfold CertSemiDecider. intros a p q.
    remember (fun (x:a) (n:nat) => prj1 (q x) n) as F eqn:E. exists F.
    intros x. remember (prj2 (q x)) as H1 eqn:E'. clear E'. simpl in H1.
    rewrite E. assumption.
Defined.

Arguments fromCertSD {a} {p}.

Definition toCertSD : forall (a:Type) (p:a -> Prop),
    Sig (fun (F:a -> nat -> bool) => forall (x:a), p x <-> tsat (F x)) ->
    CertSemiDecider p.
Proof.
    unfold CertSemiDecider. intros a p [F H1] x. apply (Ex (F x)), H1.
Defined.

Lemma L3 : forall (a:Type) (p:a -> Prop),
    SemiDecidable p <-> exists (q:CertSemiDecider p), True.
Proof.
    unfold SemiDecidable, SemiDecider, CertSemiDecider. 
    intros a p. split; intros H1.
    - destruct H1 as [F H1]. exists (fun x => Ex (F x) (H1 x)). trivial.
    - destruct H1 as [q _]. exists (prj1 (fromCertSD q)). 
      exact (prj2 (fromCertSD q)).
Qed.


