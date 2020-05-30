Require Import List.

Require Import In.
Require Import Eq.
Require Import Equiv.

Lemma app_charac : forall (v:Type) (xs ys:list v) (z:v),
    z :: (xs ++ ys) <-> z :: xs \/ z :: ys.
Proof.
    intros v xs ys z. split.
    - apply in_app_or.
    - apply in_or_app.
Qed.

Lemma app_compat_l : forall (v:Type) (xs xs' ys:list v),
    xs == xs' -> xs ++ ys == xs' ++ ys.
Proof.
    intros v xs xs' ys [H1 H2]. split; intros z H3;
    apply app_charac in H3; destruct H3 as [H3|H3]; 
    apply app_charac.
    - left. apply H1. assumption.
    - right. assumption.
    - left. apply H2. assumption.
    - right. assumption.
Qed.

Lemma app_compat_r : forall (v:Type) (xs ys ys':list v),
    ys == ys' -> xs ++ ys == xs ++ ys'.
Proof.
    intros v xs ys ys' [H1 H2]. split; intros z H3;
    apply app_charac in H3; destruct H3 as [H3|H3]; 
    apply app_charac.
    - left. assumption.
    - right. apply H1. assumption.
    - left. assumption.
    - right. apply H2. assumption.
Qed.

Lemma app_compat_lr : forall (v:Type) (e:Eq v) (xs xs' ys ys':list v),
    xs == xs' -> ys == ys' -> xs ++ ys == xs' ++ ys'.
Proof.
    intros v e xs xs' ys ys' H1 H2. apply equivTrans with (xs' ++ ys).
    - apply app_compat_l. assumption.
    - apply app_compat_r. assumption.
Qed.

