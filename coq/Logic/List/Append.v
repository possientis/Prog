Require Import List.

Require Import Logic.List.In.
Require Import Logic.List.Equiv.

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

Lemma app_compat_lr : forall (v:Type) (xs xs' ys ys':list v),
    xs == xs' -> ys == ys' -> xs ++ ys == xs' ++ ys'.
Proof.
    intros v xs xs' ys ys' H1 H2. apply equivTrans with (xs' ++ ys).
    - apply app_compat_l. assumption.
    - apply app_compat_r. assumption.
Qed.

(* not very useful                                                              *)
Lemma app_assoc' : forall (v:Type) (xs ys zs:list v),
    (xs ++ ys) ++ zs == xs ++ (ys ++ zs).
Proof.
    intros v xs ys zs. rewrite app_assoc. apply equivRefl.
Qed.

Lemma app_comm : forall (v:Type) (xs ys:list v),
    xs ++ ys == ys ++ xs.
Proof.
    intros v xs ys. split; intros z; intros H1;
    apply in_app_or in H1; destruct H1 as [H1|H1]; apply in_or_app.
    - right. assumption.
    - left. assumption.
    - right. assumption.
    - left. assumption.
Qed.

Lemma app_nil : forall (v:Type) (xs ys:list v),
    xs ++ ys = nil -> xs = nil /\ ys = nil.
Proof.
    intros v xs ys. destruct xs as [|x xs]; destruct ys as [|y ys]; 
    simpl; intros H.
    - split; reflexivity.
    - inversion H.
    - inversion H.
    - inversion H.
Qed.
