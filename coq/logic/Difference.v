Require Import List.

Require Import In.
Require Import Eq.
Require Import Equiv.
Require Import Concat.
Require Import Include.
Require Import Intersect.

(* diff cannot be defined in terms of intersection, as there is no such thing   *)
(* as a 'complement list' of ys. Such complement would in general be infinite.  *) 
Fixpoint diff (v:Type) (e:Eq v) (xs ys:list v) : list v :=
    match xs with
    | nil       => nil
    | cons x xs =>
        match in_dec eqDec x ys with
        | left  _   => diff v e xs ys
        | right _   => cons x (diff v e xs ys)
        end
    end.

Arguments diff {v} {e}.

Notation "xs \\ ys" := (diff xs ys) 
    (at level 50, left associativity) : Difference_scope.

Open Scope Difference_scope.

Lemma diff_charac : forall (v:Type) (e:Eq v) (xs ys:list v) (z:v),
    z :: (xs \\ ys) <-> z :: xs /\ ~ z :: ys.
Proof.
    intros v e xs ys z. split.
    - induction xs as [|x xs IH]; intros H.
        + inversion H.
        + destruct (in_dec eqDec x ys) as [H'|H'] eqn:E; 
          simpl in H; rewrite E in H.
            { apply IH in H. destruct H as [H1 H2]. split.
                { right. assumption. }
                { assumption. }
            }
            { destruct H as [H|H].
                { subst. split.
                    { left. reflexivity. }
                    { assumption. }
                }
                { apply IH in H. destruct H as [H1 H2]. split.
                    { right. assumption. }
                    { assumption. }
                }
            }
    - induction xs as [|x xs IH]; intros [H1 H2].
        + inversion H1.
        + destruct (in_dec eqDec x ys) as [H|H] eqn:E; simpl; rewrite E.
            { destruct H1 as [H1|H1].
                { subst. exfalso. apply H2. assumption. }
                { apply IH. split; assumption. }
            }
            { destruct H1 as [H1|H1].
                { subst. left. reflexivity. }
                { right. apply IH. split; assumption. }
            }
Qed.

(* TODO: need == instead of <= *)
Lemma diff_inter_comm : forall (v:Type) (e:Eq v) (xs ys zs:list v),
    (xs /\ ys) \\ zs <= ((xs \\ zs) /\ ys).
Proof.
    intros v e xs ys zs x H. rewrite diff_charac in H. 
    destruct H as [H1 H3]. rewrite inter_charac in H1. destruct H1 as [H1 H2].
    apply inter_charac. split.
    - apply diff_charac. split; assumption.
    - assumption.
Qed.

Lemma diff_distrib_app_r : forall (v:Type) (e:Eq v) (xs ys zs:list v),
    (xs ++ ys) \\ zs = (xs \\ zs) ++ (ys \\ zs).
Proof.
    intros v e. induction xs as [|x xs IH]; intros ys zs.
    - reflexivity.
    - rewrite <- app_comm_cons. simpl. destruct (in_dec eqDec x zs) as [H|H].
        + apply IH.
        + rewrite <- app_comm_cons. rewrite IH. reflexivity.
Qed.

Lemma diff_distrib_app_l : forall (v:Type) (e:Eq v) (xs ys zs:list v),
    zs \\ (xs ++ ys) = ((zs \\ xs) /\ (zs \\ ys)).
Proof.
    intros v e xs ys zs. revert xs ys. induction zs as [|z zs IH]; intros xs ys.
    - reflexivity.
    - simpl. destruct (in_dec eqDec z (xs ++ ys)) as [H1|H1].
        + destruct (in_dec eqDec z xs) as [H2|H2]; 
          destruct (in_dec eqDec z ys) as [H3|H3].
            { apply IH. }
            { rewrite inter_cons_not_in_r.
                { apply IH. }
                { intros H4. rewrite diff_charac in H4. destruct H4 as [H4 H5].
                  apply H5. assumption. }}
            { rewrite inter_cons_not_in_l.
                { apply IH. }
                { intros H4. rewrite diff_charac in H4. destruct H4 as [H4 H5].
                    apply H5. assumption. }}
            { exfalso. apply in_app_or in H1. destruct H1 as [H1|H1].
                { apply H2. assumption. }
                { apply H3. assumption. }}
        + destruct (in_dec eqDec z xs) as [H2|H2];
          destruct (in_dec eqDec z ys) as [H3|H3].
            { exfalso. apply H1. apply in_or_app. left. assumption. }
            { exfalso. apply H1. apply in_or_app. left. assumption. }
            { exfalso. apply H1. apply in_or_app. right. assumption. }
            { rewrite IH. simpl. destruct (eqDec z z) as [H4|H4].
                { destruct (in_dec eqDec z zs) as [H5|H5].
                    { rewrite inter_cons_in_r.
                        { reflexivity. }
                        { apply diff_charac; split; assumption. }}
                    { rewrite inter_cons_not_in_r.
                        { reflexivity. }
                        { rewrite diff_charac. intros [H6 H7].
                          apply H5. assumption. }}}
                { exfalso. apply H4. reflexivity. }}
Qed.

Lemma diff_distrib_app_l' : forall (v:Type) (e:Eq v) (xs ys zs:list v),
    zs \\ (xs ++ ys) = (zs \\ xs) \\ ys.
Proof.
    intros v e xs ys zs. revert xs ys. induction zs as [|z zs IH]; intros xs ys.
    - reflexivity.
    - simpl. destruct (in_dec eqDec z (xs ++ ys)) as [H1|H1].
        + destruct (in_dec eqDec z xs) as [H2|H2]; simpl;
          destruct (in_dec eqDec z ys) as [H3|H3].
            { apply IH. }
            { apply IH. }
            { apply IH. }
            { exfalso. apply in_app_or in H1. destruct H1 as [H1|H1].
                { apply H2. assumption. }
                { apply H3. assumption. }}
        + destruct (in_dec eqDec z xs) as [H2|H2]; simpl;
          destruct (in_dec eqDec z ys) as [H3|H3].
            { exfalso. apply H1. apply in_or_app. left. assumption. }
            { exfalso. apply H1. apply in_or_app. left. assumption. }
            { exfalso. apply H1. apply in_or_app. right. assumption. }
            { rewrite IH. reflexivity. }
Qed. 

Lemma diff_nil : forall (v:Type) (e:Eq v) (xs:list v),
    xs \\ nil = xs.
Proof.
    intros v e. induction xs as [|x xs IH].
    - reflexivity.
    - simpl. rewrite IH. reflexivity.
Qed.

Lemma diff_incl_r : forall (v:Type) (e:Eq v) (xs ys zs:list v),
    xs <= ys -> zs \\ ys <= zs \\ xs.
Proof.
    intros v e xs ys zs H1 z H2. apply diff_charac. apply diff_charac in H2. 
    destruct H2 as [H2 H3]. split.
    - assumption.
    - intros H4. apply H3, H1. assumption.
Qed.

Lemma diff_compat_l : forall (v:Type) (e:Eq v) (xs xs' ys:list v),
    xs == xs' -> xs \\ ys == xs' \\ ys.
Proof.
    intros v e xs xs' ys [H1 H2]. split; intros z H3; 
    apply diff_charac in H3; destruct H3 as [H3 H4];
    apply diff_charac; split.
    - apply H1. assumption.
    - assumption.
    - apply H2. assumption.
    - assumption.
Qed.

Lemma diff_compat_r : forall (v:Type) (e:Eq v) (xs ys ys':list v),
    ys == ys' -> xs \\ ys == xs \\ ys'.
Proof.
    intros v e xs ys ys' [H1 H2]. split; intros z H3;
    apply diff_charac in H3; destruct H3 as [H3 H4];
    apply diff_charac; split.
    - assumption.
    - intros H5. apply H4, H2. assumption.
    - assumption.
    - intros H5. apply H4, H1. assumption.
Qed.

Lemma diff_compat_lr : forall (v:Type) (e:Eq v) (xs xs' ys ys':list v),
    xs == xs' -> ys == ys' -> xs \\ ys == xs' \\ ys'.
Proof.
    intros v e xs xs' ys ys' H1 H2. apply equivTrans with (xs' \\ ys).
    - apply diff_compat_l. assumption.
    - apply diff_compat_r. assumption.
Qed.

Lemma diff_not_in : forall (v:Type) (e:Eq v) (xs ys:list v),
    (forall (z:v), z :: ys -> ~ z :: xs) -> xs \\ ys = xs.
Proof.
    intros v e. induction xs as [|x xs IH]; intros ys H1.
    - reflexivity.
    - simpl. destruct (in_dec eqDec x ys) as [H2|H2].
        + exfalso. apply (H1 x).
            { assumption. }
            { left. reflexivity. }
        + rewrite IH.
            { reflexivity. }
            { intros z H3 H4. apply (H1 z).
                { assumption. }
                { right. assumption. }}
Qed.

Lemma diff_concat : forall (v:Type) (e:Eq v) (xss:list(list v)) (ys:list v),
    (forall (xs:list v) (y:v), y :: ys -> xs :: xss -> ~ y :: xs) ->
    concat xss \\ ys = concat xss.
Proof.
    intros v e. induction xss as [|xs xss IH]; intros ys H1.
    - reflexivity.
    - simpl. rewrite diff_distrib_app_r, IH.
        + assert (xs \\ ys = xs) as H2.
            { apply diff_not_in. intros z H2. apply (H1 xs).
                { assumption. }
                { left. reflexivity. }}
          rewrite H2. reflexivity.
        + intros zs y H2 H3. apply H1.         
            { assumption. }
            { right. assumption. }
Qed.


Lemma diff_append : forall (v:Type) (e:Eq v) (xs ys:list v),
    xs ++ ys == xs ++ (ys \\ xs).
Proof.
    intros v e. induction xs as [|x xs IH]; intros ys; simpl.
    - rewrite diff_nil. apply equivRefl.
    - apply equivTrans with (cons x (xs ++ (ys \\ xs))).
        + apply equivConsCompat, IH.
        + split; intros z H1. 
            { destruct (eqDec x z) as [H2|H2].
                { subst. left. reflexivity. }
                { destruct H1 as [H1|H1].
                    { apply H2 in H1. contradiction. }
                    { apply in_app_or in H1. destruct H1 as [H1|H1];
                      right; apply in_or_app.
                        { left. assumption. }
                        { right. apply diff_charac in H1. destruct H1 as [H1 H3].
                          apply diff_charac. split.
                            { assumption. }
                            { intros [H4|H4].
                                { apply H2 in H4. contradiction. }
                                { apply H3 in H4. contradiction. }}}}}}
            { destruct H1 as [H1|H1].
                { subst. left. reflexivity. }
                { right. apply in_or_app. 
                  apply in_app_or in H1. destruct H1 as [H1|H1].
                    { left. assumption. }
                    { apply diff_charac in H1. destruct H1 as [H1 H2]. right.
                      apply diff_charac. split.
                        { assumption. }
                        { intros H3. apply H2. right. assumption. }}}}
Qed.

