Require Import List.

Require Import In.
Require Import Eq.
Require Import Nil.
Require Import Equiv.
Require Import Include.
Require Import Append.

Fixpoint inter (v:Type) (e:Eq v) (xs ys:list v) : list v :=
    match xs with
    | nil        => nil
    | cons x xs => 
        match in_dec eqDec x ys with
        | left  _   => cons x (inter v e xs ys)
        | right _   => inter v e xs ys
        end
    end.

Arguments inter {v} {e}.

Notation "xs /\ ys" := (inter xs ys)
    (at level 80, right associativity) : Intersect_scope.

Open Scope Intersect_scope.

Lemma inter_charac : forall (v:Type) (e:Eq v) (xs ys:list v) (z:v),
    z :: (xs /\ ys) <-> z :: xs /\ z :: ys.
Proof.
    intros v e xs ys z. split.
    - induction xs as [|x xs IH]; intros H.
        + inversion H.
        + destruct (in_dec eqDec x ys) as [H'|H'] eqn:E; 
          simpl in H; rewrite E in H.
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
            { apply IH in H. destruct H as [H1 H2]. split.
                { right. assumption. }
                { assumption. }
            }
   - induction xs as [|x xs IH]; intros [H1 H2].
        + inversion H1.
        + destruct (in_dec eqDec x ys) as [H|H] eqn:E; simpl; rewrite E.
            { destruct H1 as [H1|H1].
                { subst. left. reflexivity. }
                { right. apply IH. split; assumption. }
            }
            { destruct H1 as [H1|H1]. 
                { subst. exfalso. apply H. assumption. }
                { apply IH. split; assumption. }
            } 
Qed.

(* left-distributivity is false: xs = [0], ys = [1], zs = [1,0], then           *)
(* zs /\ xs = [0]                                                               *)
(* zs /\ ys = [1]                                                               *)
(* so (zs /\ xs) ++ (zs /\ ys) = [0,1] where zs /\ (xs ++ ys) = [1,0]           *)
Lemma inter_distrib_app_r : forall (v:Type) (e:Eq v) (xs ys zs:list v),
    ((xs ++ ys) /\ zs) = (xs /\ zs) ++ (ys /\ zs).
Proof.
    intros v e. induction xs as [|x xs IH]; intros ys zs.
    - reflexivity.
    - rewrite <- app_comm_cons. simpl. destruct (in_dec eqDec x zs) as [H|H].
        + rewrite <- app_comm_cons. rewrite IH. reflexivity.
        + apply IH.
Qed.

Lemma inter_cons_not_in_r : forall (v:Type) (e:Eq v) (xs ys:list v) (y:v),
    ~ y :: xs -> (xs /\ (cons y ys)) = (xs /\ ys).
Proof.
    intros v e. induction xs as [|x xs IH]; intros ys y H.
    - reflexivity.
    - simpl. destruct (eqDec y x) as [H1|H1].
        + subst. exfalso. apply H. left. reflexivity.
        + destruct (in_dec eqDec x ys) as [H2|H2].
            { rewrite IH.
                { reflexivity. }
                { intros H3. apply H. right. assumption. }}
            { apply IH.  intros H3. apply H. right. assumption. }
Qed.

Lemma inter_cons_not_in_l : forall (v:Type) (e:Eq v) (xs ys:list v) (x:v),
    ~ x :: ys -> ((cons x xs) /\ ys) = (xs /\ ys).
Proof.
    intros v e. induction xs as [|x xs IH]; intros ys y H;
    simpl; destruct (in_dec eqDec y ys) as [H1|H1].
    - apply H in H1. contradiction.
    - reflexivity.
    - apply H in H1. contradiction.
    - reflexivity.
Qed.

Lemma inter_cons_in_r : forall (v:Type) (e:Eq v) (xs ys:list v) (y:v),
    y :: ys -> (xs /\ (cons y ys)) = (xs /\ ys).
Proof.
    intros v e. induction xs as [|x xs IH]; intros ys y H.
    - reflexivity.
    - simpl. destruct (eqDec y x) as [H1|H1].
        + subst. destruct (in_dec eqDec x ys) as [H2|H2].
            { rewrite IH.
                { reflexivity. }
                { assumption. }}
            { apply H2 in H. contradiction. }
        + destruct (in_dec eqDec x ys) as [H2|H2]; rewrite IH.
            { reflexivity. }
            { assumption. }
            { reflexivity. }
            { assumption. }
Qed.

Lemma inter_nil : forall (v:Type) (e:Eq v) (xs:list v),
    (xs /\ nil) = nil.
Proof.
    intros v e. induction xs as [|x xs IH].
    - reflexivity.
    - simpl. apply IH.
Qed.

Lemma inter_comm : forall (v:Type) (e:Eq v) (xs ys:list v),
    (xs /\ ys) == (ys /\ xs).
Proof.
   intros v e xs ys. split; intros z H; apply inter_charac in H; 
    destruct H as [H1 H2]; apply inter_charac; split; assumption.
Qed.

Lemma inter_assoc : forall (v:Type) (e:Eq v) (xs ys zs:list v),
    ((xs /\ ys) /\ zs) == (xs /\ (ys /\ zs)).
Proof.
    intros v e xs ys zs. split; intros z H; apply inter_charac in H;
    destruct H as [H1 H3].
    - apply inter_charac in H1. destruct H1 as [H1 H2].
      apply inter_charac. split.
        + assumption.
        + apply inter_charac. split; assumption.
    - apply inter_charac in H3. destruct H3 as [H2 H3].
      apply inter_charac. split.
        + apply inter_charac. split; assumption.
        + assumption.
Qed.

Lemma inter_compat_l : forall (v:Type) (e:Eq v) (xs ys zs:list v),
    xs == ys -> (xs /\ zs) == (ys /\ zs).
Proof.
    intros v e xs ys zs [H1 H2]. split; intros z H;
    apply inter_charac in H; destruct H as [H3 H4];
    apply inter_charac; split.
    - apply H1. assumption.
    - assumption.
    - apply H2. assumption.
    - assumption.
Qed.

Lemma inter_compat_r : forall (v:Type) (e:Eq v) (xs ys zs:list v),
    xs == ys -> (zs /\ xs) == (zs /\ ys).
Proof.
    intros v e xs ys zs [H1 H2]. split; intros z H;
    apply inter_charac in H; destruct H as [H3 H4];
    apply inter_charac; split.
    - assumption.
    - apply H1. assumption.
    - assumption.
    - apply H2. assumption.
Qed.

Lemma inter_compat_lr : forall (v:Type) (e:Eq v) (xs xs' ys ys':list v),
    xs == xs' -> ys == ys' -> (xs /\ ys) == (xs' /\ ys').
Proof.
   intros v e xs xs' ys ys' H1 H2. 
   apply equivTrans with (xs' /\ ys).  
   - apply inter_compat_l. assumption.
   - apply inter_compat_r. assumption.
Qed.

Lemma inter_sub : forall (v:Type) (e:Eq v) (xs ys:list v),
    xs <= ys -> (xs /\ ys) == xs.
Proof.
    intros v e xs ys H1. split; intros z H2.
    - apply inter_charac in H2. destruct H2 as [H2 H3]. assumption.
    - apply inter_charac. split.
        + assumption.
        + apply H1. assumption.
Qed.

(* Stronger result, useful for rewrite.                                         *)
Lemma inter_sub' : forall (v:Type) (e:Eq v) (xs ys:list v),
    xs <= ys -> (xs /\ ys) = xs.
Proof.
    intros v e. induction xs as [|x xs IH]; intros ys H.
    - reflexivity.
    - simpl. destruct (in_dec eqDec x ys) as [H1|H1].
        + rewrite IH.
            { reflexivity. }
            { intros z H2. apply H. right. assumption. }
        + exfalso. apply H1, H. left. reflexivity.
Qed.

Lemma inter_sub_equiv : forall (v:Type) (e:Eq v) (xs ys zs zs':list v),
    zs' <= zs -> 
    (zs /\ xs)  == (zs /\ ys) -> 
    (zs' /\ xs) == (zs' /\ ys).
Proof.
    intros v e xs ys zs zs' H1 H2.
    apply equivTrans with ((zs' /\ zs) /\ xs).
    - apply inter_compat_l. apply equivSym. apply inter_sub. assumption.
    - apply equivTrans with ((zs' /\ zs) /\ ys).
        + apply equivTrans with (zs' /\ (zs /\ xs)).
            { apply inter_assoc. }
            { apply equivTrans with (zs' /\ (zs /\ ys)).
                { apply inter_compat_r. assumption. }
                { apply equivSym. apply inter_assoc. }}
        + apply inter_compat_l. apply inter_sub. assumption.
Qed.


Lemma inter_distrib_app_l : forall (v:Type) (e:Eq v) (xs ys zs:list v),
    (zs /\ (xs ++ ys)) == (zs /\ xs) ++ (zs /\ ys).
Proof.
    intros v e xs ys zs. apply equivTrans with ((xs ++ ys) /\ zs). 
    - apply inter_comm.
    - rewrite inter_distrib_app_r. apply app_compat_lr; apply inter_comm.
Qed.


Lemma inter_app_nil_l : forall (v:Type) (e:Eq v) (xs ys zs:list v),
    (zs /\ (xs ++ ys)) = nil -> (zs /\ xs) = nil /\ (zs /\ ys) = nil.
Proof.
    intros v e xs ys zs H1. apply equivNilIsNil in H1.
    assert ((zs /\ xs) ++ (zs /\ ys) == nil) as H2.
        { apply (equivCompatLR v (zs /\ (xs ++ ys)) nil).
            { apply equivSym, inter_distrib_app_l. }
            { apply equivRefl. }
            { assumption. }}
    apply equivNilIsNil in H2. apply app_nil in H2. destruct H2 as [H2 H3].
    split; assumption.
Qed.


Lemma inter_sub_nil_l : forall (v:Type) (e:Eq v) (xs ys zs:list v),
    xs <= ys -> (ys /\ zs) = nil -> (xs /\ zs) = nil.
Proof.
   intros v e xs ys zs H1 H2. apply nil_charac. intros x. 
   rewrite inter_charac. intros [H3 H4]. rewrite nil_charac in H2.
   apply (H2 x). apply inter_charac. split.
   - apply H1. assumption.
   - assumption.
Qed.

