Require Import List.

Require Import In.
Require Import Eq.
Require Import Equiv.
Require Import Include.

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


