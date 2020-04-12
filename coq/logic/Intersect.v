Require Import List.

Require Import In.
Require Import Eq.

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

Lemma inter_cons_r : forall (v:Type) (e:Eq v) (xs ys:list v) (y:v),
    ~In y xs -> (xs /\ (cons y ys)) = (xs /\ ys).
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


Lemma inter_cons_l : forall (v:Type) (e:Eq v) (xs ys:list v) (x:v),
    ~In x ys -> ((cons x xs) /\ ys) = (xs /\ ys).
Proof.
    intros v e. induction xs as [|x xs IH]; intros ys y H;
    simpl; destruct (in_dec eqDec y ys) as [H1|H1].
    - apply H in H1. contradiction.
    - reflexivity.
    - apply H in H1. contradiction.
    - reflexivity.
Qed.


