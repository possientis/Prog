Require Import Lt.
Require Import Le.
Require Import Peano_dec.

(* Definition works for 'strict-like' relations                                 *)
Inductive Accessible (a:Type)(r:a -> a -> Prop) : a -> Prop := 
| Acc : forall (x:a), (forall (y:a), r y x -> Accessible a r y) -> 
    Accessible a r x
.

Arguments Accessible {a}.

Definition WellFounded (a:Type) (r:a -> a -> Prop) :=
    forall (x:a), Accessible r x.

Arguments WellFounded {a}.

Lemma lt_is_acc : forall (a:Type) (r:a -> a -> Prop) (x y:a),
    r x y -> Accessible r y  -> Accessible r x.
Proof.
    intros a r x y R Ay. destruct Ay as [y H].
    apply H. assumption.
Qed.

Lemma nat_is_acc : forall (n:nat), Accessible lt n.
Proof.
    induction n as [|n IH]; constructor.
    - intros n H. inversion H.
    - intros m H. destruct (eq_nat_dec m n) as [H'|H'].
        + subst. assumption.
        + unfold lt in H. apply le_S_n in H. 
          apply le_lt_or_eq in H. destruct H as [H|H].
            { apply lt_is_acc with n; assumption. }
            { apply H' in H. contradiction. }
Qed.

Lemma lt_is_wf : WellFounded lt.
Proof.
    unfold WellFounded. intros n. apply nat_is_acc.
Qed.

Definition Reflexive (a:Type) (r:a -> a -> Prop) : Prop :=
    forall (x:a), r x x.

Definition AntiSym (a:Type) (r:a -> a -> Prop) : Prop := 
    forall (x y:a), r x y -> r y x -> x = y.

Definition Transitive (a:Type) (r:a -> a -> Prop) : Prop :=
    forall (x y z:a), r x y -> r y z -> r x z.

Definition Total (a:Type) (r:a -> a -> Prop) : Prop :=
    forall (x y:a), r x y \/ r y x.

Arguments Reflexive {a}.
Arguments AntiSym {a}.
Arguments Transitive {a}.
Arguments Total {a}.

Definition TotalOrder (a:Type) (r:a -> a -> Prop) : Prop :=
    Reflexive r /\ AntiSym r /\ Transitive r /\ Total r.

Arguments TotalOrder {a}.

Definition Minimal (a:Type) (r:a -> a -> Prop) (x:a) : Prop :=
    forall (y:a), r y x -> x = y.

Arguments Minimal {a}.

(* There is an injection j:b -> a, i.e. b is a subset of a                      *)
Inductive Embedding (b a:Type) : Type :=
| Embed : forall (j:b -> a), (forall (x y:b), j x = j y -> x = y) -> Embedding b a
.

Arguments Embed {b} {a}.

(* Restricting relation r on a to subset b                                      *)
Definition restrict (a b:Type) (r:a -> a -> Prop) (e:Embedding b a)(x y:b) 
    : Prop :=
        match e with
        | Embed j _ => r (j x) (j y)
        end.

Arguments restrict {a} {b}.

(* Every non-empty subset has a minimal element                                 *)
Definition HasMinProp (a:Type) (r:a -> a -> Prop) : Prop :=
    forall (b:Type) (e:Embedding b a), forall (y:b), exists (z:b), 
    Minimal (restrict r e) z.

Arguments HasMinProp {a}.

Definition WellOrder (a:Type) (r:a -> a -> Prop) : Prop :=
    TotalOrder r /\ HasMinProp r.

Arguments WellOrder {a}.

(* returns a 'strict' counterpart of a given relation                           *)
Definition strict (a:Type) (r:a -> a -> Prop) (x y:a) : Prop :=
    r x y /\ x <> y.

Arguments strict {a}.

Lemma LeReflexive : Reflexive le.
Proof.
    unfold Reflexive. apply le_refl.
Qed.

Lemma LeAntiSym : AntiSym le.
Proof.
    unfold AntiSym. apply le_antisym.
Qed.

Lemma LeTransitive : Transitive le.
Proof.
    unfold Transitive. apply le_trans.
Qed.

Lemma LeTotal : Total le.
Proof.
    unfold Total. intros n m.
    destruct (eq_nat_dec n m) as [H|H].
    - subst. left. apply le_n.
    - apply nat_total_order in H. destruct H as [H|H].
        + left. apply le_trans with (S n).
            { apply le_S, le_n. }
            { assumption. }
        + right. apply le_trans with (S m).
            { apply le_S, le_n. }
            { assumption. }
Qed.


Lemma LeTotalOrder : TotalOrder le.
Proof.
    unfold TotalOrder. split.
    - apply LeReflexive.
    - split.
        + apply LeAntiSym.
        + split.
            { apply LeTransitive. }
            { apply LeTotal. }
Qed.

Theorem WellOrderWF : forall (a:Type) (r:a -> a -> Prop),
    WellOrder r -> WellFounded (strict r).
Proof.
Admitted. (* TODO *)


Lemma LeHasMinProp : HasMinProp le.
Proof.
    unfold HasMinProp. intros b e y. destruct e as [j p].
    unfold Minimal. unfold restrict.
Show.
