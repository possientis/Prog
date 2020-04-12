Require Import List.

Definition Equiv (a:Type) (xs ys:list a) : Prop :=
    incl xs ys /\ incl ys xs.

Arguments Equiv {a}.

Lemma EquivRefl : forall (a:Type) (xs:list a), Equiv xs xs.
Proof. intros a xs. split; apply incl_refl. Qed.

Lemma EquivSym : forall (a:Type) (xs ys:list a), Equiv xs ys -> Equiv ys xs.
Proof. intros a xs ys [H1 H2]. split; assumption. Qed.

Lemma EquivTrans : forall (a:Type) (xs ys zs:list a), 
    Equiv xs ys -> Equiv ys zs -> Equiv xs zs.
Proof.
    intros a xs ys zs [H1 H2] [H3 H4]. 
    split; apply incl_tran with ys; assumption.
Qed.

