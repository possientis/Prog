Require Import Func.

Definition lem (p:Prop) : Prop := p \/ ~p.

Definition ifRel (a b:Type) (p:Prop) (f g:a ==> b) (x:a) (y:b) : Prop :=
    (p /\ rel f x y) \/ (~p /\ rel g x y).

Arguments ifRel {a} {b} _ _ _ _ _.


Lemma ifRelFunctional : forall (a b:Type) (p:Prop) (f g:a ==> b),
    Functional (ifRel p f g).
Proof.
    unfold Functional. intros a b p [fr fTot fFunc] [gr gTot gFunc] x y y'. 
    unfold ifRel. simpl. intros [[Hp H1]|[Hp H1]] [[Hq H2]|[Hq H2]].
    - unfold Functional in fFunc. apply (fFunc x).
        + exact H1.
        + exact H2.
    - exfalso. apply Hq. exact Hp.
    - exfalso. apply Hp. exact Hq.
    - unfold Functional in gFunc. apply (gFunc x).
        + exact H1.
        + exact H2.
Qed.


Arguments ifRelFunctional {a} {b} _ _ _ _ _ _ _ _.


Lemma ifRelTotal : forall (a b:Type) (p:Prop) (f g:a ==> b),
    lem p -> Total (ifRel p f g).
Proof.
    unfold Total, ifRel. intros a b p [fr fTot fFunc] [gr gTot gFunc] [H|H] x.
    - simpl. unfold Total in fTot. destruct (fTot x) as [y Hy].
        exists y. left. split.
            + exact H.
            + exact Hy.
    - simpl. unfold Total in fTot. destruct (gTot x) as [y Hy].
        exists y. right. split.
            + exact H.
            + exact Hy.
Qed.

Arguments ifRelTotal {a} {b} _ _ _ _ _.


(* not that useful but good to know. Only applies if type a is not empty*)
Lemma ifRelTotal_converse : forall (a b:Type) (p:Prop) (f g:a ==> b),
    (exists (x:a), True) -> Total (ifRel p f g) -> lem p.
Proof.
    unfold Total, ifRel, lem. intros a b p f g [x _] H.
    destruct (H x) as [y [[Hp H']|[Hp H']]].
    - left.  exact Hp.
    - right. exact Hp.
Qed.


Definition ifFunc (a b:Type) (p:Prop) (q: lem p) (f g:a ==> b) : a ==> b :=
    func (ifRel p f g) (ifRelTotal p f g q) (ifRelFunctional p f g). 

Arguments ifFunc {a} {b} _ _ _ _.

Lemma ifFunc_correct_true : forall (a b:Type) (p:Prop) (q:lem p) (f g:a ==> b),
    forall (x:a) (y:b), p -> (rel (ifFunc p q f g) x y <-> rel f x y).
Proof.
    intros a b p q f g x y H. unfold ifFunc. simpl. unfold ifRel.
    remember (rel f) as r. split.
    - intros [[Hp H']|[Hp H']].
        + exact H'.
        + exfalso. apply Hp. exact H.
    - intros H'. left. split.
        + exact H.
        + exact H'.
Qed.

Lemma ifFunc_correct_false : forall (a b:Type) (p:Prop) (q:lem p) (f g:a ==> b),
    forall (x:a) (y:b), ~p -> (rel (ifFunc p q f g) x y <-> rel g x y).
Proof.
    intros a b p q f g x y H. unfold ifFunc. simpl. unfold ifRel.
    remember (rel g) as r. split.
    - intros [[Hp H']|[Hp H']].
        + exfalso.  apply H. exact Hp.
        + exact H'.
    - intros H'. right. split.
        +  exact H.
        +  exact H'.
Qed.


