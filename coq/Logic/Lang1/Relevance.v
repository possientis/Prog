Require Import List.

Require Import Logic.Nat.Eq.
Require Import Logic.Class.Eq.
Require Import Logic.List.Remove.

Require Import Logic.Fol.Free.

Require Import Logic.Set.Set.
Require Import Logic.Set.Equal.

Require Import Logic.Lang1.Syntax.
Require Import Logic.Lang1.Semantics.
Require Import Logic.Lang1.Environment.

Definition envEqualOn (p:Formula) (e e':Env) : Prop :=
    forall (n:nat), In n (Fr p) -> e n == e' n.

Lemma relevance : forall (e e':Env) (p:Formula), 
    envEqualOn p e e' -> eval e p <-> eval e' p.
Proof.
    intros e e' p. unfold envEqualOn. revert e e'.
    induction p as [|n m|p1 IH1 p2 IH2|n p1 IH1]; intros e e' H; simpl.
    - tauto.
    - split. 
        + apply elemCompatLR; apply H.
            { left. reflexivity. }
            { right. left. reflexivity. }
        + apply elemCompatLR; apply equalSym; apply H.
            { left. reflexivity. }
            { right. left. reflexivity. }
    - rewrite (IH1 e e'), (IH2 e e').
        + tauto.
        + intros n H'. apply H. simpl. apply in_or_app. right. assumption.
        + intros n H'. apply H. simpl. apply in_or_app. left.  assumption.
    - split; intros H' x.
        + rewrite (IH1 (bind e' n x) (bind e n x)). 
            { apply H'. }
            { intros m.  destruct (eqDec n m) as [E|E].
                { subst. rewrite bindSame, bindSame. intros. apply equalRefl. }
                { rewrite bindDiff, bindDiff.
                    { intros H''. apply equalSym. apply H. simpl. 
                      apply remove_still; assumption. }
                    { assumption. }
                    { assumption. }}}
        + rewrite (IH1 (bind e n x) (bind e' n x)). 
            { apply H'. }
            { intros m H''. destruct (eqDec n m) as [E|E].
                { subst. rewrite bindSame, bindSame. apply equalRefl. }
                { rewrite bindDiff, bindDiff.
                    { apply H. simpl. apply remove_still; assumption. }
                    { assumption. }
                    { assumption. }}}
Qed.

Lemma evalEnvEqual : forall (e e':Env) (p:Formula),
    envEqual e e' -> eval e p <-> eval e' p.
Proof.
    intros e e' p H. apply relevance. intros n H'. apply H.
Qed.

Lemma evalNotInFree : forall (e:Env) (n:nat) (x:set) (p:Formula),
    ~In n (Fr p) -> eval (bind e n x) p <-> eval e p.
Proof.
    intros e n x p H. apply relevance. intros m H'. 
    destruct (eqDec n m) as [E|E].
    - subst. apply H in H'. contradiction.
    - rewrite bindDiff. 
        + apply equalRefl.
        + assumption.
Qed.
