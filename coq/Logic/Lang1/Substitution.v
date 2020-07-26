Require Import List.

Require Import Logic.Nat.Eq.
Require Import Logic.Class.Eq.
Require Import Logic.List.Remove.
Require Import Logic.Func.Composition.

Require Import Logic.Set.Set.
Require Import Logic.Set.Equal.

Require Import Logic.Lang1.Valid.
Require Import Logic.Lang1.Syntax.
Require Import Logic.Lang1.Semantics.
Require Import Logic.Lang1.Relevance.
Require Import Logic.Lang1.Environment.

Local Lemma rewrite_ : forall (p p' q:set -> Prop),
    (forall x, p x <-> p' x) -> 
    ((forall x, p x) <-> (forall x, q x) ) ->
    ((forall x, p' x) <-> (forall x, q x)).
Proof.
    intros p p' q H1 [H2 H3]. split; intros H4.
    - apply H2. intros x. rewrite (H1 x). apply H4.
    - intros x. rewrite <- (H1 x). apply H3. assumption.
Qed.

(* Substitution lemma: provided a variable substitution is valid for a formula  *)
(* p, i.e. does not give rise to variable capture, semantics is preserved.      *)
Lemma Substitution : forall (e:Env) (f:nat -> nat) (p:Formula), Valid f p -> 
    eval e (fmap f p) <-> eval (e ; f) p.
Proof.
    intros e f p. revert p f e. induction p as [|n m|p1 IH1 p2 IH2|n p1 IH1];
    intros f e V.
    - simpl. split; auto.
    - simpl. split; auto.
    - simpl.  apply ValidImp in V. destruct V as [V1 V2].
      rewrite IH1, IH2.
        + split; auto.
        + assumption.
        + assumption.
    - simpl. apply ValidAll in V. destruct V as [V1 V2].
      apply rewrite_ with (fun x => eval ((bind e (f n) x) ; f) p1).
        + intros x. rewrite IH1.
            { split; auto. }
            { assumption. }
        + apply rewrite_ with (fun x => eval (bind (e;f) n x) p1).
            { intros x. apply relevance. intros m H1. 
              unfold bind, comp. destruct (eqDec n m) as [H2|H2].
                { subst. destruct (eqDec (f m) (f m)) as [H3|H3].
                    { apply equalRefl. }
                    { exfalso. apply H3. reflexivity. }}
                { destruct (eqDec (f n) (f m)) as [H3|H3].
                    { exfalso. apply (V2 m). 
                        { simpl. apply remove_still; assumption. }
                        { assumption. }}
                    { apply equalRefl. }}}
            { split; auto. }
Qed.



