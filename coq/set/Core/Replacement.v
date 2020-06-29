Require Import List.

Require Import Utils.LEM.
Require Import Utils.Filter.

Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.ToList.
Require Import Core.Functional.
Require Import Core.Compatible.
Require Import Core.Extensionality.

Require Import Normal.Normal.

(* Axiom schema of replacement assuming LEM for our Coq meta-logic.             *)
Theorem replacementLEM : forall (p:set -> set -> Prop),
    LEM ->
    compatible2 p ->
    functional p  -> 
    forall (x:set),
        exists (y:set), forall (z:set),
            z :: y <-> exists (u:set), u :: x /\ p u z.
Proof.
    intros p L C F x. 
    remember (toList x) as xs eqn:H1.
    remember (fun x y => p x y /\ Normal y) as q eqn:Q.
    assert (forall (x:set) (y y':set), q x y -> q x y' -> y = y') as H2.
    { rewrite Q. intros u y y' [H3 H4] [H5 H6]. apply normalEqualSame.
        { assumption. }
        { assumption. }
        { apply (F u); assumption. } }
    assert (exists (ys:list set), forall (y:set), 
        In y ys <-> exists (u:set), In u xs /\ q u y) as H3.
    { apply filterReplace; assumption. }
    destruct H3 as [ys H3]. exists (fromList ys). intros z. split; intros H4.
    - rewrite toListElem, toListFromList in H4. destruct H4 as [z' [H4 [H5 H6]]].
      apply H3 in H4. rewrite Q in H4. destruct H4 as [u [H7 [H8 H9]]].    
      exists u. split.
        + apply toListElem. exists u. split.
            { rewrite <- H1. assumption. }
            { split; apply inclRefl. }
        + apply (C u u z' z).
            { apply equalRefl. }
            { apply doubleIncl. split; assumption. }
            { assumption. }
    - apply toListElem. rewrite toListFromList. remember (normal z) as z' eqn:Z.
      exists z'. destruct H4 as [u [H4 H5]]. apply toListElem in H4. 
      destruct H4 as [u' [H4 [H6 H7]]]. split.
        + apply H3. exists u'. split.
            { rewrite H1. assumption. }
            { rewrite Q. split.
                { apply (C u u' z z').
                    { apply doubleIncl. split; assumption. }
                    { rewrite Z. apply equalSym, normalEqual. }
                    { assumption. }}
                { rewrite Z. apply normalNormal. }}
        + apply doubleIncl. rewrite Z. apply equalSym, normalEqual. 
Qed.

(* Again, this is simply to demonstrate explicit dependency in x in not needed. *)
Corollary replacementLEM_ : forall (p:set -> set -> set -> Prop),
    LEM ->
    compatible3 p ->
    forall (x:set),
    functional (p x)  -> 
        exists (y:set), forall (z:set),
            z :: y <-> exists (u:set), u :: x /\ p x u z.
Proof.
    intros p L C x F. apply replacementLEM. 
    - assumption.
    - apply Comp3Comp2. assumption.
    - assumption.
Qed.


(* A proof of the axiom schema of specification based on replacement.           *)
Theorem specificationLEM : forall (p:set -> Prop), 
    LEM ->
    compatible p -> 
    forall (x:set), exists (y:set), forall (z:set), 
        z :: y <-> z :: x /\ p z.
Proof.
    intros p L C. remember (fun x y => p x /\ (x == y)) as q eqn:Q.
    assert (compatible2 q) as Cq.
        { unfold compatible2. rewrite Q. intros x x' y y' H1 H2 [H3 H4]. split.
            { apply (C x x'); assumption. }
            { apply equalTrans with x.
                { apply equalSym. assumption. }
                { apply equalTrans with y; assumption. }}}
    assert (functional q) as Fq.
        { unfold functional. rewrite Q. intros x y y' [H1 H2] [H3 H4].
          apply equalTrans with x.
            { apply equalSym. assumption. }
            { assumption. }}
    intros x. remember (replacementLEM q L Cq Fq x) as R eqn:E. clear E. 
    destruct R as [y R]. exists y. intros z. destruct (R z) as [H1 H2]. 
    rewrite Q in H1. split; intros H.
    -  apply H1 in H. clear H1 H2.
      destruct H as [u [H1 [H2 H3]]]. split.
        + apply elemCompatL with u; assumption.
        + apply (C u z); assumption.
    - apply H2. exists z. destruct H as [H3 H4]. split.
        + assumption.
        + rewrite Q. split.
            { assumption. }
            { apply equalRefl. }
Qed.
