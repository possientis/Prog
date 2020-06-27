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
Theorem replacememtLEM : forall (p:set -> set -> Prop),
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
    -
Show.
