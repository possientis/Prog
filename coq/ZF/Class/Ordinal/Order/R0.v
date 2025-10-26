Require Import ZF.Class.Incl.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Order.Le.
Require Import ZF.Class.Prod.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Max.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Union2.

Module CEM := ZF.Class.Empty.
Module COC := ZF.Class.Ordinal.Core.
Module SOC := ZF.Set.Ordinal.Core.

(* Class to be used as order on On x On.                                        *)
Definition R0 : Class := fun x =>
  exists a b c d, x = :( :(a,b): , :(c,d): ):                 /\
    (a :\/: b :< c :\/: d                                     \/
    (a :\/: b  = c :\/: d /\ Le :( :(a,b): , :(c,d): ): )).

Proposition Charac2 : forall (x y:U),
  R0 :(x,y): <->
  exists a b c d,
    x = :(a,b):           /\
    y = :(c,d):           /\
   (a :\/: b :< c :\/: d  \/
   (a :\/: b  = c :\/: d  /\ Le :( :(a,b): , :(c,d): ): )).
Proof.
  intros x y. split; intros H1.
  - destruct H1 as [a [b [c [d [H1 H2]]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H3].
    exists a. exists b. exists c. exists d. split. 1: assumption.
    split; assumption.
  - destruct H1 as [a [b [c [d [H1 [H2 H3]]]]]].
    exists a. exists b. exists c. exists d. subst.
    split. 2: assumption. reflexivity.
Qed.

Proposition Charac4 : forall (a b c d:U),
  R0 :( :(a,b): , :(c,d): ): <->
  a :\/: b :< c :\/: d        \/
 (a :\/: b  = c :\/: d        /\ Le :( :(a,b): , :(c,d): ): ).
Proof.
  intros a b c d. split; intros H1.
  - apply Charac2 in H1. destruct H1 as [a' [b' [c' [d' [H1 [H2 H3]]]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H4].
    apply OrdPair.WhenEqual in H2. destruct H2 as [H2 H5].
    subst. assumption.
  - apply Charac2. exists a. exists b. exists c. exists d.
    split. 1: reflexivity. split. 1: reflexivity. assumption.
Qed.

(* A non-empty subclass of On x On has an R0-minimal element.                   *)
Proposition HasMinimal : forall (A:Class),
  A :<=: On :x: On          ->
  A :<>: :0:                ->

  exists a b,
    On a                    /\
    On b                    /\
    Minimal R0 A :(a,b):.
Proof.
  intros A H1 H2.
  remember (fun c => exists a b, c = a :\/: b /\ A :(a,b):) as B eqn:H3.
  assert (B :<=: On) as H4. {
    intros x H4. rewrite H3 in H4. destruct H4 as [a [b [H4 H5]]].
    subst. apply H1 in H5. apply Prod.Charac2 in H5. destruct H5 as [H5 H6].
    apply Max.IsOrdinal; assumption. }
  assert (B :<>: :0:) as H5. {
    apply CEM.HasElem in H2. destruct H2 as [x H2].
    assert ((On :x: On ) x) as H5. { apply H1. assumption. }
    destruct H5 as [a [b [H5 _]]]. subst. apply CEM.HasElem.
    exists (a :\/: b). exists a. exists b. split. 2: assumption. reflexivity. }
  assert (exists c, On c /\ B c /\ forall x, B x -> c :<=: x) as H6. {
    apply SOC.HasMinimal; assumption. }
  destruct H6 as [c [H6 [H7 H8]]].
  remember (fun x =>
    exists a b, x = :(a,b): /\ c = a :\/: b /\ A :(a,b): ) as C eqn:H9.
  assert (C :<=: On :x: On) as H10. {
    intros x H10. rewrite H9 in H10. destruct H10 as [a [b [H10 [_ H11]]]].
    apply H1 in H11. subst. assumption. }
  assert (C :<>: :0:) as H11. {
    rewrite H3 in H7. destruct H7 as [a [b H7]]. apply CEM.HasElem.
    exists :(a,b):. rewrite H9. exists a. exists b. split. 2: assumption.
    reflexivity. }
  assert (exists a b, On a /\ On b /\ Minimal Le C :(a,b):) as H12. {
    apply Le.HasMinimal; assumption. }
  destruct H12 as [a [b [H12 [H13 H14]]]].
  assert (C :(a,b):) as H15. { apply Minimal.IsIn with Le. assumption. }
  assert (c = a :\/: b /\ A :(a,b):) as H16. {
    rewrite H9 in H15. destruct H15 as [a' [b' [H15 H16]]].
    apply OrdPair.WhenEqual in H15. destruct H15 as [H15 H17].
    subst. assumption. }
  destruct H16 as [H16 H17].
  assert (Minimal R0 A :(a,b):)as H18. {
    split. 1: assumption. intros x H18 H19. assert (H20 := H18).
    apply H1 in H20. destruct H20 as [y [z [H20 [H21 H22]]]].
    remember (y :\/: z) as d eqn:H23.
    assert (B d) as H24. {
      rewrite H3. exists y. exists z. split. 1: assumption.
      rewrite <- H20. assumption. }
    apply H8 in H24.
    assert (On c) as H25. { rewrite H16. apply Max.IsOrdinal; assumption. }
    assert (On d) as H26. { rewrite H23. apply Max.IsOrdinal; assumption. }
    apply SOC.InclIsEqualOrElem in H24; try assumption.
    destruct H24 as [H24|H24].
    - rewrite H20 in H19. apply Charac4 in H19. destruct H19 as [H19|H19].
      + apply NoElemLoop1 with c. rewrite <- H24 in H23. rewrite <- H23 in H19.
        rewrite <- H16 in H19. assumption.
      + destruct H19 as [_ H19]. revert H19. apply H14.
        rewrite H9. exists y. exists z. split. 1: reflexivity. split.
        * rewrite <- H23. assumption.
        * rewrite <- H20. assumption.
    - rewrite H20 in H19. apply Charac4 in H19. destruct H19 as [H19|H19].
      + rewrite <- H23 in H19. rewrite <- H16 in H19.
        apply NoElemLoop1 with c. apply SOC.ElemIsIncl in H19; try assumption.
        apply H19. assumption.
      + destruct H19 as [H19 _].
        rewrite <- H23 in H19. rewrite <- H16 in H19. rewrite H19 in H24.
        revert H24. apply NoElemLoop1. }
  exists a. exists b. split. 1: assumption. split; assumption.
Qed.

