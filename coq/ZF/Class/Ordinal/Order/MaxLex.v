Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Founded.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Class.Order.WellOrdering.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Order.Lex.
Require Import ZF.Class.Ordinal.Enum.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.InitSegment.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Max.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageUnderClass.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.Eval.
Require Import ZF.Notation.Image.

Module CEM := ZF.Class.Empty.
Module COC := ZF.Class.Ordinal.Core.
Module COI := ZF.Class.Order.InitSegment.
Module CPR := ZF.Class.Prod.
Module CRB := ZF.Class.Relation.Bij.
Module SIN := ZF.Set.Incl.
Module SOC := ZF.Set.Ordinal.Core.
Module SOI := ZF.Set.Order.InitSegment.
Module SOS := ZF.Set.Ordinal.Succ.
Module SPR := ZF.Set.Prod.

(* Max-lexicographic order on On x On.                                          *)
Definition MaxLex : Class := fun x =>
  exists a b c d, x = :( :(a,b): , :(c,d): ):                 /\
    (a :\/: b :< c :\/: d                                     \/
    (a :\/: b  = c :\/: d /\ Lex :( :(a,b): , :(c,d): ): )).

(* The ordinal pairing associated with MaxLex maps On x On onto On.             *)
(* This is the max-lexicographic form of a Godel pairing function.              *)
Definition Pairing : Class := (Enum MaxLex (On :x: On))^:-1:.

Proposition Charac2 : forall (x y:U),
  MaxLex :(x,y): <->
  exists a b c d,
    x = :(a,b):           /\
    y = :(c,d):           /\
   (a :\/: b :< c :\/: d  \/
   (a :\/: b  = c :\/: d  /\ Lex :( :(a,b): , :(c,d): ): )).
Proof.
  intros x y. split; intros H1.
  - destruct H1 as [a [b [c [d [H1 H2]]]]].
    apply OrdPair.Equal in H1. destruct H1 as [H1 H3].
    exists a. exists b. exists c. exists d. split. 1: assumption.
    split; assumption.
  - destruct H1 as [a [b [c [d [H1 [H2 H3]]]]]].
    exists a. exists b. exists c. exists d. subst.
    split. 2: assumption. reflexivity.
Qed.

Proposition Charac4 : forall (a b c d:U),
  MaxLex :( :(a,b): , :(c,d): ): <->
  a :\/: b :< c :\/: d        \/
 (a :\/: b  = c :\/: d        /\ Lex :( :(a,b): , :(c,d): ): ).
Proof.
  intros a b c d. split; intros H1.
  - apply Charac2 in H1. destruct H1 as [a' [b' [c' [d' [H1 [H2 H3]]]]]].
    apply OrdPair.Equal in H1. destruct H1 as [H1 H4].
    apply OrdPair.Equal in H2. destruct H2 as [H2 H5].
    subst. assumption.
  - apply Charac2. exists a. exists b. exists c. exists d.
    split. 1: reflexivity. split. 1: reflexivity. assumption.
Qed.

(* A non-empty subclass of On x On has a MaxLex-minimal element.                *)
Proposition HasMinimal : forall (A:Class),
  A :<=: On :x: On          ->
  A :<>: :0:                ->

  exists a b,
    On a                    /\
    On b                    /\
    Minimal MaxLex A :(a,b):.
Proof.
  intros A H1 H2.
  remember (fun c => exists a b, c = a :\/: b /\ A :(a,b):) as B eqn:H3.
  assert (B :<=: On) as H4. {
    intros x H4. rewrite H3 in H4. destruct H4 as [a [b [H4 H5]]].
    subst. apply H1 in H5. apply CPR.Charac2 in H5. destruct H5 as [H5 H6].
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
  assert (exists a b, On a /\ On b /\ Minimal Lex C :(a,b):) as H12. {
    apply Lex.HasMinimal; assumption. }
  destruct H12 as [a [b [H12 [H13 H14]]]].
  assert (C :(a,b):) as H15. { apply Minimal.IsIn with Lex. assumption. }
  assert (c = a :\/: b /\ A :(a,b):) as H16. {
    rewrite H9 in H15. destruct H15 as [a' [b' [H15 H16]]].
    apply OrdPair.Equal in H15. destruct H15 as [H15 H17].
    subst. assumption. }
  destruct H16 as [H16 H17].
  assert (Minimal MaxLex A :(a,b):)as H18. {
    split. 1: assumption. intros x H18 H19. assert (H20 := H18).
    apply H1 in H20. destruct H20 as [y [z [H20 [H21 H22]]]].
    remember (y :\/: z) as d eqn:H23.
    assert (B d) as H24. {
      rewrite H3. exists y. exists z. split. 1: assumption.
      rewrite <- H20. assumption. }
    apply H8 in H24.
    assert (On c) as H25. { rewrite H16. apply Max.IsOrdinal; assumption. }
    assert (On d) as H26. { rewrite H23. apply Max.IsOrdinal; assumption. }
    apply SOC.EqualOrElem in H24; try assumption.
    destruct H24 as [H24|H24].
    - rewrite H20 in H19. apply Charac4 in H19. destruct H19 as [H19|H19].
      + apply Foundation.NoLoop1 with c. rewrite <- H24 in H23. rewrite <- H23 in H19.
        rewrite <- H16 in H19. assumption.
      + destruct H19 as [_ H19]. revert H19. apply H14.
        rewrite H9. exists y. exists z. split. 1: reflexivity. split.
        * rewrite <- H23. assumption.
        * rewrite <- H20. assumption.
    - rewrite H20 in H19. apply Charac4 in H19. destruct H19 as [H19|H19].
      + rewrite <- H23 in H19. rewrite <- H16 in H19.
        apply Foundation.NoLoop1 with c. apply SOC.ElemIsIncl in H19; try assumption.
        apply H19. assumption.
      + destruct H19 as [H19 _].
        rewrite <- H23 in H19. rewrite <- H16 in H19. rewrite H19 in H24.
        revert H24. apply Foundation.NoLoop1. }
  exists a. exists b. split. 1: assumption. split; assumption.
Qed.

(* MaxLex is founded on On x On.                                                *)
Proposition IsFounded : Founded MaxLex (On :x: On).
Proof.
  intros x H1 H2.
  assert (exists a b, On a /\ On b /\ Minimal MaxLex (toClass x) :(a,b):) as H3. {
    apply HasMinimal. 1: assumption. apply Empty.NotEmptyToClass. assumption. }
  destruct H3 as [a [b [H3 [H4 H5]]]].
  exists :(a,b):. assumption.
Qed.

(* MaxLex is total on On x On.                                                  *)
Proposition IsTotal : Total MaxLex (On :x: On).
Proof.
  intros x y H1 H2.
  destruct H1 as [a [b [H1 [H3 H4]]]]. destruct H2 as [c [d [H2 [H5 H6]]]]. subst.
  assert (On (a :\/: b)) as H7. { apply Max.IsOrdinal; assumption. }
  assert (On (c :\/: d)) as H8. { apply Max.IsOrdinal; assumption. }
  assert (
    a :\/: b  = c :\/: d  \/
    a :\/: b :< c :\/: d  \/
    c :\/: d :< a :\/: b) as H9. { apply SOC.IsTotal; assumption. }
  destruct H9 as [H9|[H9|H9]].
  - assert (
    :(a,b): = :(c,d):       \/
    Lex :(:(a,b):,:(c,d):): \/
    Lex :(:(c,d):,:(a,b):):) as H10. {
    apply Lex.IsTotal; apply CPR.Charac2; split; assumption. }
    destruct H10 as [H10|[H10|H10]].
    + left. assumption.
    + right. left.  apply Charac4. right. split; assumption.
    + right. right. apply Charac4. right. split. 2: assumption.
      symmetry. assumption.
  - right. left.  apply Charac4. left. assumption.
  - right. right. apply Charac4. left. assumption.
Qed.

(* MaxLex is a well-ordering on On x On.                                        *)
Proposition IsWellOrdering : WellOrdering MaxLex (On :x: On).
Proof.
  split.
  - apply IsFounded.
  - apply IsTotal.
Qed.

(* The MaxLex predecessors of a pair lie in the next square above its maximum.  *)
Proposition InitSquareIncl : forall (a b c:U),
  On a                                                              ->
  On b                                                              ->
  c = succ (a :\/: b)                                               ->
  COI.initSegment MaxLex (On :x: On) :(a,b): :<=: toClass (c :x: c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c H1 H2 H3. subst c.
  (* The maximum of two ordinals and its successor are ordinals.                *)
  assert (On (a :\/: b)) as H3. { apply Max.IsOrdinal; assumption. }
  assert (On (succ (a :\/: b))) as H4. { apply Succ.IsOrdinal. assumption. }
  intros x H5. apply COI.Charac in H5.
  destruct H5 as [[y [z [H5 [H6 H7]]]] H8]. subst.
  (* A predecessor in MaxLex has maximum at most that of the target pair.       *)
  apply Charac4 in H8. apply SPR.Charac2.
  assert (y :\/: z :<=: a :\/: b) as H9. {
    destruct H8 as [H8|[H8 _]].
    - apply SOC.ElemIsIncl; assumption.
    - rewrite H8. apply SIN.Refl. }
  (* Hence each coordinate is below the successor of that maximum.              *)
  assert (y :<=: a :\/: b) as H10. {
    apply SIN.Tran with (y :\/: z). 2: assumption. apply Union2.IsInclL. }
  assert (z :<=: a :\/: b) as H11. {
    apply SIN.Tran with (y :\/: z). 2: assumption. apply Union2.IsInclR. }
  split; apply SOC.InclElemTran with (a :\/: b); try assumption;
  apply Succ.IsIn.
Qed.


(* MaxLex is well-founded on On x On.                                           *)
Proposition IsWellFounded : WellFounded MaxLex (On :x: On).
Proof.
  split. 1: apply IsFounded. intros x H1.
  destruct H1 as [a [b [H1 [H2 H3]]]]. subst.
  remember (succ (a :\/: b)) as c eqn:H4.
  assert (COI.initSegment MaxLex (On :x: On) :(a,b): :<=:
    toClass (c :x: c)) as H5. {
    apply InitSquareIncl; assumption. }
  apply Small.InclCompat with (toClass (c :x: c)). 1: assumption.
  apply Small.SetIsSmall.
Qed.

(* MaxLex is a well-founded well-ordering on On x On.                           *)
Proposition IsWellFoundedWellOrd : WellFoundedWellOrd MaxLex (On :x: On).
Proof.
  split.
  - apply IsWellFounded.
  - apply IsWellOrdering.
Qed.

(* Pairing is an order isomorphism from On x On to On.                          *)
Proposition IsIsom : Isom Pairing MaxLex E (On :x: On) On.
Proof.
  apply Isom.Converse, Enum.IsIsom.
  - apply IsWellFoundedWellOrd.
  - apply Core.IsProperSquare.
Qed.

(* Pairing maps the MaxLex initial segment of a pair onto its ordinal value.    *)
Proposition PairingInit : forall (a b:U),
  On a                                                 ->
  On b                                                 ->
  Pairing:[(COI.initSegment MaxLex (On :x: On) :(a,b):)]: :~:
  toClass (Pairing!:(a,b):).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 H2.
  (* The pair belongs to the ordered square of the ordinal class.               *)
  assert ((On :x: On) :(a,b):) as H3. { apply CPR.Charac2. split; assumption. }
  (* Its value under the pairing is therefore an ordinal.                       *)
  assert (On (Pairing!:(a,b):)) as H4. {
    destruct IsIsom as [H4 _].
    apply (ZF.Class.Relation.Bij.IsInRange Pairing (On :x: On) On :(a,b):);
    assumption. }
  (* Intersecting an ordinal with the class of ordinals does not change it.     *)
  assert (On :/\: toClass (Pairing!:(a,b):) :~:
    toClass (Pairing!:(a,b):)) as H5. {
    intros x. split; intros H5.
    - apply H5.
    - split. 2: assumption. apply SOC.IsOrdinal with (Pairing!:(a,b):);
      assumption. }
  (* Isomorphisms carry initial segments to initial segments.                   *)
  apply Equiv.Tran with (COI.initSegment E On Pairing!:(a,b):).
  - apply COI.IsomFullImage. 1: apply IsIsom. assumption.
  - apply Equiv.Tran with (On :/\: toClass (Pairing!:(a,b):)).
    + apply E.InitSegmentEA.
    + assumption.
Qed.

(* The product of two ordinals is a subset of the domain of Pairing.            *)
Proposition IsIncl : forall (a b:U),
  On a                                    ->
  On b                                    ->
  toClass (a :x: b) :<=: domain Pairing.
Proof.
  intros a b H1 H2 z H3.
  apply Prod.Charac in H3. destruct H3 as [x [y [H3 [H4 H5]]]].
  exists Pairing!:(x,y):. rewrite H3.
  apply CRB.Satisfies with (On :x: On) On.
  - apply IsIsom.
  - apply CPR.Charac2.
    assert (On x) as H6. { apply SOC.IsOrdinal with a; assumption. }
    assert (On y) as H7. { apply SOC.IsOrdinal with b; assumption. }
    split; assumption.
Qed.
