Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Fun.From.
Require Import ZF.Set.Relation.Fun.From2.
Require Import ZF.Set.Relation.Fun.IfThenElse.
Require Import ZF.Set.Relation.Id.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.Map.
Require Import ZF.Set.Relation.Map.Prod.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Single.
Require Import ZF.Set.Sum.
Require Import ZF.Set.Union2.

Module SFI := ZF.Set.Relation.Fun.IfThenElse.
Module SSU := ZF.Set.Sum.

(* The either map applies f on the left summand and g on the right.             *)
Definition either (a b f g:U) : U :=
  ifThenElse (a :++: b) (toClass (:{ :0: }: :x: a))
    (fun z => f!((outR :{ :0: }: a)!z))
    (fun z => g!((outR :{ :1: }: b)!z)).

(* The either map sends a pair of maps to their either.                         *)
Definition eitherMap (a b c:U) : U :=
  from2 (map a c) (map b c) (fun f g => either a b f g).

(* The either of maps a -> c and b -> c is a map a ++ b -> c.                   *)
Proposition IsFun : forall (a b c f g:U),
  Fun f a c -> Fun g b c -> Fun (either a b f g) (a :++: b) c.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c f g H1 H2. split.
  - apply SFI.IsFunctionOn.
  - intros y H3. apply Range.Charac in H3. destruct H3 as [z H3].
    apply SFI.Charac2 in H3.
    destruct H3 as [[H3 [H4 H5]]|[H3 [H4 H5]]].
    + rewrite H3. apply Fun.IsInRange with a. 1: assumption.
      apply Fun.IsInRange with (:{ :0: }: :x: a). 2: assumption.
      apply Prod.IsFunR.
    + rewrite H3. apply Fun.IsInRange with b. 1: assumption.
      apply Fun.IsInRange with (:{ :1: }: :x: b). 1: apply Prod.IsFunR.
      apply Union2.Charac in H4.
      destruct H4 as [H4|H4]. 2: assumption. contradiction.
Qed.

(* Evaluating either on the left summand gives the left value.                  *)
Proposition EvalL : forall (a b c f g x:U),
  Fun f a c                           ->
  Fun g b c                           ->
  x :< a                              ->
  (either a b f g)!(:(:0:,x):) = f!x.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c f g x H1 H2 H3. unfold either. rewrite SFI.Eval1.
  - rewrite Prod.EvalR. 1: reflexivity. 2: assumption.
    apply Single.IsIn.
  - apply Union2.Charac. left.
    apply Prod.Charac2. split. 2: assumption.
    apply Single.IsIn.
  - apply Prod.Charac2. split. 2: assumption.
    apply Single.IsIn.
Qed.

(* Evaluating either on the right summand gives the right value.                *)
Proposition EvalR : forall (a b c f g y:U),
  Fun f a c                           ->
  Fun g b c                           ->
  y :< b                              ->
  (either a b f g)!(:(:1:,y):) = g!y.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c f g y H1 H2 H3. unfold either. rewrite SFI.Eval2.
  - rewrite Prod.EvalR. 1: reflexivity. 2: assumption.
    apply Single.IsIn.
  - apply Union2.Charac. right.
    apply Prod.Charac2. split. 2: assumption.
    apply Single.IsIn.
  - intros H4. apply Prod.Charac2 in H4. destruct H4 as [H4 H5].
    apply Single.Charac in H4. symmetry in H4.
    apply ZeroIsNotOne. assumption.
Qed.

(* Composing either with the left injection gives the left component.           *)
Proposition ComposeL : forall (a b c f g:U),
  Fun f a c                           ->
  Fun g b c                           ->
  (either a b f g) :.: (inL a b) = f.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c f g H1 H2. apply Fun.Equal with a c a c.
  2: assumption. 2: reflexivity.
  - apply Fun.Compose with (a :++: b).
    + apply Sum.IsFunL.
    + apply IsFun; assumption.
  - intros x H3.
    rewrite (Fun.ComposeEval (inL a b) (either a b f g) a (a :++: b) c x).
    4: assumption.
    + rewrite SSU.EvalL, (EvalL a b c); try assumption. reflexivity.
    + apply Sum.IsFunL.
    + apply IsFun; assumption.
Qed.

(* Composing either with the right injection gives the right component.         *)
Proposition ComposeR : forall (a b c f g:U),
  Fun f a c                           ->
  Fun g b c                           ->
  (either a b f g) :.: (inR a b) = g.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c f g H1 H2. apply Fun.Equal with b c b c.
  2: assumption. 2: reflexivity.
  - apply Fun.Compose with (a :++: b).
    + apply Sum.IsFunR.
    + apply IsFun; assumption.
  - intros y H3.
    rewrite (Fun.ComposeEval (inR a b) (either a b f g) b (a :++: b) c y).
    4: assumption.
    + rewrite SSU.EvalR, (EvalR a b c); try assumption. reflexivity.
    + apply Sum.IsFunR.
    + apply IsFun; assumption.
Qed.

(* If two injections have disjoint ranges, either is an injection from the sum. *)
Proposition IsInj : forall (a b c f g:U),
  Inj f a c                                      ->
  Inj g b c                                      ->
  (forall x y, x :< a -> y :< b -> f!x <> g!y)   ->
  Inj (either a b f g) (a :++: b) c.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c f g H1 H2 H3.
  remember (either a b f g) as h eqn:H4.
  assert (Fun f a c) as H5. { apply Inj.IsFun. assumption. }
  assert (Fun g b c) as H6. { apply Inj.IsFun. assumption. }
  assert (Fun h (a :++: b) c) as H7. { rewrite H4. apply IsFun; assumption. }
  (* Equal values determine the summand tag and then the original element.      *)
  assert (forall z t, z :< a :++: b -> t :< a :++: b -> h!z = h!t -> z = t)
    as H8. {
    intros z t H8 H9 H10. rewrite H4 in H10.
    apply Union2.Charac in H8. apply Union2.Charac in H9.
    destruct H8 as [H8|H8]; destruct H9 as [H9|H9].
    - apply Prod.Charac in H8. destruct H8 as [u [v [H8 [H11 H12]]]].
      apply Prod.Charac in H9. destruct H9 as [r [s [H9 [H13 H14]]]].
      subst z. subst t. apply Single.Charac in H11. apply Single.Charac in H13.
      subst u. subst r.
      rewrite (EvalL a b c) in H10; try assumption.
      rewrite (EvalL a b c) in H10; try assumption.
      assert (v = s) as H11. { apply (Inj.EvalInjective f a c); assumption. }
      subst v. reflexivity.
    - apply Prod.Charac in H8. destruct H8 as [u [v [H8 [H11 H12]]]].
      apply Prod.Charac in H9. destruct H9 as [r [s [H9 [H13 H14]]]].
      subst z. subst t. apply Single.Charac in H11. apply Single.Charac in H13.
      subst u. subst r.
      rewrite (EvalL a b c) in H10; try assumption.
      rewrite (EvalR a b c) in H10; try assumption.
      assert (f!v <> g!s) as H11. { apply H3; assumption. }
      contradiction.
    - apply Prod.Charac in H8. destruct H8 as [u [v [H8 [H11 H12]]]].
      apply Prod.Charac in H9. destruct H9 as [r [s [H9 [H13 H14]]]].
      subst z. subst t. apply Single.Charac in H11. apply Single.Charac in H13.
      subst u. subst r.
      rewrite (EvalR a b c) in H10; try assumption.
      rewrite (EvalL a b c) in H10; try assumption.
      assert (f!s <> g!v) as H11. { apply H3; assumption. }
      symmetry in H10. contradiction.
    - apply Prod.Charac in H8. destruct H8 as [u [v [H8 [H11 H12]]]].
      apply Prod.Charac in H9. destruct H9 as [r [s [H9 [H13 H14]]]].
      subst z. subst t. apply Single.Charac in H11. apply Single.Charac in H13.
      subst u. subst r.
      rewrite (EvalR a b c) in H10; try assumption.
      rewrite (EvalR a b c) in H10; try assumption.
      assert (v = s) as H11. { apply (Inj.EvalInjective g b c); assumption. }
      subst v. reflexivity. }
  (* Pointwise separation turns the function on the sum into an injection.      *)
  split. 2: apply H7. split.
  - split.
    + apply H7.
    + apply FunctionOn.IsOneToOne with (a :++: b).
      1: apply H7.
      assumption.
  - apply H7.
Qed.

(* Bijections on the two summands induce a bijection between disjoint sums.     *)
Proposition IsBij : forall (a b c d f g f' g':U),
  Bij f a c                                         ->
  Bij g b d                                         ->
  f' = (inL c d) :.: f                              ->
  g' = (inR c d) :.: g                              ->
  Bij (either a b f' g') (a :++: b) (c :++: d).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c d f g f' g' H1 H2 H3 H4.
  remember (either a b f' g') as h eqn:H5.
  (* The two branches inject into the left and right target summands.           *)
  assert (Inj f' a (c :++: d)) as H6. {
    rewrite H3. apply Inj.Compose with c.
    - apply Bij.IsInj. assumption.
    - apply SSU.IsInjL. }
  assert (Inj g' b (c :++: d)) as H7. {
    rewrite H4. apply Inj.Compose with d.
    - apply Bij.IsInj. assumption.
    - apply SSU.IsInjR. }
  (* Distinct target tags make the two branch ranges disjoint.                  *)
  assert (forall x y, x :< a -> y :< b -> f'!x <> g'!y) as H8. {
    intros x y H8 H9 H10.
    rewrite H3 in H10. rewrite H4 in H10.
    rewrite (Inj.ComposeEval f (inL c d) a c (c :++: d) x) in H10.
    2: apply Bij.IsInj; assumption. 2: apply SSU.IsInjL. 2: assumption.
    rewrite (Inj.ComposeEval g (inR c d) b d (c :++: d) y) in H10.
    2: apply Bij.IsInj; assumption. 2: apply SSU.IsInjR. 2: assumption.
    assert (f!x :< c) as H11. { apply Bij.IsInRange with a; assumption. }
    assert (g!y :< d) as H12. { apply Bij.IsInRange with b; assumption. }
    rewrite SSU.EvalL in H10. 2: assumption.
    rewrite SSU.EvalR in H10. 2: assumption.
    apply OrdPair.Equal in H10. destruct H10 as [H10 _].
    apply ZeroIsNotOne. assumption. }
  (* Hence the either map is injective on the disjoint sum.                     *)
  assert (Inj h (a :++: b) (c :++: d)) as H9. {
    rewrite H5. apply IsInj; assumption. }
  assert (Fun h (a :++: b) (c :++: d)) as H10. {
    apply Inj.IsFun. assumption. }
  (* Every tagged target value is hit by using the matching branch bijection.   *)
  assert ((c :++: d) :<=: range h) as H11. {
    intros z H11. apply Union2.Charac in H11.
    destruct H11 as [H11|H11].
    - apply Prod.Charac in H11. destruct H11 as [u [v [H11 [H12 H13]]]].
      apply Single.Charac in H12. subst u.
      apply (Bij.RangeCharac f a c v) in H13. 2: assumption.
      destruct H13 as [x [H13 H14]].
      apply (Fun.RangeCharac h (a :++: b) (c :++: d)). 1: assumption.
      exists (:(:0:,x):). split.
      + apply Union2.Charac. left. apply Prod.Charac2.
        split. 2: assumption. apply Single.IsIn.
      + rewrite H5, (EvalL a b (c :++: d) f' g' x);
        try apply Inj.IsFun; try assumption.
        rewrite H3. rewrite (Inj.ComposeEval f (inL c d) a c (c :++: d) x).
        2: apply Bij.IsInj; assumption. 2: apply SSU.IsInjL. 2: assumption.
        rewrite SSU.EvalL. 2: apply Bij.IsInRange with a; assumption.
        rewrite H14. symmetry. apply H11.
    - apply Prod.Charac in H11. destruct H11 as [u [v [H11 [H12 H13]]]].
      apply Single.Charac in H12. subst u.
      apply (Bij.RangeCharac g b d v) in H13. 2: assumption.
      destruct H13 as [y [H13 H14]].
      apply (Fun.RangeCharac h (a :++: b) (c :++: d)). 1: assumption.
      exists (:(:1:,y):). split.
      + apply Union2.Charac. right. apply Prod.Charac2.
        split. 2: assumption. apply Single.IsIn.
      + rewrite H5, (EvalR a b (c :++: d) f' g' y);
        try apply Inj.IsFun; try assumption.
        rewrite H4. rewrite (Inj.ComposeEval g (inR c d) b d (c :++: d) y).
        2: apply Bij.IsInj; assumption. 2: apply SSU.IsInjR. 2: assumption.
        rewrite SSU.EvalR. 2: apply Bij.IsInRange with b; assumption.
        rewrite H14. symmetry. apply H11. }
  apply Bij.FromFun. 1: assumption. 2: assumption.
  apply H9.
Qed.

(* The either map is a map from map(a,c) x map(b,c) to map(a ++ b,c).           *)
Proposition IsFunMap : forall (a b c:U),
  Fun (eitherMap a b c) ((map a c) :x: (map b c)) (map (a :++: b) c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c. apply From2.IsFun.
  intros f g H1 H2. apply CharacMap. apply IsFun.
  - apply CharacMap. assumption.
  - apply CharacMap. assumption.
Qed.

(* The either of two identities maps the sum onto the union.                    *)
Proposition HasOnto : forall (a b:U),
  Onto (either a b (id a) (id b)) (a :++: b) (a :\/: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b.
  assert (Fun (id a) a (a :\/: b)) as H1. {
    apply Fun.InclCompatR with a.
    - apply Union2.IsInclL.
    - apply Id.IsFun. }
  assert (Fun (id b) b (a :\/: b)) as H2. {
    apply Fun.InclCompatR with b.
    - apply Union2.IsInclR.
    - apply Id.IsFun. }
  assert (Fun (either a b (id a) (id b)) (a :++: b) (a :\/: b)) as H3. {
    apply IsFun; assumption. }
  assert (range (either a b (id a) (id b)) = a :\/: b) as H4. {
    apply Incl.Double. split.
    - apply H3.
    - intros y H5. apply Union2.Charac in H5. destruct H5 as [H5|H5].
      + apply Fun.RangeCharac with (a :++: b) (a :\/: b). 1: assumption.
        exists (:(:0:,y):). split.
        * apply Union2.Charac. left.
          apply Prod.Charac2. split. 2: assumption. apply Single.IsIn.
        * rewrite (EvalL a b (a :\/: b)); try assumption.
          apply Id.Eval. assumption.
      + apply Fun.RangeCharac with (a :++: b) (a :\/: b). 1: assumption.
        exists (:(:1:,y):). split.
        * apply Union2.Charac. right.
          apply Prod.Charac2. split. 2: assumption. apply Single.IsIn.
        * rewrite (EvalR a b (a :\/: b)); try assumption.
          apply Id.Eval. assumption. }
  split. 1: apply H3. assumption.
Qed.

(* If both summands have two elements, their sum injects into their product.    *)
Proposition HasInj : forall (a b:U),
  (exists x y, x :< a /\ y :< a /\ x <> y)  ->
  (exists x y, x :< b /\ y :< b /\ x <> y)  ->
  exists f, Inj f (a :++: b) (a :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b [x1 [x2 [H1 [H2 H3]]]] [y1 [y2 [H4 [H5 H6]]]].
  remember (fun y => y <> y1) as A eqn:H8.
  remember (fun y => :(x1,y):) as g1 eqn:H9.
  remember (fun y:U => :(x2,y2):) as g2 eqn:H10.
  remember (From.from a (fun x => :(x,y1):)) as f eqn:H11.
  remember (SFI.ifThenElse b A g1 g2) as g eqn:H12.
  (* The left branch is the horizontal line at y1.                              *)
  assert (Inj f a (a :x: b)) as H13. {
    rewrite H11. apply From.IsInj.
    - intros x H13. apply Prod.Charac2. split; assumption.
    - intros x y H13 H14 H15. apply OrdPair.Equal in H15. apply H15. }
  (* The right branch is a vertical line, except that y1 is moved aside.        *)
  assert (SFI.Injective b A g1 g2) as H14. {
    rewrite H8. rewrite H9. rewrite H10. split.
    - intros y z H14 H15 H16 H17 H18. apply OrdPair.Equal in H18. apply H18.
    - split.
      + intros y z H14 H15 H16 H17 H18.
        apply OrdPair.Equal in H18. destruct H18 as [H18 H19].
        assert (x1 <> x2) as H20. { assumption. }
        contradiction.
      + split.
        * intros y z H14 H15 H16 H17 H18.
          apply OrdPair.Equal in H18. destruct H18 as [H18 H19].
          assert (x2 <> x1) as H20. {
            intros H20. symmetry in H20. contradiction. }
          contradiction.
        * intros y z H14 H15 H16 H17 H18.
          assert (y = y1) as H19. {
            apply DoubleNegation. intro H19. contradiction. }
          assert (z = y1) as H20. {
            apply DoubleNegation. intro H20. contradiction. }
          subst. reflexivity. }
  assert (Inj g b (a :x: b)) as H15. {
    rewrite H12. apply SFI.IsInj.
    - rewrite H8. rewrite H9. rewrite H10. split.
      + intros y H15 H16. apply Prod.Charac2. split; assumption.
      + intros y H15 H16. apply Prod.Charac2. split; assumption.
    - apply H14. }
  (* The horizontal and modified vertical branches have disjoint values.        *)
  assert (forall x y, x :< a -> y :< b -> f!x <> g!y) as H16. {
    intros x y H16 H17 H18. rewrite H11 in H18. rewrite H12 in H18.
    rewrite From.Eval in H18. 2: assumption.
    assert (A y \/ ~ A y) as H19. { apply LawExcludedMiddle. }
    destruct H19 as [H19|H19].
    - rewrite SFI.Eval1 in H18; try assumption.
      rewrite H9 in H18. apply OrdPair.Equal in H18. destruct H18 as [H18 H20].
      rewrite H8 in H19. symmetry in H20. contradiction.
    - rewrite SFI.Eval2 in H18; try assumption.
      rewrite H10 in H18. apply OrdPair.Equal in H18. destruct H18 as [H18 H20].
      contradiction. }
  exists (either a b f g). apply IsInj; assumption.
Qed.
