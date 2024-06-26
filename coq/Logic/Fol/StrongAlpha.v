Require Import List.

Require Import Logic.Class.Eq.
Require Import Logic.Bool.Eq.
Require Import Logic.Bool.Three.

Require Import Logic.Func.Replace.
Require Import Logic.Func.Permute.
Require Import Logic.Func.Identity.
Require Import Logic.Func.Injective.
Require Import Logic.Func.Composition.

Require Import Logic.List.In.
Require Import Logic.List.Remove.
Require Import Logic.List.Coincide.
Require Import Logic.List.Difference.

Require Import Logic.Rel.Include.
Require Import Logic.Rel.Properties.

Require Import Logic.Fol.Free.
Require Import Logic.Fol.Valid.
Require Import Logic.Fol.Syntax.
Require Import Logic.Fol.Functor.
Require Import Logic.Fol.Variable.
Require Import Logic.Fol.Subformula.
Require Import Logic.Fol.Congruence.

Declare Scope Fol_StrongAlpha_scope.

(* Generator of strong alpha-equivalence.                                       *)
(* Strong alpha-equivalence coincides with the usual alpha-equivalence when the *)
(* type of variable v is infinite. Otherwise, it is a stronger relation. For    *)
(* example, if the type v only has two possible values x and y, the terms       *)
(* t1 = All x (All y (Elem x y))                                                *)
(* t2 = All y (All x (Elem y x))                                                *)
(* are alpha-equivalent but not strongly so. See examples below.                *)
Inductive StrongAlpha0 (v:Type) (e:Eq v) : P v -> P v -> Prop :=
| mkStrongAlpha0: forall (x y:v) (p1:P v), 
    x <> y        -> 
    ~ y :: var p1 ->
    StrongAlpha0 v e (All x p1) (All y (fmap (y // x) p1)) 
.

Arguments StrongAlpha0 {v} {e}.
Arguments mkStrongAlpha0 {v} {e}.

(* The strong alpha-equivalence is the congruence generated by StrongAlph0.     *)
Definition StrongAlpha (v:Type) (e:Eq v) : P v -> P v -> Prop := 
    Cong (@StrongAlpha0 v e).

Arguments StrongAlpha {v} {e}.

Notation "p ~ q" := (StrongAlpha p q)
    (at level 60, no associativity) : Fol_StrongAlpha_scope.

Open Scope Fol_StrongAlpha_scope.

(* Not following pdf to obtain stronger result of equality as lists.            *)
(* Two strongly alpha-equivalent formulas have the same free variables.         *)
Lemma StrongAlpha_free : forall (v:Type) (e:Eq v) (p q:P v), 
    p ~ q -> Fr p = Fr q.
Proof.
    intros v e. apply incl_charac, Cong_smallest.
    - apply free_congruence.
    - apply incl_charac. intros x y H1. destruct H1 as [x y p1 H1 H2]. simpl.
      assert (valid (y // x) p1) as H3. { apply valid_replace. assumption. }
      assert (Fr (fmap (y // x) p1) = map (y // x) (Fr p1)) as H4.
        { destruct (valid_free v v e e (y // x) p1) as [H5 H6].
          apply H5.
            { apply H3. } 
            { apply Sub_refl. }}
      rewrite H4. assert (y = (y // x) x) as H7.
        { rewrite replace_x. reflexivity. } 
      rewrite H7 at 1. clear H3 H4 H7. rewrite (remove_map v v e e).
        + rewrite (coincide_map v v (y //x) id).
            { symmetry. apply map_id. }
            { intros u H3. apply replace_not_x. unfold id. intros H4. 
              subst. revert H3. apply remove_x_gone. }
        + intros u H3 H4. rewrite replace_x. rewrite replace_not_x; 
          intros H5; subst.
            { apply H2. apply (free_var v e). assumption. }
            { apply H3. reflexivity. }
Qed.

(* Strong alpha-equivalence is preserved by injective maps.                     *)
Lemma StrongAlpha_injective : 
    forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (p q:P v),
        injective f -> p ~ q -> fmap f p ~ fmap f q.
Proof.
    intros v w e e' f p q H1 H2. revert p q H2. 
    apply incl_charac, Cong_smallest.
    - apply fmap_congruence, Cong_congruence.
    - apply incl_charac. intros p q H2. destruct H2 as [x y p1 H2 H3]. simpl.
      apply CongBase. rewrite <- fmap_comp'. 
      assert (f ; (y // x) = (f y // f x) ; f) as H4. {
        apply replace_injective. assumption. }
      rewrite H4. rewrite fmap_comp. constructor.
        + intros H5. apply H2, H1. assumption.
        + intros H5. rewrite var_fmap in H5. apply in_map_iff in H5.
          destruct H5 as [u [H5 H6]]. apply H1 in H5. subst.
          apply H3 in H6. contradiction.
Qed.

(* Strong alpha-equivalence is preserved by variable replacement, if the new    *)
(* variable y is fresh, i.e. does not already belong to any of the terms.       *)
Lemma StrongAlpha_replace : 
    forall (v:Type) (e:Eq v) (p q:P v) (x y:v),
        ~ y :: var p -> ~ y :: var q -> 
            p ~ q -> fmap (y // x) p ~ fmap (y // x) q.
Proof.
    intros v e p q x y H1 H2 H3.
    assert (fmap (y // x) p = fmap (y <:> x) p) as H4.
        { apply var_replace_permute. assumption. }
    assert (fmap (y // x) q = fmap (y <:> x) q) as H5.
        { apply var_replace_permute. assumption. }
    rewrite H4, H5. apply (StrongAlpha_injective _ _ _).
    apply permute_injective. assumption.
Qed.

(* Strong alpha-equivalence class unchanged by variable replacement, if the new *)
(* variable y is fresh and the variable being replaced x is not free.           *)
Lemma StrongAlpha_replace_self:
    forall (v:Type) (e:Eq v) (p:P v) (x y:v),
        ~ y :: var p -> 
        ~ x :: Fr p  ->
        fmap (y // x) p ~ p.
Proof.
    intros v e p x y. revert p. 
    induction p as [|x' y'|p1 IH1 p2 IH2|x' p1 IH1]; 
    intros H1 H2; simpl; simpl in H1; simpl in H2.
    - apply Cong_reflexive.
    - unfold replace. 
      destruct (eqDec x' x) as [H3|H3]; destruct (eqDec y' x) as [H4|H4].
        + subst. exfalso. apply H2. left. reflexivity.
        + subst. exfalso. apply H2. left. reflexivity.
        + subst. exfalso. apply H2. right. left. reflexivity.
        + apply Cong_reflexive.
    - apply CongImp.
        + apply IH1; intros H3.
            { apply H1, in_or_app. left. assumption. }
            { apply H2, in_or_app. left. assumption. }
        + apply IH2; intros H3.
            { apply H1, in_or_app. right. assumption. }
            { apply H2, in_or_app. right. assumption. }
    - unfold replace. destruct (eqDec x' x) as [H3|H3].
        + subst. destruct (eqDec x y) as [H4|H4].
            { subst. apply CongAll. fold (y // y). rewrite replace_x_x.
              rewrite fmap_id. apply Cong_reflexive. }
            { fold (y // x). apply Cong_symmetric, CongBase. 
              constructor; try assumption.
              intros H5. apply H1. right. assumption. }
        + apply CongAll. apply IH1; intros H4.
            { apply H1. right. assumption. }
            { apply H2. exfalso. apply H2. apply remove_still; assumption. }
Qed.

(* Almost strong alpha-equivalence. Will be shown to be the same.               *)
Inductive AlmostStrongAlpha (v:Type) (e:Eq v) : P v -> P v -> Prop := 
| ABot : AlmostStrongAlpha v e Bot Bot
| AElem : forall (x y:v), AlmostStrongAlpha v e (Elem x y) (Elem x y)
| AImp  : forall (p1 p2 q1 q2:P v), 
    p1 ~ q1 -> 
    p2 ~ q2 -> 
    AlmostStrongAlpha v e (Imp p1 p2) (Imp q1 q2)
| AAllx : forall (x:v) (p1 q1:P v), 
    p1 ~ q1 -> 
    AlmostStrongAlpha v e (All x p1) (All x q1)
| AAllxy : forall (x y:v) (p1 q1 r:P v),
    x <> y               ->
    p1 ~ r               ->
    q1 ~ fmap (y // x) r ->
    ~ y :: var r         ->
    AlmostStrongAlpha v e (All x p1) (All y q1)
.

Arguments AlmostStrongAlpha {v} {e}.

Notation "p :~: q" := (AlmostStrongAlpha p q)
    (at level 60, no associativity) : Fol_StrongAlpha_scope.

Open Scope Fol_StrongAlpha_scope.

Lemma almostImpRev : forall (v:Type) (e:Eq v) (p1 p2 q:P v), 
    Imp p1 p2 :~: q -> exists (q1 q2:P v),
        (p1 ~ q1) /\ (p2 ~ q2) /\ (q = Imp q1 q2).
Proof.
    intros v e p1 p2 q H1. remember (Imp p1 p2) as p eqn:E. revert p1 p2 E.
    destruct H1 as [|x y|p1' p2' q1 q2 H1 H2|x p1' q1|x y p1' q1 r H1 H2 H3 H4];
    intros p1 p2 E; inversion E. subst. exists q1. exists q2.
    split; try assumption. split; try assumption. reflexivity.
Qed.


Lemma almostAllRev : forall (v:Type) (e:Eq v) (p1 q:P v) (x:v),
    All x p1 :~: q -> 
        (exists (q1:P v), (p1 ~ q1) /\ (q = All x q1)) \/
        (exists (q1 r:P v) (y:v),
            (x <> y)                /\ 
            (p1 ~ r)                /\ 
            (q1 ~ fmap (y // x) r)  /\
            (~ y :: var r)          /\
            (q = All y q1)).
Proof.
    intros v e p1 q x H1. remember (All x p1) as p eqn:E. revert x p1 E.
    destruct H1 as [|x' y|p1' p2 q1 q2 H1 H2|x' p1' q1|x' y p1' q1 r H1 H2 H3 H4];
    intros x p1 E; inversion E; subst; clear E.
    - left. exists q1. split; try assumption. reflexivity.
    - right. exists q1. exists r. exists y.
      split; try assumption.
      split; try assumption.
      split; try assumption.
      split; try assumption.
      reflexivity.
Qed.

(* Almost equivalence contains generator of strong alpha-equivalence.           *)
Lemma almostStrongAlpha0 : forall (v:Type) (e:Eq v),
    @StrongAlpha0 v e <= @AlmostStrongAlpha v e.
Proof.
    intros v e. apply incl_charac. intros p q H1.
    destruct H1 as [x y p1 H1 H2]. apply AAllxy with p1;
    try assumption; try (apply Cong_reflexive).
Qed.

(* Almost equivalence is reflexive.                                             *)
Lemma almostRefl : forall (v:Type) (e:Eq v) (p:P v), p :~: p.
Proof.
    intros v e p. destruct p as [|x y|p1 p2|x p1]; 
    try constructor; try (apply Cong_reflexive).
Qed.

(* Almost equivalence is symmetric.                                             *)
Lemma almostSym : forall (v:Type) (e:Eq v) (p q:P v), p :~: q -> q :~: p.
Proof.
    intros v e p q H1. 
    destruct H1 as [|x y|p1 p2 q1 q2 H1 H2|x p1 q1|x y p1 q1 r H1 H2 H3 H4].
    - constructor.
    - constructor.
    - constructor; apply Cong_symmetric; assumption.
    - constructor. apply Cong_symmetric. assumption.
    - apply AAllxy with (fmap (y // x) r).
        + apply not_eq_sym. assumption.
        + assumption.
        + apply Cong_transitive with r; try assumption.
          assert (r = fmap (x // y) (fmap (y // x) r)) as H5.
            { rewrite var_replace_trans; try assumption.
              rewrite replace_x_x. rewrite fmap_id. reflexivity. }
          rewrite <- H5. apply Cong_reflexive.
        + apply var_replace_remove. assumption.
Qed.

(* Almost equivalence is transitive.                                            *)
Lemma almostTrans : forall (v:Type) (e:Eq v) (p q r:P v),
    p :~: q -> q :~: r -> p :~: r.
Proof.
    intros v e p q r H1. revert r.
    destruct H1 as [|x y|p1 p2 q1 q2 H1 H2|x p1 q1|x y p1 q1 r' H1 H2 H3 H4];
    intros r H5.
    - assumption.
    - assumption.
    - apply almostImpRev in H5. 
      destruct H5 as [r1 [r2 [H5 [H6 H7]]]]. subst. constructor.
        + apply Cong_transitive with q1; assumption.
        + apply Cong_transitive with q2; assumption.
    - apply almostAllRev in H5. destruct H5 as [H5|H5].
        + destruct H5 as [r1 [H5 H6]]. subst. constructor.
          apply Cong_transitive with q1; assumption.
        + destruct H5 as [r1 [r' [y [H5 [H6 [H7 [H8 H9]]]]]]]. subst. 
          apply AAllxy with r'; try assumption.
          apply Cong_transitive with q1; assumption.
    - apply almostAllRev in H5. destruct H5 as [H5|H5].
        + destruct H5 as [r1 [H5 H6]]. subst.
          apply AAllxy with r'; try assumption.
          apply Cong_transitive with q1; try assumption.
          apply Cong_symmetric. assumption.
        + destruct H5 as [r1 [s [z [H5 [H6 [H7 [H8 H9]]]]]]]. subst.
          destruct (eqDec x z) as [H10|H10].
            { subst. constructor. 
              rewrite var_replace_permute in H3; try assumption.
              rewrite var_replace_permute in H7; try assumption.
              rewrite permute_comm in H7.
              apply Cong_transitive with (fmap (y <:> z) s);
              try (apply Cong_symmetric; assumption).
              apply Cong_transitive with (fmap (y <:> z) q1).
              { apply Cong_transitive with (fmap (y <:> z) (fmap (y <:> z) r')).
                { rewrite <- fmap_comp', permute_involution, fmap_id.
                  assumption. }
                { apply (StrongAlpha_injective _ _ _ _).
                    { apply permute_injective. }
                    { apply Cong_symmetric. assumption. }}}  
              { apply (StrongAlpha_injective _ _ _ _); try assumption.
                  { apply permute_injective. }}}
            { assert (~z :: Fr r') as K.
                { intros H9.
                  assert (z :: Fr (fmap (y // x) r')) as H11.
                    { destruct (in_dec eqDec x (Fr r')) as [H12|H12]. 
                        { apply free_replace2; try assumption. right.
                          split; try assumption. apply not_eq_sym. assumption. }
                        { rewrite free_replace1; assumption. }}
                  apply H8. apply (free_var _ _ s z).
                  rewrite (StrongAlpha_free _ _ s (fmap (y // x) r'));
                  try assumption. apply Cong_transitive with q1; 
                  try assumption. apply Cong_symmetric. assumption. }
              apply AAllxy with (fmap (y // z) r'); try assumption.
                { apply Cong_transitive with r'; try assumption.
                  apply Cong_symmetric. apply StrongAlpha_replace_self;
                  try assumption. }
                { assert (fmap (x // y) (fmap (z // x) (fmap (y // z) r'))
                        = fmap (z // y) (fmap (x // z) (fmap (y // x) r'))) as H9.
                    { rewrite <- fmap_comp', <- fmap_comp'.
                      rewrite <- fmap_comp', <- fmap_comp'.
                      apply var_support. intros u H9.
                      assert (u <> y) as H11.
                        { intros H12. subst. apply H4. assumption. }
                      unfold comp.
                      destruct (eqDec u x) as [H12|H12]; 
                      destruct (eqDec u z) as [H13|H13].
                        { subst. reflexivity. }
                        { subst. rewrite replace_x.
                          rewrite (replace_not_x _ _ z y x); try assumption.
                          rewrite replace_x.
                          rewrite (replace_not_x _ _ y x z).
                            { rewrite (replace_not_x _ _ z x y); try assumption.
                              rewrite replace_x. reflexivity. }
                            { intros H14. subst. apply H5. reflexivity. }}
                        { subst. rewrite replace_x.
                          rewrite (replace_not_x _ _ x z y).
                            { rewrite replace_x.
                              rewrite (replace_not_x _ _ x y z); try assumption.
                              rewrite replace_x.
                              rewrite (replace_not_x _ _ y z x); try assumption.
                              reflexivity. }
                            { intros H13. subst. apply H1. reflexivity. }}
                        { rewrite (replace_not_x _ _ z y u); try assumption.
                          rewrite (replace_not_x _ _ x z u); try assumption.
                          rewrite (replace_not_x _ _ y x u); try assumption.
                          rewrite (replace_not_x _ _ x y u); try assumption.
                          rewrite (replace_not_x _ _ z x u); try assumption.
                          rewrite (replace_not_x _ _ y z u); try assumption.
                          reflexivity. }}
                  apply Cong_transitive with (fmap (z // y) s); try assumption. 
                  apply Cong_symmetric.
                  assert (fmap (z // x) (fmap (y // z) r') ~
                    fmap (x // y) (fmap (z // x) (fmap (y // z) r'))) as H11. 
                    { apply Cong_symmetric, StrongAlpha_replace_self.
                        { apply var_replace_remove. assumption. }
                        { intros H11. assert (y :: Fr (fmap (y // z) r')) as H12.
                            { destruct (in_dec eqDec x (Fr (fmap (y // z) r')))
                              as [H13|H13]. 
                                { rewrite free_replace2 in H11; try assumption.
                                    { destruct H11 as [H11|H11].
                                        { subst. exfalso. apply H5. reflexivity. }
                                        { destruct H11 as [H11 H14]. assumption. }}
                                    { apply var_replace_remove. intros H14. subst.
                                      apply H5. reflexivity. }}
                                { rewrite free_replace1 in H11; try assumption.
                                  apply var_replace_remove. intros H14. subst.
                                  apply H5. reflexivity. }}
                      apply H4. apply (free_var _ _ _). 
                      rewrite free_replace1 in H12; assumption. }}
                  assert (fmap (z // y) s ~
                    fmap (z // y) (fmap (x // z) (fmap (y // x) r'))) as H12.
                    { apply StrongAlpha_replace; try assumption.
                        { apply var_replace_remove. intros H12. subst.
                          apply H10. reflexivity. }
                        { apply Cong_symmetric.
                          apply Cong_transitive with q1; try assumption.
                          apply Cong_symmetric.
                          apply Cong_transitive with (fmap (y // x) r');
                          try assumption. apply Cong_symmetric.
                          apply StrongAlpha_replace_self.
                            { apply var_replace_remove; try assumption. }
                            { intros H12. 
                              destruct (in_dec eqDec x (Fr r')) as [H13|H13].
                                { rewrite free_replace2 in H12; try assumption.
                                  destruct H12 as [H12|[H12 H14]]. 
                                    { subst. apply H5. reflexivity. }
                                    { apply K in H12. contradiction. }}
                                { rewrite free_replace1 in H12; try assumption.
                                  apply K in H12. contradiction. }}}}
                  apply Cong_transitive with 
                    (fmap (x // y) (fmap (z // x) (fmap (y // z) r'))).
                    { assumption. }
                    { apply Cong_symmetric. rewrite H9. assumption. }}
                { apply var_replace_remove. apply not_eq_sym. assumption. }}
Qed.

(* Almost strong equivalence implies strong equivalence.                        *)
Lemma almostStrongAlpha : forall (v:Type) (e:Eq v) (p q:P v),
   p :~: q -> p ~ q.
Proof.
    intros v e p q H1.
    destruct H1 as [|x y|p1 p2 q1 q2 H1 H2|x p1 q1|x y p1 q1 r' H1 H2 H3 H4].
    - apply Cong_reflexive.
    - apply Cong_reflexive.
    - apply CongImp; assumption.
    - apply CongAll. assumption.
    - apply Cong_transitive with (All x r').
        + apply CongAll. assumption.
        + apply Cong_symmetric. 
          apply Cong_transitive with (All y (fmap (y // x) r')).
            { apply CongAll. assumption. }
            { apply Cong_symmetric, CongBase. constructor; assumption. }
Qed.

(* The almost equivalence is a congruent relation.                              *)
Lemma almostCongruent : forall (v:Type) (e:Eq v),
    congruent (@AlmostStrongAlpha v e).
Proof.
    intros v e. split.
    - intros p1 p2 q1 q2 H1 H2. constructor; apply almostStrongAlpha; assumption.
    - intros x p1 q1 H1. constructor. apply almostStrongAlpha. assumption.
Qed.

(* The almost equivalence is a congruence                                       *)
Lemma almostCongruence : forall (v:Type) (e:Eq v),
    congruence (@AlmostStrongAlpha v e).
Proof.
    intros v e. split.
    - split.
        + unfold reflexive. apply almostRefl.
        + split.
            { unfold symmetric. apply almostSym. }
            { unfold transitive. apply almostTrans. }
    - apply almostCongruent.
Qed.

(* The almost equivalence is the same relation as the strong alpha-equivalence. *)
Lemma almostIsStrong : forall (v:Type) (e:Eq v) (p q:P v),
    p :~: q <-> p ~ q.
Proof.
    intros v e p q. split.
    - apply almostStrongAlpha.
    - apply incl_charac_to. apply Cong_smallest.
        + apply almostCongruence.
        + apply almostStrongAlpha0.
Qed.

Theorem strongAlphaCharac : forall (v:Type) (e:Eq v) (p q:P v),
    p ~ q <->
    (p = Bot /\ q = Bot)                            \/
    (exists (x y:v), p = Elem x y /\ q = Elem x y)  \/
    (exists (p1 p2 q1 q2:P v), 
        p = Imp p1 p2               /\ 
        q = Imp q1 q2               /\ 
        p1 ~ q1                     /\
        p2 ~ q2)                                    \/
    (exists (x:v) (p1 q1:P v), 
        p = All x p1                /\
        q = All x q1                /\
        p1 ~ q1)                                    \/
    (exists (x y:v) (p1 q1 r:P v), 
        p = All x p1                /\
        q = All y q1                /\
        x <> y                      /\
        ~ y :: var r                /\
        p1 ~ r                      /\
        q1 ~ fmap (y // x) r).
Proof.
    intros v e p q. split.
    - intros H1. rewrite <- almostIsStrong in H1. 
      destruct H1 as [|x y|p1 p2 q1 q2 H1 H2|x p1 q1 H1|x y p1 q1 r H1 H2 H3 H4].
        + left. split; reflexivity.
        + right. left. exists x. exists y. split; reflexivity.
        + right. right. left. exists p1. exists p2. exists q1. exists q2.
          split; try reflexivity. split; try reflexivity. split; assumption.
        + right. right. right. left. exists x. exists p1. exists q1.
          split; try reflexivity. split; try reflexivity. assumption.
        + right. right. right. right. exists x. exists y. exists p1. exists q1.
          exists r. split; try reflexivity. split; try reflexivity.
          split; try assumption. split; try assumption. split; assumption.
    - intros 
        [ [H1 H2]
        | [[x [y [H1 H2]]]
        | [[p1 [p2 [q1 [q2 [H1 [H2 [H3 H4]]]]]]]
        | [[x [p1 [q1 [H1 [H2 H3]]]]]
        | [x [y [p1 [q1 [r [H1 [H2 [H3 [H4 [H5 H6]]]]]]]]]]
        ]]]]; apply almostIsStrong; rewrite H1, H2.
        + constructor.
        + constructor.
        + constructor; assumption.
        + constructor. assumption.
        + apply AAllxy with r; assumption.
Qed.

Lemma StrongAlphaBotRev : forall (v:Type) (e:Eq v) (p:P v), Bot ~ p -> p = Bot.
Proof.
    intros v e p H1. apply strongAlphaCharac in H1. destruct H1 as 
    [[H1 H2]
    |[[x [y [H1 H2]]]
    |[[p1 [p2 [q1 [q2 [H1 [H2 H3]]]]]]
    |[[x [p1 [q1 [H1 [H2 H3]]]]]
    |[x [y [p1 [q1 [r [H1 [H2 H3]]]]]]]]]]]; try inversion H1.
    assumption.
Qed.


Lemma StrongAlphaElemRev : forall (v:Type) (e:Eq v) (p:P v) (x y:v),
    Elem x y ~ p -> p = Elem x y.
Proof.
    intros v e p x' y' H1. apply strongAlphaCharac in H1. destruct H1 as 
    [[H1 H2]
    |[[x [y [H1 H2]]]
    |[[p1 [p2 [q1 [q2 [H1 [H2 H3]]]]]]
    |[[x [p1 [q1 [H1 [H2 H3]]]]]
    |[x [y [p1 [q1 [r [H1 [H2 H3]]]]]]]]]]]; try inversion H1.
    subst. reflexivity.
Qed.

Lemma StrongAlphaImpRev : forall (v:Type) (e:Eq v) (p1 p2 q:P v), 
    Imp p1 p2 ~ q -> exists (q1 q2:P v),
        (p1 ~ q1) /\ (p2 ~ q2) /\ (q = Imp q1 q2).
Proof.
    intros v e p1 p2 q H1. apply almostImpRev, almostIsStrong. assumption.
Qed.


Lemma StrongAlphaAllRev : forall (v:Type) (e:Eq v) (p1 q:P v) (x:v),
    All x p1 ~ q -> 
        (exists (q1:P v), (p1 ~ q1) /\ (q = All x q1)) \/
        (exists (q1 r:P v) (y:v),
            (x <> y)                /\ 
            (p1 ~ r)                /\ 
            (q1 ~ fmap (y // x) r)  /\
            (~ y :: var r)          /\
            (q = All y q1)).
Proof.
    intros v e p1 q x H1. apply almostAllRev, almostIsStrong. assumption.
Qed.

(* This is why strong alpha-equivalence is not the right notion, as it fails    *)
(* in cases when the set of variables is finite. Here card V = 2.               *)
(* We expose two terms which are clearly alpha-equivalent but not strongly so.  *)
Lemma CounterExample1 : forall (x y:bool), x <> y ->
    ~(All x (All y (Elem x y)) ~ All y (All x (Elem y x))).
Proof.
    intros x y Hxy.
    remember (All y (Elem x y)) as p1 eqn:H1. 
    remember (All x (Elem y x)) as q1 eqn:H2.
    intros H3. apply StrongAlphaAllRev in H3. destruct H3 as [H3|H3].
    - destruct H3 as [p1' [H3 H4]]. inversion H4. subst. apply Hxy. reflexivity.
    - destruct H3 as [q1' [r [z [H3 [H4 [H5 [H6 H7]]]]]]]. 
      inversion H7. subst. clear H7. apply StrongAlphaAllRev in H4.
      destruct H4 as [H4|H4].
        + destruct H4 as [q1 [H4 H7]]. apply H6. rewrite H7. left. reflexivity.
        + destruct H4 as [q1 [r' [y [H4 [H7 [H8 [H9 H10]]]]]]].
          apply StrongAlphaElemRev in H7. 
          apply (onlyTwoElements x y z); try assumption.
            { intros H11. subst. apply H9. left. reflexivity. }
            { auto. }
Qed.

(* Another example of failure, this time with a three-element variable set.     *)
Lemma CounterExample2 : forall (x y z:Three), 
    x <> y -> 
    x <> z -> 
    y <> z -> ~ (
        All x (All y (All z (Imp (Elem x y) (Elem y z))))
        ~
        All y (All z (All x (Imp (Elem y z) (Elem z x))))).
Proof.
    intros x y z H1 H2 H3.
    remember (All y (All z (Imp (Elem x y) (Elem y z)))) as p1 eqn:H4.
    remember (All z (All x (Imp (Elem y z) (Elem z x)))) as q1 eqn:H5. 
    intros H6. apply StrongAlphaAllRev in H6. destruct H6 as [H6|H6]. 
    - destruct H6 as [p1' [H6 H7]]. inversion H7. subst. apply H1. reflexivity.
    - destruct H6 as [q1' [r [u [H6 [H7 [H8 [H9 H10]]]]]]]. inversion H10. 
      rewrite <- H11 in H8. (* H11 name is auto *)
      rewrite <- H0  in H8. (* H0  name is auto *)
      rewrite <- H0  in H9. (* H0  name is auto *)
      clear H0 H6 H10 H11 q1' u.
      rewrite H4 in H7. generalize H7. intros G7.
      apply StrongAlphaAllRev in H7. destruct H7 as [H7|H7].
        + destruct H7 as [q1' [H7 H10]]. apply H9. rewrite H10. 
          left. reflexivity.
        + destruct H7 as [q2 [r2 [u [H7 [H10 [H11 [H12 H13]]]]]]]. 
          destruct (eqDec x u) as [H14|H14].
            { assert (~ x :: Fr r) as H15. 
                { intros H15. rewrite <- H14 in H13. rewrite H13 in H15.
                  simpl in H15. apply remove_x_gone in H15. assumption. }
              apply H15. 
              assert (Fr(All y (All z (Imp (Elem x y) (Elem y z)))) = Fr r) as H16. 
                { apply StrongAlpha_free. assumption. }
              rewrite <- H16. 
              apply remove_still; try auto.
              apply remove_still; try auto.
              left. reflexivity. }
            { destruct (eqDec z u) as [H15|H15].
                { rewrite <- H15 in H13. 
                  apply StrongAlphaAllRev in G7. destruct G7 as [G7|G7].
                    { destruct G7 as [q3 [G8 G9]]. rewrite H13 in G9.
                      inversion G9. subst. apply H3. reflexivity. }
                    { destruct G7 as [q3 [r3 [v [G8 [G9 [G10 [G11 G12]]]]]]].
                      rewrite H13 in G12. inversion G12. rewrite <- H6 in G10.
                      rewrite <- H0 in G10. (* H0 name is auto *)
                      rewrite <- H0 in G11. clear G8 G12 H0 H6 v.
                      generalize G9. intros K9.
                      apply StrongAlphaAllRev in G9. destruct G9 as [G9|G9].
                        { destruct G9 as [q4 [G12 G13]]. apply G11. rewrite G13.
                          left. reflexivity. }
                        { destruct G9 as [q4 [r4 [v [G12 [G13 [G14 [G15 G16]]]]]]].
                            { destruct (eqDec x v) as [K10|K10].
                                { rewrite <- K10 in G16.
                                  assert (~ x :: Fr r3) as K11.
                                    { intros K11. rewrite G16 in K11.
                                      apply remove_x_gone in K11. assumption. }
                                  assert (Fr(All z (Imp (Elem x y) (Elem y z)))
                                    = Fr r3) as K13.
                                    { apply StrongAlpha_free. assumption. }
                                  apply K11. rewrite <- K13.
                                  apply remove_still; try auto.
                                  left. reflexivity. }
                                { destruct (eqDec y v) as [K11|K11].
                                    { rewrite <- K11 in G16.
                                      assert (~ y :: Fr r3) as K12.
                                        { intros K12. rewrite G16 in K12.
                                          apply remove_x_gone in K12. assumption. }
                                       assert 
                                        (Fr(All z (Imp (Elem x y) (Elem y z)))
                                        = Fr r3) as K13.
                                        { apply StrongAlpha_free. assumption. }
                                       apply K12. rewrite <- K13.
                                       apply remove_still; try auto.
                                       right. left. reflexivity. }
                                    { apply (onlyThreeElements x y z v); 
                                      auto. }}}}}}
                { apply (onlyThreeElements x y z u); auto. }}
Qed.
