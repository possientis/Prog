Require Import List.

Require Import Logic.Class.Eq.

Require Import Logic.List.In.
Require Import Logic.List.Include.

Require Import Logic.Fol.Free.
Require Import Logic.Fol.Syntax.

Require Import Logic.Fol2.Context.

Fixpoint removeFromScope (v:Type) (e:Eq v) (x:v) (G:Ctx v) : Ctx v :=
  match G with
  | nil               => nil
  | (cons (Var y) G') =>
      match (eqDec x y) with
      | left _        => removeFromScope v e x G'
      | right _       => cons (Var y) (removeFromScope v e x G')
      end
  | (cons (Prp p) G') =>
      match in_dec eqDec x (Fr p) with
      | left _        => removeFromScope v e x G'
      | right _       => cons (Prp p) (removeFromScope v e x G')
    end
 end.

Arguments removeFromScope {v} {e}.

Lemma remove_stillV : forall (v:Type) (e:Eq v) (G:Ctx v) (x y:v),
  x <> y -> Var y :: G -> Var y :: removeFromScope x G.
Proof.
  intros v e G x y. induction G as [|ent G' IH].
  - intros _ HIn. inversion HIn.
  - destruct ent as [z|p]; intros HNeq HIn; simpl.
    + destruct (eqDec x z) as [Hxz|Hxz].
      * subst. apply IH.
        { apply HNeq. }
        { destruct HIn as [HIn|HIn].
          - inversion HIn. contradiction.
          - apply HIn. }
      * destruct HIn as [HIn|HIn].
        { inversion HIn. subst. left. reflexivity. }
        { right. apply IH.
          - apply HNeq.
          - apply HIn. }
    + destruct (in_dec eqDec x (Fr p)) as [HFree|HFree].
      * apply IH. apply HNeq. destruct HIn as [HIn|HIn].
        { inversion HIn. }
        { apply HIn. }
      * right. apply IH. apply HNeq. destruct HIn as [HIn|HIn].
        { inversion HIn. }
        { apply HIn. }
Qed.

Lemma remove_stillP : forall (v:Type) (e:Eq v) (G:Ctx v) (x:v) (p:P v),
  ~x :: Fr p -> Prp p :: G -> Prp p :: removeFromScope x G.
Proof.
  intros v e G x p. induction G as [|ent G' IH].
  - intros _ HIn. inversion HIn.
  - destruct ent as [y|q]; intros HFree HIn; simpl.
    + destruct (eqDec x y) as [Hxy|Hxy].
      * apply IH.
        { apply HFree. }
        { destruct HIn as [HIn|HIn].
          - inversion HIn.
          - apply HIn. }
      * right. apply IH.
        { apply HFree. }
        { destruct HIn as [HIn|HIn].
          - inversion HIn.
          - apply HIn. }
    + destruct (in_dec eqDec x (Fr q)) as [HFree'|Hfree'].
      * apply IH.
        { apply HFree. }
        { destruct HIn as [HIn|HIn].
          - inversion HIn. subst. contradiction.
          - apply HIn. }
      * destruct HIn as [HIn|HIn].
        { inversion HIn. subst. left. reflexivity. }
        { right. apply IH.
          - apply HFree.
          - apply HIn. }
Qed.

Lemma removeFromScope_mon : forall (v:Type) (e:Eq v) (G H:Ctx v) (x:v),
  G <= H -> (removeFromScope x G) <= (removeFromScope x H).
Proof.
  intros v e G H x. revert H. induction G as [|ent G' IH]; simpl; intros H HIncl.
  - intros u Hu. inversion Hu.
  - destruct ent as [y|p].
    + destruct (eqDec x y) as [HEq|HNeq].
      * subst. apply IH. intros u Hu. apply HIncl. right. apply Hu.
      * intros ent Hent. destruct Hent as [Hent|Hent].
        { rewrite <- Hent. apply remove_stillV.
          - apply HNeq.
          - apply HIncl. left. reflexivity. }
        { apply IH. intros u Hu.
          - apply HIncl. right. apply Hu.
          - apply Hent. }
    + destruct (in_dec eqDec x (Fr p)) as [HFree|HFree].
      * apply IH. intros u Hu. apply HIncl. right. apply Hu.
      * intros ent Hent. destruct Hent as [Hent|Hent].
        { rewrite <- Hent. apply remove_stillP.
          - apply HFree.
          - apply HIncl. left. reflexivity. }
        { apply IH.
          - intros u Hu. apply HIncl. right. apply Hu.
          - apply Hent. }
Qed.

Lemma remove_goneV : forall (v:Type) (e:Eq v) (G:Ctx v) (x:v),
  ~ Var x :: removeFromScope x G.
Proof.
  intros v e G x. induction G as [|ent G' IH]; simpl.
  - intros H. apply H.
  - destruct ent as [y|p].
    + destruct (eqDec x y) as [HEq|HNeq].
      * apply IH.
      * intros [HIn|HIn].
        { inversion HIn. subst. contradiction. }
        { apply IH, HIn. }
    + destruct (in_dec eqDec x (Fr p)) as [HFree|HFree].
      * apply IH.
      * intros [HIn|HIn].
        { inversion HIn. }
        { apply IH, HIn. }
Qed.

Lemma remove_goneP : forall (v:Type) (e:Eq v) (G:Ctx v) (x:v) (p:P v),
  x :: Fr p -> ~ Prp p :: removeFromScope x G.
Proof.
  intros v e G x p HFree. induction G as [|ent G' IH]; simpl.
  - intros H. apply H.
  - destruct ent as [y|q].
    + destruct (eqDec x y) as [HEq|HNeq].
      * apply IH.
      * intros [HIn|HIn].
        { inversion HIn. }
        { apply IH, HIn. }
    + destruct (in_dec eqDec x (Fr q)) as [HFree'|HFree'].
      * apply IH.
      * intros [HIn|HIn].
        { inversion HIn. subst. contradiction. }
        { apply IH, HIn. }
Qed.


Lemma removeFromScope_x_not_in : forall (v:Type) (e:Eq v) (G:Ctx v) (x:v),
  CtxVal G -> ~ Var x :: G -> removeFromScope x G = G.
Proof.
  intros v e G x. induction G as [|ent G' IH]; intros HVal HIn; simpl.
  - reflexivity.
  - destruct ent as [y|p].
    + destruct (eqDec x y) as [HEq|HNeq].
      * subst. exfalso. apply HIn. left. reflexivity.
      * rewrite IH.
        { reflexivity. }
        { apply validInvertV with y, HVal. }
        { intros HIn'. apply HIn. right. apply HIn'. }
    + destruct (in_dec eqDec x (Fr p)) as [HFree|HFree].
      * apply validInScopeP in HVal. exfalso. apply HIn. right.
        apply scope_in_ctx. apply HVal, HFree.
      * rewrite IH.
        { reflexivity. }
        { apply validInvertP with p, HVal. }
        { intros HIn'. apply HIn. right. apply HIn'. }
Qed.

Lemma removeFromScope_incl : forall (v:Type) (e:Eq v) (G:Ctx v) (x:v),
  removeFromScope x G <= G.
Proof.
  intros v e G x. induction G as [|ent G' IH]; simpl.
  - apply incl_refl.
  - destruct ent as [y|p].
    + destruct (eqDec x y) as [HEq|HNeq].
      * subst. intros u Hu. right. apply IH, Hu.
      * intros u [Hu|Hu].
        { rewrite <- Hu. left. reflexivity. }
        { right. apply IH, Hu. }
    + destruct (in_dec eqDec x (Fr p)) as [HFree|HFree].
      * intros u Hu. right. apply IH, Hu.
      * intros u [Hu|Hu].
        { rewrite <- Hu. left. reflexivity. }
        { right. apply IH, Hu. }
Qed.

Arguments removeFromScope_incl {v} {e}.

Lemma remove_characV : forall (v:Type) (e:Eq v) (G:Ctx v) (x:v),
  forall (y:v), Var y :: removeFromScope x G <-> Var y :: G /\ x <> y.
Proof.
  intros v e G x. induction G as [|ent G' IH]; simpl; intros y.
  - split.
    + intros H. contradiction.
    + intros [H1 H2]. contradiction.
  - split.
    + destruct ent as [z|p].
      * destruct (eqDec x z) as [HEq|HNeq].
        { subst. intros HIn. split.
          - right. apply (removeFromScope_incl G' z), HIn.
          - apply IH, HIn. }
        { intros [HIn|HIn].
          - inversion HIn. subst. split.
            + left. reflexivity.
            + apply HNeq.
          - split.
            + right. apply IH, HIn.
            + apply IH, HIn. }
      * destruct (in_dec eqDec x (Fr p)) as [HFree|HFree].
        { intros HIn. split.
          - right. apply IH, HIn.
          - apply IH, HIn. }
        { intros [HIn|HIn].
          - inversion HIn.
          - split.
            + right. apply IH, HIn.
            + apply IH, HIn. }
    + destruct ent as [z|p].
      * destruct (eqDec x z) as [HEq|HNeq].
        { subst. intros [[HEq|HIn] HNeq].
          - apply IH. split.
            + inversion HEq. subst. contradiction.
            + apply HNeq.
          - apply IH. split.
            + apply HIn.
            + apply HNeq. }
        { intros [[HEq|HIn] HNeq'].
          - inversion HEq. subst. left. reflexivity.
          - right. apply IH. split.
            + apply HIn.
            + apply HNeq'. }
      * destruct (in_dec eqDec x (Fr p)) as [HFree|HFree].
        { intros [[HEq|HIn] HNeq].
          - inversion HEq.
          - apply IH. split.
            + apply HIn.
            + apply HNeq. }
        { intros [[HEq|HIn] HNeq].
          - inversion HEq.
          - right. apply IH. split.
            + apply HIn.
            + apply HNeq. }
Qed.

Lemma remove_characP : forall (v:Type) (e:Eq v) (G:Ctx v) (x:v),
  forall (p:P v), Prp p :: removeFromScope x G <-> Prp p :: G /\ ~ x :: Fr p.
Proof.
  intros v e G x. induction G as [|ent G' IH]; simpl; intros p.
  - split.
    + intros H. contradiction.
    + intros [H1 H2]. contradiction.
  - split.
    + destruct ent as [y|q].
      * destruct (eqDec x y) as [HEq|HNeq].
        { subst. intros HIn. split.
          - right. apply IH, HIn.
          - apply IH, HIn. }
        { intros [HIn|HIn].
          - inversion HIn.
          - split.
            + right. apply IH, HIn.
            + apply IH, HIn. }
      * destruct (in_dec eqDec x (Fr q)) as [HFree|HFree].
        { intros HIn. split.
          - right. apply IH, HIn.
          - apply IH, HIn. }
        { intros [HIn|HIn].
          - inversion HIn. subst. split.
            + left. reflexivity.
            + apply HFree.
          - split.
            + right. apply IH, HIn.
            + apply IH, HIn. }
    + destruct ent as [y|q].
      * destruct (eqDec x y) as [HEq|HNeq].
        { subst. intros [[HEq|HIn] HFree].
          - inversion HEq.
          - apply IH. split.
            + apply HIn.
            + apply HFree. }
        { intros [[HEq|HIn] HFree].
          - inversion HEq.
          - right. apply IH. split.
            + apply HIn.
            + apply HFree. }
      * destruct (in_dec eqDec x (Fr q)) as [HFree|HFree].
        { intros [[HEq|HIn] HFree'].
          - inversion HEq. subst. contradiction.
          - apply IH. split.
            + apply HIn.
            + apply HFree'. }
        { intros [[HEq|HIn] HFree'].
          - inversion HEq. subst. left. reflexivity.
          - right. apply IH. split.
            + apply HIn.
            + apply HFree'. }
Qed.
(*
Lemma removeStillValid : forall (v:Type) (e:Eq v) (G:Ctx v) (x:v),
  CtxVal G -> CtxVal (removeFromScope x G).
Proof.
  intros v e G x. induction G as [|ent G' IH]; intro HVal.
  - constructor.
  - destruct ent as [y|p].
    + destruct (eqDec x y) as [HEq|HNeq] eqn:E.
      * subst. simpl. rewrite E. apply IH. apply validInvertV with y,HVal.
      * simpl. rewrite E.

Show.
*)
