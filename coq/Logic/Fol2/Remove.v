Require Import List.

Require Import Logic.Class.Eq.

Require Import Logic.List.In.

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
