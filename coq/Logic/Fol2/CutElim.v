Require Import Logic.Class.Eq.

Require Import Logic.List.Include.

Require Import Logic.Fol.Free.
Require Import Logic.Fol.Syntax.

Require Import Logic.Fol2.Context.
Require Import Logic.Fol2.Proof.

Definition cutElim (v:Type) (e:Eq v) (G:Ctx v) (r:P v) (pr:G :- r):
  forall (p q:P v), r = p :-> q -> G :- p -> G :- q.
Proof.
  induction pr as
    [G r HVal HIncl
    |G x r HScope HSeq IH
    |G r1 r2 HIncl  HSeq IH
    |G x y r HSeq IH
    |G r1 r2 HSeq IH
    |G r1 r2 HSeq1 IH1 ISeq2 IH2
    |G r HSeq IH
    |G r HVal HAxi
    |G x r HSeq IH
    |G x r HScope HSeq IH
    |G x y r HNeq HScope HSeq IH
    ]; intros p q HEq pr.
  - rewrite HEq in pr. rewrite HEq. clear HEq.

Show.


(*
Definition remove_dup (v:Type) (e:Eq v) (G:Ctx v) (p q: P v) :
  G;p;p :- q -> G;p :- q.
Proof.
  intros pr. remember (G;p;p) as H eqn:E. revert G p E.
  induction pr as
    [G' p' HVal HIncl
    |G' x p' HScope HSeq IH
    |G' p' q' HIncl  HSeq IH
    |G' x y p' HSeq IH
    |G' p' q' HSeq IH
    |G' p' q' HSeq1 IH1 ISeq2 IH2
    |G' p' HSeq IH
    |G' p' HVal HAxi
    |G' x p' HSeq IH
    |G' x p' HScope HSeq IH
    |G' x y p' HNeq HScope HSeq IH
    ]; intros G p HEq.
  - inversion HEq. subst. refine (extract _ _).
    + apply validInvertP with p, HVal.
    + apply HIncl.
  - inversion HEq.
  - inversion HEq. subst. apply HSeq.
  - inversion HEq.
  - refine (deduct _).

Show.
*)

