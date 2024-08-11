Require Import Logic.Class.Eq.

Require Import Logic.List.Include.

Require Import Logic.Fol.Free.
Require Import Logic.Fol.Syntax.

Require Import Logic.Fol2.Context.
Require Import Logic.Fol2.Proof.

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

(*
Definition cutElim (v:Type) (e:Eq v) (G:Ctx v) (p q:P v) :

 :- p -> G;p :- q -> G :- q.
Proof.
  intros pr.
  induction pr as
    [G p' HVal HIncl
    |G x p' HScope HSeq IH
    |G p' q' HIncl  HSeq IH
    |G x y p HSeq IH
    |G p' q' HSeq IH
    |G p' q' HSeq1 IH1 ISeq2 IH2
    |G p' HSeq IH
    |G p' HVal HAxi
    |G x p HSeq IH
    |G x p HScope HSeq IH
    |G x y p HNeq HScope HSeq IH
    ].
  -

Show.
*)

