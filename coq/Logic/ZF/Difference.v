Declare Scope ZF_Difference_scope.
Open    Scope ZF_Difference_scope.

Require Import Logic.ZF.Core.
Require Import Logic.ZF.Specification.

(* The set a \ b is made of those elements of a which do not belong to b.       *)
Definition difference (a b:U) : U := :{a | fun x => ~ x :< b }:.

Notation "a :\: b" := (difference a b)
  (at level 3, no associativity) : ZF_Difference_scope.

Proposition DiffCharac : forall (a b:U),
  forall x, x :< a:\:b <-> x :< a /\ ~ x :< b.
Proof.
  intros a b x. unfold difference. apply SpecCharac.
Qed.
