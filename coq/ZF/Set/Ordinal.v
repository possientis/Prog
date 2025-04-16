Require Import ZF.Class.
Require Import ZF.Class.Ordinal.
Require Import ZF.Set.
Require Import ZF.Set.Incl.

(* The class of all ordinals.                                                   *)
Definition Ordinal : Class := On.

(* Strict inclusion and set membership coincide on ordinals.                    *)
Proposition StrictInclIsElem : forall (a b:U), Ordinal a -> Ordinal b ->
  a :<: b <-> a :< b.
Proof.
  intros a b H1 H2. split; intros H3.
  - apply (StrictInclIsElem (toClass b)); try assumption.
    apply StrictInclFromClass. assumption.
  - apply StrictInclFromClass, (StrictInclIsElem (toClass b)); assumption.
Qed.

