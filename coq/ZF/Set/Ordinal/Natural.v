Require Import ZF.Class.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.

Export ZF.Set.Empty.

Proposition ZeroIsOrdinal : Ordinal :0:.
Proof.
  apply Ordinal.EquivCompat with :0:. 2: apply Class.Ordinal.ZeroIsOrdinal.
  apply EquivSym, ToClassOfEmptySet.
Qed.


