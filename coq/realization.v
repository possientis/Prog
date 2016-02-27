Require Import ZArith.

Section realization.
  Variables A B: Set.
  Let spec: Set := (((A->B)->B)->B)->A->B.
  Let realization: spec
    := fun (f:((A->B)->B)->B) (a:A) => f (fun g => g a).

  Definition nat_fun_to_Z_fun : Set := (nat->nat)->Z->Z.

  Definition absolute_fun : nat_fun_to_Z_fun :=
    fun f z => Z_of_nat (f (Zabs_nat z)).
  Definition always_0: nat_fun_to_Z_fun :=
    fun _ _ => 0%Z.
  Definition to_marignan: nat_fun_to_Z_fun :=
    fun _ _ => 1515%Z.
  Definition ignore_f: nat_fun_to_Z_fun :=
    fun _ z => z.
  Definition from_marignan: nat_fun_to_Z_fun :=
    fun f _ => Z_of_nat (f 1515%nat).

End realization.

