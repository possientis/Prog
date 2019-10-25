Require Import List.

Require Import Core.Set.

Definition decidable (p:set -> Prop) := forall (x:set), {p x} + {~ p x}.


(*
Definition foo (xs:list set) (p:set -> Prop) (H: decidable p) :
    { exists (x:set), In x xs /\ p x } + { ~ exists (x:set), In x xs /\ p x}.
Proof.
    induction xs as [|x xs IH].
    - admit.
    - destruct (H x) as [Hx|Hx].
        + left. exists x. split.
            { left. reflexivity. }
            { assumption. }
        + destruct IH as [IH|IH].
            { destruct IH. 


Show.
*)
