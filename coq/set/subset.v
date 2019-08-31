Require Import set.
Require Import Exists.
Require Import Order.
 
Fixpoint subset_n (n:nat) : set -> set -> Prop :=
    match n with
    | 0     => (fun _  _    => True)
    | S n   => (fun xs ys   =>
        match xs with
        | Nil               => True
        | Cons x xs         =>
            subset_n n xs ys  (* xs <= ys *) 
        /\  Exists            (* there is y in ys such that x = y *) 
            (fun y => subset_n n x y /\ subset_n n y x)
            ys
        end)
    end.
              
(*
Lemma subset_n_Sn : forall (n:nat) (xs ys:set),
    order xs + order ys <= n -> (subset_n n xs ys <-> subset_n (S n) xs ys).
Proof.
    induction n as [|n IH].
    -

Show.
*)
