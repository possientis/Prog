Require Import Wf_nat PeanoNat Psatz. (* lt_wf =? lia *)

Check lt_wf.

Definition dec : forall (b:bool), {b = true} + {b = false} :=
    fun (b:bool) => 
        match b as b' return {b' = true} + {b' = false} with
        | true  => left  (eq_refl true)
        | false => right (eq_refl false)
        end.


Definition fac : nat -> nat.
Proof.
refine (Fix lt_wf (fun _ => nat)
    (fun (n:nat) =>
        fun (fac : forall (y:nat), y < n -> nat) =>
            if dec (n =? 0)
                then 1
                else n * (fac (n - 1) _)
)).
clear fac.
destruct n as [|n].
    - inversion e.
    - lia.
Defined.

Compute fac 8.

(* works but no idea why                                                        *)
Lemma fac_S (n:nat) : fac (S n) = (S n) * fac n.
Proof.
    unfold fac at 1; rewrite Fix_eq; fold fac.
    now replace (S n - 1) with n by lia.
    now intros x f g H; case dec; intros; rewrite ?H.
Qed.


