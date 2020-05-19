Definition L1 : bool <> nat.
Proof.
Admitted.


(* bool = nat type-checks since bool and nat have same sort Set                 *)
(*
Check bool.
Check nat.
*)

(* This is going to be true for bool but not for nat.                          *)
Definition P1 (X:Type) : Prop := forall (x y z:X), x = y \/ x = z \/ y = z.

Definition L2 : P1 bool.
Proof.
    unfold P1. intros x y z. destruct x; destruct y; destruct z.
    - left. reflexivity.
    - left. reflexivity.
    - right. left. reflexivity.
    - right. right. reflexivity.
    - right. right. reflexivity.
    - right. left. reflexivity.
    - left. reflexivity.
    - left. reflexivity.
Qed.

Definition L3 : ~ (0 = 1 \/ 0 = 2 \/ 1 = 2).
Proof.
    intros [H|[H|H]]; inversion H.
Qed.

Definition L4 : ~ P1 nat.
Proof.
    unfold P1, not. intros H. apply L3. apply H.
Qed.

Definition L5 : bool <> nat.
Proof.
    intros H. apply L4. rewrite <- H. apply L2.
Qed.

(*
Check True. (* Prop *)
Check unit. (* Set  *)
Check bool. (* Set  *)
*)

(* Different sorts but still seems ok                                           *)
Definition L6 : bool <> True.
Proof.
Admitted.

Definition L7 : bool <> unit.
Proof.
Admitted.

(* true for unit but not for bool.                                              *)
Definition P2 (X:Type) : Prop := forall (x y:X), x = y.

Definition L8 : P2 unit.
Proof.
    intros x y. destruct x; destruct y. reflexivity.
Qed.

Definition L9 : P2 unit.
Proof.
refine (
    fun (x y:unit) => 
        match x, y with
        | tt, tt    => eq_refl tt
        end
). 
Qed.

Definition L10 : true <> false.
Proof.
    intros H. inversion H.
Qed.


Definition L11 : ~ P2 bool.
Proof.
    unfold P2. intros H. apply L10. apply H.
Qed.

Definition L12 : bool <> unit.
Proof.
    intros H. apply L11. rewrite H. apply L9.
Qed.

Definition L13 : ~ ( (true,true) = (true,false) 
                  \/ (true,true) = (false,false) 
                  \/ (true, false) = (false, false)).
Proof. intros [H|[H|H]]; inversion H. Qed.


Open Scope type_scope.

Definition L14 : ~ P1 (bool * bool).
Proof.
    unfold P1. intros H. apply L13. apply H.
Qed.

Definition L15 : bool * bool <> bool.
Proof.
    intros H. apply L14. rewrite H. apply L2.
Qed.

