Lemma eta_eq : forall (a b:Type) (f:a -> b), f = (fun (x:a) => f x).
Proof.
    intros a b f. reflexivity.
Qed.

Inductive Void : Type :=.

Definition absurd (a:Type) : Void -> a :=
    fun (x:Void) => match x with end.

Lemma absurd_unique1 : forall (a:Type) (f:Void -> a) (y:a) (x:Void), y = f x.
Proof.
    intros a f y x. inversion x.
Qed.


Lemma absurd_unique2 : forall (a:Type) (f:Void -> a),
(fun (x:Void) => f x) = (fun (x:Void) => match x with end).
Proof.
    intros a f. 

Show.


