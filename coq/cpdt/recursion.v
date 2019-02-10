(*
Check nat_rect.
*)

Fixpoint nat_rect' 
    (P:nat -> Type) 
    (p:P 0) 
    (q:forall (n:nat), P n -> P (S n)) 
    (n:nat) : P n :=
    match n with 
    | 0     => p
    | S m   => q m (nat_rect' P p q m)
    end. 

Definition nat_rect'' := fix f
    (P:nat -> Type) 
    (p:P 0) 
    (q:forall (n:nat), P n -> P (S n))
    (n:nat) : P n :=
    match n with 
    | 0     => p
    | S m   => q m (f P p q m)
    end. 


Lemma rect_correct : forall 
    (P:nat -> Type) 
    (p:P 0) 
    (q:forall (n:nat), P n -> P (S n))
    (n:nat),
    nat_rect' P p q n = nat_rect'' P p q n.
Proof. reflexivity. Qed.

Definition nat_rect3 
    (P:nat -> Type) 
    (p:P 0) 
    (q:forall (n:nat), P n -> P (S n))
    : forall (n:nat), P n :=
    fix f (n:nat) : P n :=
        match n with 
        | 0     => p
        | S m   => q m (f m)
        end. 
Lemma rect3_correct : forall 
    (P:nat -> Type) 
    (p:P 0) 
    (q:forall (n:nat), P n -> P (S n))
    (n:nat),
    nat_rect3 P p q n = nat_rect' P p q n.
Proof. 
    intros P p q. induction n as [|n IH]. 
    - reflexivity.
    - simpl. rewrite IH. reflexivity.
Qed.

 
 
Definition nat_ind' (P:nat -> Prop) := nat_rect' P. 
Definition nat_rec' (P:nat -> Set)  := nat_rect' P.

(*
Check nat_ind'.
Check nat_rec'.
*)

Lemma plus_n_0' : forall (n:nat), plus n 0 = n.
Proof.
    apply nat_ind'.
    - reflexivity.
    - intros n IH. simpl. rewrite IH. reflexivity.
Qed.

(*
Check nat_rec'.
nat_rec : forall P : nat -> Set,
    P 0 -> 
    (forall n : nat, P n -> P (S n)) -> 
    forall n : nat, P n
*)

Lemma nat_rec_init : 
    forall (P:nat -> Set),
    forall (p:P 0),
    forall (q: forall n, P n -> P (S n)),
    nat_rec' P p q 0 = p.
Proof. reflexivity. Qed.


Lemma nat_rec_inc : 
    forall (P:nat -> Set),
    forall (p:P 0),
    forall (q: forall n, P n -> P (S n)),
    forall (n:nat),
    nat_rec' P p q (S n) = q n (nat_rec' P p q n).
Proof. reflexivity. Qed.


Definition plus': nat -> nat -> nat :=
    nat_rec' (fun _ => nat -> nat) (fun m => m) (fun _ f m => S (f m)).

Lemma plus_0_n' : forall (n:nat), plus' 0 n = n.
Proof. reflexivity. Qed.

Lemma plus_Sn_m' : forall (n m:nat), plus' (S n) m = S (plus' n m).
Proof. reflexivity. Qed.

Lemma plus'_correct : forall (n m:nat), plus' n m = plus n m.
Proof.
    apply (nat_ind' (fun n => forall (m:nat), plus' n m = plus n m)); 
    intros n; simpl.
    - unfold plus'. unfold nat_rec'. unfold nat_rect'. reflexivity.
    - intros IH m. rewrite plus_Sn_m', IH. reflexivity.
Qed.

