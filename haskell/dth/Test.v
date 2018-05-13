Inductive Nat : Type := Zero : Nat  | Succ : Nat -> Nat.

Fixpoint plus (n m:Nat) : Nat :=
    match n with
    | Zero      => m
    | Succ n    => Succ (plus n m)
    end.

Inductive Vec : Type -> Nat -> Type :=
| VNil : forall (a:Type), Vec a Zero
| VCons: forall (a:Type) (n:Nat) (x:a) (xs:Vec a n), Vec a (Succ n)
.


Fixpoint replicate (a:Type) (n:Nat) (x:a) : Vec a n :=
    match n with
    | Zero      => VNil a
    | Succ n    => VCons a n x (replicate a n x)
    end.

Compute replicate.
(*
    = fix Ffix (x : Type) (x0 : Nat) (x1 : x) {struct x0} : Vec x x0 :=
      match x0 as c return (Vec x c) with
      | Zero => VNil x
      | Succ x2 => VCons x x2 x1 (Ffix x x2 x1)
      end
      : forall (a : Type) (n : Nat), a -> Vec a n
*)

Arguments replicate {a} _ _.

Definition replicate' := 
    fix f (a:Type) (n:Nat) (x:a) : Vec a n :=
        match n as n' return (Vec a n') with
        | Zero      => VNil a
        | Succ p    => VCons a p x (f a p x)
        end.

Check replicate'.

Arguments replicate' {a} _ _.

Lemma replicate_correct : forall (a:Type) (n:Nat) (x:a),
   replicate n x = replicate' n x.
Proof.
    intros a n x. induction n.
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
Qed.

Lemma Vec_Same : forall (a:Type) (n m:Nat), n = m -> Vec a n = Vec a m.
Proof. intros a n m H. rewrite H. reflexivity. Qed.


Definition cast (a b:Type) (p:a = b) (x:a) : b :=
    match p in _ = T return T with
    | eq_refl    => x
    end.

Arguments cast {a} {b} _ _.

Definition toVec (a:Type) (n m:Nat) (p:n = m) (x:Vec a n) : Vec a m :=
    cast (Vec_Same a n m p) x.

Lemma plus_0_n : forall (n:Nat), n = plus Zero n.
Proof. intros n. induction n; reflexivity. Qed.


Arguments VNil {a}.
Arguments VCons {a} {n} _ _.

