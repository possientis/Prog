(* Computational Primitives                                                     *)
(* 1. plain definition                                                          *)
(*      Definition (c:t) := e                                                   *)
(* 2. lambda abstraction                                                        *)
(*      fun (x:t) => e                                                          *)
(* 3. recursive abstraction                                                     *)
(*      fix f (x:t) := e (where f is free in e)                                 *)
(* 4. pattern match                                                             *)
(*      match x with                                                            *)
(*      | c1 x1 ... xn  => e1                                                   *)  
(*      | ...                                                                   *)
(*      end                                                                     *)
(* 5. let expression                                                            *)
(*      let x := e in e'                                                        *)


Definition not := fun (x : bool) => 
    match x with 
    | true => false 
    | false => true 
    end.

Definition plus := fix g (x:nat) := 
    fun (y:nat) =>
        match x with
        | 0     => y
        | S x'  => S (g x' y)
        end. 

Definition minus := fix g (x:nat) :=
    fun (y:nat) =>
        match x with
        | 0     => 0
        | S x'  => 
            match y with
            | 0     => x
            | S y'  => g x' y'
            end
        end. 

Definition swap := fun (a b:Type) => fun (p : a * b) =>
    match p with
    | (x,y) => (y,x)
    end.

Arguments swap {a} {b}.

Definition double := fix f (x:nat) :=
    match x with
    | 0     => 0
    | S x'  => S (S (f x'))
    end.

Fixpoint iter (a : Type) (f:a -> a) (n:nat) (x : a) : a :=
    match n with
    | 0     => x
    | S n   => f (iter a f n x)
    end.

(* Defining iter in terms of primitives                                         *)
Definition iter' := fun (a:Type) =>
    fun (f:a -> a) =>
        fix g (n:nat) := 
            match n with
            | 0     => fun x => x
            | S n   => fun x => f (g n x)
            end.

Arguments iter  {a}.
Arguments iter' {a}.

Lemma iter_correct : forall (a:Type) (f:a -> a) (n:nat) (x:a),
    iter f n x = iter' f n x.
Proof.
    intros a f n x. induction n as [|n IH].
    - reflexivity.
    - simpl. rewrite IH. reflexivity.
Qed.


Lemma check1 : not true = false.
Proof. reflexivity. Qed.

Lemma check2 : not false = true.
Proof. reflexivity. Qed.

Lemma check3 : plus 3 5 = 8. 
Proof. reflexivity. Qed.

Lemma check4 : minus 7 3 = 4.
Proof. reflexivity. Qed.

Lemma check5 : minus 3 7 = 0.
Proof. reflexivity. Qed.

Lemma check6 : swap (3,5) = (5,3).
Proof. reflexivity. Qed.

Lemma check7 : double 5 = 10.
Proof. reflexivity. Qed.

Lemma check8 : plus 1 = S.
Proof. reflexivity. Qed.

Lemma check9 : plus 2 = fun (x:nat) => S (S x).
Proof. reflexivity. Qed.

Lemma check10 : plus (minus 3 2) = S.
Proof. reflexivity. Qed.

Lemma check11 : (fun x => 1 + x) = S.
Proof. reflexivity. Qed.

Lemma check12 : (fun x => minus (3 + x) 2) = S. 
Proof. reflexivity. Qed.

Lemma check13 : iter S 2 = fun x => S (S x).
Proof. reflexivity. Qed.

