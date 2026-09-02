Set Implicit Arguments.

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.


Inductive nat' : Set := O' | S'(_:nat').  (* alternative syntax *)


Inductive even : nat -> Prop :=
  | even_O  : even O
  | even_SS : forall n:nat, even n -> even (S (S n)).

Inductive list (A:Set) : Set :=
  | nil : list A
  | cons: A -> list A -> list A.
 
Inductive list' (A:Set) : Set := nil' | cons'(_:A)(_:list' A).

(* Variant is like Inductive but no recursive definitionof types *)

Inductive sum (A B: Set) : Set := left : A -> sum A B | right : B -> sum A B.

Inductive tree (A B:Set) : Set :=
  | node : A -> forest A B -> tree A B
  with forest (A B:Set) : Set :=
    | leaf    : B -> forest A B
    | cons''  : tree A B -> forest A B -> forest A B.

CoInductive stream (A:Set): Set :=
  | seq : A -> stream A -> stream A.

Definition head {A:Set}(x:stream A) : A := let (a,s):=x in a.
Definition tail {A:Set}(x:stream A) : stream A := let (a,s):=x in s.

CoInductive Eq {A:Set} : stream A -> stream A -> Prop := 
  eq: forall s1 s2: stream A, 
    head s1 = head s2 -> Eq (tail s1) (tail s2) -> Eq s1 s2.


Fixpoint add(n m:nat) (* {struct n} *): nat := 
  match n with
    | O   => m
    | S p => S (add p m)
  end.

Fixpoint add'(n m:nat) : nat :=
  match m with
    | O   => n
    | S p => S (add' n p)
  end.

Fixpoint nat_match
  {C:Set} (f0:C) (fS: nat -> C -> C) (n:nat) : C :=
    match n with
      | O     => f0
      | S p   => fS p (nat_match f0 fS p)
    end.

Fixpoint mod2 (n:nat) : nat :=
  match n with
    | O   => O
    | S p => match p with
              | O   => S O   
              | S q => mod2 q
            end
  end.

Eval compute in mod2 (S (S (S (S O)))).
Eval compute in mod2 (S (S (S (S (S O))))).

Fixpoint even' (n : nat) : Prop :=
  match n with
    | O   => True
    | S p => odd' p
  end
  with odd'(n : nat) : Prop :=
    match n with
      | O   => False
      | S p => even' p
    end.

Eval compute in even' (S (S (S (S O)))).
Eval compute in odd' (S (S (S (S O)))).
Eval compute in even' (S (S (S (S (S O))))).
Eval compute in odd' (S (S (S (S (S O))))).

CoFixpoint from (n : nat) : stream nat :=
  seq n (from (S n)).

Definition integers := from O.

Fixpoint sub (n:nat) : stream nat :=
  match n with
    | O   => integers
    | S p => tail (sub p)
  end.

Definition id (n:nat) : nat := head (sub n).

Eval compute in id O.
Eval compute in id (S O).
Eval compute in id( S (S O)).

Lemma same : forall n:nat, id n = n.
Proof.
  intro n. elim n.
    clear n. unfold id. simpl. reflexivity.
    clear n. intros n IH. unfold id. unfold id in IH.
    unfold sub. fold sub.  
Abort.

Eval compute in from O.
Eval compute in head (from O).
Eval compute in tail (from O).









