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

