Set Implicit Arguments.
Require Import List.

Print List. (* ooops this prints the whole module *)
Print list.
(*
Inductive list (A : Type) : Type :=
  | nil : list A 
  | cons : A -> list A -> list A
*)

Check list_ind.
(*

forall (A : Type) (P : list A -> Prop),
  P nil -> (forall (a : A) (l : list A), P l -> P (a :: l)) ->
  forall l : list A, P l
*)

Definition first_two (A:Type)(l:list A): list A :=
  match l with
    | nil         => l
    | cons a nil  => l
    | a::b::ls    => a::b::nil
  end.

Eval compute in first_two (2::3::4::5::nil).
Eval compute in first_two (2::7::nil).
Eval compute in first_two (6::nil).
Eval compute in first_two nil(A:=nat).

Fixpoint take (A:Type)(n:nat)(l:list A): list A :=
  match n with
    | 0         => nil
    | S p       =>
      match l with
        | nil   => nil
        | l::ls => l::take p ls
      end
  end.

Eval compute in take 3 (0::1::2::3::4::5::6::nil).
Eval compute in take 10 (0::1::2::3::4::5::6::nil).
Eval compute in take 2 (0::1::2::3::4::5::6::nil).
Eval compute in take 1 (0::1::2::3::4::5::6::nil).
Eval compute in take 0 (0::1::2::3::4::5::6::nil).

Fixpoint map (A:Type)(B:Type)(f:A->B)(l:list A): list B :=
  match l with
    | nil     => nil
    | l::ls   => (f l)::map f ls
  end.

Eval compute in map (fun x => 2*x) (0::1::2::3::4::5::6::nil).



