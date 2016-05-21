Parameter A:Set.

Inductive List : nat -> Set :=
  | ListNil   : List 0
  | ListCons  : forall (n:nat), A -> List n -> List (S n).


Fixpoint semantics {n:nat}(l: List n) : list A :=
  match l with
    | ListNil           => nil
    | ListCons n a l'   => (cons a (semantics l'))
  end.

Definition simple {n:nat}(l: List n) : nat :=
  match l with
    | ListNil         => 0
    | ListCons n a l' => 1
  end.

Lemma onlyList0: forall x:List 0,
  x = ListNil.
Proof.
 intro x.
 pose (g:= fun (n:nat)(l: List n) => 
        match l with
          | ListNil         => ListNil
          | ListCons n a l' => x
        end).

