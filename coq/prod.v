Set Implicit Arguments.
Require Import Arith.
Require Import List.


Print prod.
(* Inductive prod (A B : Type) : Type :=  pair : A -> B -> A * B *)

Print fst. (* fun (A B : Type) (p : A * B) => let (x, _) := p in x *)
Print snd. (* fun (A B : Type) (p : A * B) => let (_, y) := p in y *)

(* syntactic sugar as follows:

  prod A B -> A*B
  pair a b -> (a,b)

*)

Fixpoint split (A B:Type)(l : list (A*B)) : (list A)*(list B) :=
  match l with
    | nil       => (nil, nil)
    | a::ls     => let l' := split ls in ((fst a)::(fst l'), (snd a)::(snd l')) 
  end.

Eval compute in split ((1,2)::(3,4)::(5,6)::(7,8)::nil).

Fixpoint zip (A B: Type)(l1:list A)(l2: list B) : list (A*B) :=
  match l1, l2 with
    | nil, nil        => nil
    | nil, _          => nil
    |  _ , nil        => nil
    | a::l1', b::l2'  => (a,b)::zip l1' l2'
  end.

Eval compute in zip (0::2::4::6::nil) (1::3::5::7::nil).

Lemma zip_split: forall (A B:Type) (l: list (A*B)),
  zip (fst (split l)) (snd (split l)) = l.
Proof.
  intros A B l. elim l. simpl. reflexivity. clear l.
  intros a ls IH. simpl. rewrite IH. elim a. intros x y. 
  simpl. reflexivity.
Qed.

