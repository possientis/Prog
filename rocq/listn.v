Parameter A:Set.

Inductive List : nat -> Set :=
  | ListNil   : List 0
  | ListCons  : forall (n:nat), A -> List n -> List (S n).


Definition Pred {n:nat}(l: List n) :=
  match n (* return List n -> Prop *) with
    | 0 => fun l => l = ListNil
    | _ => fun _ => True
  end l.

Lemma general : forall {n:nat} (l:List n), Pred l.  
Proof.
  intros n l. unfold Pred. destruct l; auto.  
Qed.




(*
fun (n : nat) (l : List n) =>
match l as l0 in (List n0) return (Pred l0) with
| ListNil => eq_refl
| ListCons _ _ _ => I
end
*)

Definition proof {n:nat}(l: List n) :=
  match l as l0 in (List n0) return (Pred l0) with
    | ListNil => eq_refl
    | ListCons _ _ _ => I
  end.


Lemma onlyList0: forall x:List 0,
  x = ListNil.
Proof.
  intro x. apply general with (l:=x).
Qed.


Lemma l0_gen (n:nat) (l: List n) :
  match n with
    | 0 => fun l => l = ListNil
    | _ => fun _ => True
  end l.
Proof.
  now destruct l.
Qed.


Require Coq.Vectors.Vector.

Lemma l0_gen' A n (v : Vector.t A n) :
  match n (* return Vector.t A n -> Prop *) with
    | 0 => fun v => v = @Vector.nil A
    | _ => fun _ => True
  end v.
Proof.
  now destruct v.
Qed.




