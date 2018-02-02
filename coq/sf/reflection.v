Require Import nat.
Require Import bool.
Require Import list.
Require Import In.
Require Import filter.
Require Import induction.

(* direct proof *)
Example even_24 : exists k, 24 = double k.
Proof. exists 12. reflexivity. Qed.

(* at boolean level, even simpler *)
Example even_24': evenb 24 = true.
Proof. reflexivity. Qed.

(* transporting proof to boolean level *)
Example even_24'' : exists k, 24 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.


Theorem filter_not_empty_In : forall (n:nat) (l:list nat),
    filter (eqb n) l <> [] -> In n l.
Proof.
    intros n l. induction l as [|x xs IH].
    - simpl. intros H. apply H. reflexivity.
    - simpl. destruct (eqb n x) eqn:H.
        + intros _. left. symmetry. apply eqb_semantics. exact H.
        + intros H'. right. apply IH. exact H'.
Qed.

(* heuristically, the binary predicate 'reflect' says that a proposition
   is equivalent to a boolean                                            
*)

Inductive reflect (P:Prop) : bool -> Prop :=
| reflectT : P  -> reflect P true
| reflectF : ~P -> reflect P false
.

Theorem iff_reflect : forall (P:Prop) (b:bool), 
    (P <-> b = true) -> reflect P b.
Proof.
    intros P b H. destruct b eqn:H'.
    - apply reflectT. apply H. reflexivity.
    - apply reflectF. intros Hp. apply H in Hp. inversion Hp.
Qed.


Theorem reflect_iff : forall (P:Prop) (b:bool),
    reflect P b -> (P <-> b = true).
Proof.
    intros P b H.
    induction H as [H1 IH1|H1 IH1].
    - split.
        + intros _. reflexivity.
        + intros _. exact H1.
    - split.
        + intros Hp. exfalso. apply H1. exact Hp.
        + intros H. inversion H.
Qed.


Lemma eqbP : forall (n m:nat), reflect (n = m) (eqb n m).
Proof.
    intros n m. apply iff_reflect. exact (eqb_semantics n m).
Qed.


Theorem filter_not_empty_In' : forall (n:nat) (l:list nat),
    filter (eqb n) l <> [] -> In n l.
Proof.
    intros n l. induction l as [|x xs IH].
    - simpl. intros H. apply H. reflexivity.
    - simpl. destruct (eqbP n x) as [H|H].
        + intros _. left. symmetry. exact H.
        + intros H'. right. apply IH. exact H'.
Qed.


    





