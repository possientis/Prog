Require Import List.
Import ListNotations.

Require Import Eq.
Require Import Identity.
Require Import Extensionality.

Require Import Fol.P.

(* xs represents the list of variables which are deemed 'bound'                 *)
Definition h_ (v w:Type) (e:Eq v) (f g:v -> w) (xs : list v) (x:v) : w :=
    match in_dec eqDec x xs with
    | left _    => g x
    | right _   => f x
    end.

Arguments h_ {v} {w} {e}.

(* Notion of 'dual substitution of variable, but defined in terms of the list   *)
(* xs of variables which are deemed bound, rather than free.                    *)
Fixpoint dmap_ (v w:Type) (e:Eq v) (f g:v -> w) (p:P v) (xs:list v) : P w :=
    match p with
    | Bot       => Bot
    | Elem x y  => Elem (h_ f g xs x) (h_ f g xs y) 
    | Imp p1 p2 => Imp (dmap_ v w e f g p1 xs) (dmap_ v w e f g p2 xs)
    | All x p1  => All (g x) (dmap_ v w e f g p1 (x :: xs))     (* x now bound  *)
    end.

Arguments dmap_ {v} {w} {e}.

Definition dmap (v w:Type) (e:Eq v) (f g:v -> w) (p:P v) : P w :=
    dmap_ f g p [].

Arguments dmap {v} {w} {e}.

Lemma dmap_id_ : forall (v:Type) (e:Eq v) (p:P v) (xs:list v),
    dmap_ id id p xs = p.
Proof.
    intros v e p.
    induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1]; intros xs; simpl.
    - reflexivity.
    - unfold h_. 
      destruct (in_dec eqDec x xs) as [H1|H1], (in_dec eqDec y xs) as [H2|H2];
      reflexivity. 
    - rewrite IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.

Lemma dmap_id : forall (v:Type) (e:Eq v), dmap id id = @id (P v). 
Proof.
    intros v e. apply extensionality. intros x. 
    unfold dmap. apply dmap_id_.
Qed.

(* There is no obvious result in relation to function composition               *)

