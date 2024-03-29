Require Import List.
Import ListNotations.

Require Import Logic.Class.Eq.
Require Import Logic.Func.Identity.
Require Import Logic.Axiom.Extensionality.

Require Import Logic.Fol.Syntax.

(* xs represents the list of variables which are deemed 'bound'                 *)
Definition h_ (v w:Type) (e:Eq v) (f g:v -> w) (xs : list v) (x:v) : w :=
    match in_dec eqDec x xs with
    | left _    => f x
    | right _   => g x
    end.

Arguments h_ {v} {w} {e}.

(* Notion of 'dual substitution of variable, but defined in terms of the list   *)
(* xs of variables which are deemed bound, rather than free.                    *)
Fixpoint dmap_ (v w:Type) (e:Eq v) (f g:v -> w) (xs:list v) (p:P v) : P w :=
    match p with
    | Bot       => Bot
    | Elem x y  => Elem (h_ f g xs x) (h_ f g xs y) 
    | Imp p1 p2 => Imp (dmap_ v w e f g xs p1) (dmap_ v w e f g xs p2)
    | All x p1  => All (f x) (dmap_ v w e f g (x :: xs) p1)     (* x now bound  *)
    end.

Arguments dmap_ {v} {w} {e}.

Definition dmap (v w:Type) (e:Eq v) (f g:v -> w) (p:P v) : P w :=
    dmap_ f g [] p.

Arguments dmap {v} {w} {e}.

Lemma dmap_id_ : forall (v:Type) (e:Eq v) (xs:list v) (p:P v),
    dmap_ id id xs p = p.
Proof.
    intros v e xs p. revert xs.
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
