Require Import List.
Import ListNotations.

Require Import Eq.
Require Import Map.
Require Import Identity.
Require Import Composition.
Require Import Extensionality.

Require Import Lam.T.

(* xs represents the list of variables which are deemed 'bound'                 *)
Definition h_ (v w:Type) (e:Eq v) (f g:v -> w) (xs : list v) (x:v) : w :=
    match in_dec e x xs with
    | left _    => g x          (* x is deemed bound    -> g x                  *)
    | right _   => f x          (* x is deemed free     -> f x                  *)
    end.

Arguments h_ {v} {w}.

(* Notion of 'dual substitution of variable, but defined in terms of the list   *)
(* xs of variables which are deemed bound, rather than free.                    *)
Fixpoint dmap_ (v w:Type) (e:Eq v) (f g:v -> w) (t:T v) (xs:list v) : T w :=
    match t with
    | Var x     => Var (h_ e f g xs x) 
    | App t1 t2 => App (dmap_ v w e f g t1 xs) (dmap_ v w e f g t2 xs)
    | Lam x t1  => Lam (g x) (dmap_ v w e f g t1 (x :: xs))     (* x now bound  *)
    end.

Arguments dmap_ {v} {w}.

Definition dmap (v w:Type) (e:Eq v) (f g:v -> w) (t:T v) : T w :=
    dmap_ e f g t [].

Arguments dmap {v} {w}.

Lemma dmap_id_ : forall (v:Type) (e:Eq v) (t:T v) (xs:list v),
    dmap_ e id id t xs = t.
Proof.
    intros v e t.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; intros xs; simpl.
    - unfold h_. destruct (in_dec e x xs) as [H|H]; reflexivity.
    - rewrite IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.

Lemma dmap_id : forall (v:Type) (e:Eq v), dmap e id id = @id (T v). 
Proof.
    intros v e. apply extensionality. intros x. 
    unfold dmap. apply dmap_id_.
Qed.

(* There is no obvious result in relation to function composition               *)