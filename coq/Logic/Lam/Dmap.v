Require Import List.
Import ListNotations.

Require Import Logic.Class.Eq.
Require Import Logic.Func.Identity.
Require Import Logic.Axiom.Extensionality.

Require Import Logic.Lam.Syntax.

(* xs represents the list of variables which are deemed 'bound'                 *)
Definition h_ (v w:Type) (e:Eq v) (f g:v -> w) (xs : list v) (x:v) : w :=
    match in_dec eqDec x xs with
    | left _    => f x          (* x is deemed bound    -> g x                  *)
    | right _   => g x          (* x is deemed free     -> f x                  *)
    end.

Arguments h_ {v} {w} {e}.

(* Notion of 'dual substitution of variable, but defined in terms of the list   *)
(* xs of variables which are deemed bound, rather than free.                    *)
Fixpoint dmap_ (v w:Type) (e:Eq v) (f g:v -> w) (t:T v) (xs:list v) : T w :=
    match t with
    | Var x     => Var (h_ f g xs x) 
    | App t1 t2 => App (dmap_ v w e f g t1 xs) (dmap_ v w e f g t2 xs)
    | Lam x t1  => Lam (f x) (dmap_ v w e f g t1 (x :: xs))     (* x now bound  *)
    end.

Arguments dmap_ {v} {w} {e}.

Definition dmap (v w:Type) (e:Eq v) (f g:v -> w) (t:T v) : T w :=
    dmap_ f g t [].

Arguments dmap {v} {w} {e}.

Lemma dmap_id_ : forall (v:Type) (e:Eq v) (t:T v) (xs:list v),
    dmap_ id id t xs = t.
Proof.
    intros v e t.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; intros xs; simpl.
    - unfold h_. destruct (in_dec eqDec x xs) as [H|H]; reflexivity.
    - rewrite IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.

Lemma dmap_id : forall (v:Type) (e:Eq v), dmap id id = @id (T v). 
Proof.
    intros v e. apply extensionality. intros x. 
    unfold dmap. apply dmap_id_.
Qed.

(* There is no obvious result in relation to function composition               *)
