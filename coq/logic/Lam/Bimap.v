Require Import List.
Import ListNotations.

Require Import Eq.
Require Import Identity.
Require Import Extensionality.

Require Import Lam.T.

Definition h_ (v w:Type) (e:Eq v) (f g:v -> w) (xs : list v) (x:v) : w :=
    match in_dec e x xs with
    | left _    => g x
    | right _   => f x
    end.

Arguments h_ {v} {w}.

Fixpoint bimap_ (v w:Type) (e:Eq v) (f g:v -> w) (t:T v) (xs:list v) : T w :=
    match t with
    | Var x     => Var (h_ e f g xs x) 
    | App t1 t2 => App (bimap_ v w e f g t1 xs) (bimap_ v w e f g t2 xs)
    | Lam x t1  => Lam (g x) (bimap_ v w e f g t1 (x :: xs))
    end.

Arguments bimap_ {v} {w}.

Definition bimap (v w:Type) (e:Eq v) (f g:v -> w) (t:T v) : T w :=
    bimap_ e f g t [].

Arguments bimap {v} {w}.

Lemma bimap_id_ : forall (v:Type) (e:Eq v) (t:T v) (xs:list v),
    bimap_ e id id t xs = t.
Proof.
    intros v e t.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; intros xs; simpl.
    - unfold h_. destruct (in_dec e x xs) as [H|H]; reflexivity.
    - rewrite IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.

Lemma bimap_id : forall (v:Type) (e:Eq v), bimap e id id = @id (T v). 
Proof.
    intros v e. apply extensionality. intros x. 
    unfold bimap. apply bimap_id_.
Qed.
