Require Import List.
Import ListNotations.

Require Import Eq.
Require Import Map.
Require Import Identity.
Require Import Composition.
Require Import Extensionality.

Require Import Lam.T.

Definition h_ (v w:Type) (e:Eq v) (f g:v -> w) (xs : list v) (x:v) : w :=
    match in_dec e x xs with
    | left _    => g x
    | right _   => f x
    end.

Arguments h_ {v} {w}.

Fixpoint dmap_ (v w:Type) (e:Eq v) (f g:v -> w) (t:T v) (xs:list v) : T w :=
    match t with
    | Var x     => Var (h_ e f g xs x) 
    | App t1 t2 => App (dmap_ v w e f g t1 xs) (dmap_ v w e f g t2 xs)
    | Lam x t1  => Lam (g x) (dmap_ v w e f g t1 (x :: xs))
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

(*
Lemma dmap_comp_:forall(v w u:Type)(e:Eq v)(e':Eq w)(f g:v -> w)(f' g':w -> u),
    forall (t:T v) (xs:list v),
    dmap_ e (f' ; f) (g' ; g) t xs = dmap_ e' f' g' (dmap_ e f g t xs) (map g xs).
Proof.
    intros v w u e e' f g f' g' t.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; intros xs;
    unfold comp, dmap_, h_.
    - destruct (in_dec e x xs) as [H|H].
        + destruct (in_dec e' (g x) (map g xs)) as [H'|H'].
            { reflexivity. }
            { exfalso. apply H'. apply mapIn. exists x. split.
                { assumption. }
                { reflexivity. }
            }
        +  destruct (in_dec e' (f x) (map g xs)) as [H'|H'].
            {
 

Show.
*)

