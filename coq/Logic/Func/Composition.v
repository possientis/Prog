Require Import Logic.Axiom.Extensionality.

Require Import Logic.Func.Identity.

Declare Scope Composition_scope.

(* we are running out of operator symbols. Using ';' for composition in the     *)
(* usual sense of '.', so 'g ; f' means f is applied first                      *)

Definition comp (v w u:Type) (g:w -> u) (f:v -> w) (x:v) : u := g (f x).

Arguments comp {v} {w} {u} _ _ _.

Notation "g ; f" := (comp g f) 
    (at level 60, right associativity) : Composition_scope.

Open Scope Composition_scope.

Lemma comp_assoc : forall (a b c d: Type) (f:a -> b) (g:b -> c) (h:c -> d),
  h ; (g ; f) = (h ; g) ; f.
Proof.
  intros a b c d f g h. apply extensionality. intros x. reflexivity.
Qed.

Lemma comp_id_left : forall (a b: Type) (f:a -> b), 
  id ; f = f.
Proof.
  intros a b f. apply extensionality. intros x. reflexivity.
Qed.

Lemma comp_id_right : forall (a b: Type) (f:a -> b), 
  f ; id = f.
Proof.
  intros a b f. apply extensionality. intros x. reflexivity.
Qed.
