Require Import List.

Inductive tree (a:Set) : Set :=
| Node : a -> list (tree a) -> tree a
.

Arguments Node {a} _ _.

(* When attempting to define fmap in the natural way with equation:           *)
(* fmap f (Node x ts) = Node (f x) (map (fmap f) ts)                          *)
(* we encountered failures which we could not explain. However, if we define  *)
(* map differently, it appears we can be successful:                          *)

Definition map (a b:Set) (f:a -> b) : list a -> list b :=
    fix g (xs:list a) : list b := 
        match xs with
        | nil       => nil
        | x :: xs   => f x :: g xs
        end.

Arguments map {a} {b} _ _.


Fixpoint fmap (a b:Set) (f:a -> b) (t:tree a) : tree b :=
    match t with
    | Node x ts  => Node (f x) (map (fmap a b f) ts)
    end.

Arguments fmap {a} {b} _ _. 

(* Everything is so much simpler now                                          *)
Lemma fmap_check1 : forall (a b:Set) (f:a -> b) (x:a),
    fmap f (Node x nil) = Node (f x) nil.
Proof. reflexivity. Qed.

Lemma fmap_check2 : forall (a b:Set) (f:a -> b) (x:a) (ts:list (tree a)),
    fmap f (Node x ts) = Node (f x) (map (fmap f) ts).
Proof. reflexivity. Qed.


(* Note that we should probably also define fmap with a different style       *)
(* as this is likely to make any future development easier also               *)
Definition fmap' (a b:Set) (f:a -> b) : tree a -> tree b :=
    fix g (t:tree a) : tree b :=
        match t with
        | Node x ts => Node (f x) (map g ts)
        end.

Arguments fmap' {a} {b} _ _. 

Fixpoint All (a:Set) (P:a -> Prop) (xs:list a) : Prop :=
    match xs with
    | nil       => True
    | cons x xs => P x /\ All a P xs
    end. 


Arguments All {a} _ _.

(* instead of mutually inductive definition, we shall used nested induction   *)
Fixpoint tree_nested_ind (a:Set) (P:tree a -> Prop)
    (p:forall (x:a) (ts:list (tree a)), All P ts -> P (Node x ts))
    (t:tree a) : P t :=
        match t with
        | Node x ts     => p x ts 
            ((fix all (ts':list (tree a)) : All P ts' :=
                match ts' with
                | nil       => I
                | cons t ts => conj (tree_nested_ind a P p t) (all ts)
                end) ts)
        end.

(* This second induction principle can be established from the first          *)
Definition tree_nested_ind2 (a:Set) (P:tree a-> Prop)
    (pnil: forall (x:a), P (Node x nil))
    (pcons: forall (x:a) (t:tree a) (ts:list (tree a)), 
        P t -> P (Node x ts) -> P (Node x (t :: ts)))
    (t:tree a) : P t.
Proof.
    apply tree_nested_ind. intros x. induction ts as [|t' ts IH].
    - intros. apply pnil.
    - intros [H0 H1]. apply pcons.
        + assumption.
        + apply IH. assumption.
Qed.


Lemma fmap_equal : forall (a b:Set) (f:a -> b) (t:tree a), fmap f t = fmap' f t.
Proof. 
    intros a b f. apply tree_nested_ind2.
    - reflexivity.
    - intros x t ts H1 H2. simpl in H2. injection H2. clear H2. intros H2.
      simpl. rewrite <- H1, <- H2. reflexivity.
Qed.

(* Again, we are now able to write down a natural definition of fold          *)
Fixpoint fold (a b:Set) (f:a -> list b -> b) (t:tree a) : b :=
    match t with
    | Node x ts => f x (map (fold a b f) ts)
    end.

Arguments fold {a} {b} _ _.

(* In the same spirit, we should probably rather define:                      *)
Definition fold' (a b:Set) (f:a -> list b -> b): tree a -> b :=
    fix g (t:tree a) : b :=
        match t with
        | Node x ts => f x (map g ts)
        end.

Arguments fold' {a} {b} _ _.

Lemma fold_equal : forall (a b:Set) (f:a -> list b -> b) (t:tree a), 
    fold f t = fold' f t.
Proof. 
    intros a b f. apply tree_nested_ind2.
    - reflexivity.
    - intros x t ts H1 H2. simpl.

Show.
