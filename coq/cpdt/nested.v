Require Import List.
Require Import Arith.

(* We are using the type we are defining as the argument of parameterized     *)
(* type family: this is an example of 'nested inductive type'                 *)

Inductive tree (a:Set) : Set :=
| Node : a -> list (tree a) -> tree a
.

Arguments Node {a} _ _.

(* This inductive type is too complicated for coq. The default recursive      *)
(* principle is not useful.                                                   *)
(*                                                                            *)
(* Check tree_rect.                                                           *)
(*                                                                            *)
(* So we need to write our own induction principle. We shall need             *)

Fixpoint All' (a:Set) (P:a -> Prop) (xs:list a) : Prop :=
    match xs with
    | nil       => True
    | x :: xs   => P x /\ All' a P xs
    end. 

Arguments All' {a} _ _.

(* Let us define All in a slightly different way.                             *)

Definition All (a:Set) (P:a -> Prop) : list a -> Prop :=
    fix g (xs:list a) : Prop :=
        match xs with
        | nil       => True
        | x :: xs   => P x /\ g xs
        end.  

Arguments All {a} _ _.

Lemma All_same : forall (a:Set) (P:a -> Prop) (xs:list a), 
    All P xs <-> All' P xs.
Proof.
    intros a P. induction xs as [|x xs IH].
    - reflexivity.
    - destruct IH as [H1 H2]. split; simpl; 
      intros [H3 H4]; split; try (assumption).
        + apply H1. assumption.
        + apply H2. assumption.
Qed.


(* This definition should be fine but is rejected by Coq                      *)
(* Whether we use All or All' in the below makes no difference                *)

(*
   "Recursive call to tree_nest_ind has principal argument equal to 
   't' instead of 'ts0'" 

Fixpoint tree_nested_ind (a:Set) (P:tree a -> Prop) 
    (p:forall (x:a) (ts:list (tree a)), All P ts -> P (Node x ts))
    (t:tree a) {struct t} 
    : P t :=
        match t with 
        | Node x ts => p x ts (all a P p ts) 
        end
with all (a:Set) (P:tree a -> Prop) 
         (p:forall (x:a) (ts:list (tree a)), All P ts -> P (Node x ts))
         (ts:list (tree a)) {struct ts}
         : All P ts :=
             match ts with
             | nil          => I
             | cons t ts    => conj (tree_nested_ind a P p t) (all a P p ts)
             end
.
                                                                              *)



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


(* This has nothing to do with 'tree a' but since 'tree a' contains a list... *)
Fixpoint map' (a b:Set) (f:a -> b) (xs:list a) : list b :=
    match xs with
    | nil       => nil
    | x :: xs =>  f x :: map' a b f xs
    end.

Arguments map' {a} {b} _ _.

(* Once again, let us try and provide a slightly different definition for map *)

Definition map (a b:Set) (f:a -> b) : list a -> list b :=
    fix g (xs:list a) : list b := 
        match xs with
        | nil       => nil
        | x :: xs   => f x :: g xs
        end.

Arguments map {a} {b} _ _.


Lemma map_same : forall (a b:Set) (f:a -> b) (xs:list a),
    map f xs = map' f xs.
Proof.
    intros a b f. induction xs as [|x xs IH].
    - reflexivity.
    - simpl. rewrite IH. reflexivity.
Qed.

(* We define All and All' without visible benefit. We shall now see that      *)
(* defining map instead of map' bring a significant benefit, namely the       *)
(* following definition of fmap succeeds for map but fails for map':          *)

Fixpoint fmap (a b:Set) (f:a -> b) (t:tree a) : tree b :=
    match t with
    | Node x ts  => Node (f x) (map (fmap a b f) ts)
    end.

Arguments fmap {a} {b} _ _. 


(* This is a lot nicer than defining fmap with nested recursion as follows:   *)
Fixpoint fmap' (a b:Set) (f:a -> b) (t:tree a) : tree b :=
    match t with
    | Node x ts     => Node (f x) 
        ((fix g (ts':list (tree a)) : list (tree b) :=
            match ts' with
            | nil       => nil
            | cons t ts => cons (fmap' a b f t) (g ts)
            end) ts)  

    end.

Arguments fmap' {a} {b} _ _. 

(* We want to check that fmap and fmap's are the same things and the only     *)
(* realistic tool for this is our induction principle. However, our induction *)
(* formula will be 'All (fun t => fmap f t = fmap' f t) ts', i.e. the two     *)
(* functions (fmap f) and (fmap' f) coincide on ts. We need to be able to     *)
(* conclude that: map (fmap f) ts = map (fmap' f) ts                          *)

Lemma All_map : forall (a b:Set) (f g:a -> b) (xs: list a),
    All (fun x => f x = g x) xs -> map f xs = map g xs.
Proof.
    intros a b f g xs. induction xs as [| x xs IH].
    - reflexivity.
    - intros [H1 H2]. simpl. rewrite H1. apply IH in H2. rewrite H2. reflexivity.
Qed.

Lemma fmap_same: forall (a b:Set) (f:a -> b) (t:tree a), 
    fmap f t = fmap' f t.
Proof.
    intros a b f. apply tree_nested_ind. intros x ts IH. simpl.
    fold (map (fmap' f) ts). apply All_map in IH. rewrite IH. reflexivity.
Qed.

(* Another definition which succeeds with map but fails with map'             *)
Fixpoint fold' (a b:Set) (f:a -> list b -> b) (t:tree a) : b :=
    match t with 
    | Node x ts     => f x (map (fold' a b f) ts)
    end.

Arguments fold' {a} {b} _ _.

(* However, in the spirit of All vs All' and map vs map' we should define     *)
Definition fold (a b:Set) (f:a -> list b -> b): tree a -> b :=
    fix g (t:tree a) : b :=
        match t with
        | Node x ts => f x (map g ts)
        end.

Arguments fold {a} {b} _ _.

Lemma fold_same : forall (a b:Set) (f:a -> list b -> b) (t:tree a), 
    fold f t = fold' f t.
Proof. 
    intros a b f. apply tree_nested_ind. intros x ts IH. simpl.
    apply All_map in IH. rewrite IH. reflexivity.
Qed.


(* We could have defined fold using nested recursion                          *)
Fixpoint fold'' (a b:Set) (f:a -> list b -> b) (t:tree a) : b :=
    match t with 
    | Node x ts     => f x 
        ((fix g (ts': list (tree a)) : list b :=
            match ts' with
            | nil       => nil
            | t :: ts => cons (fold'' a b f t) (g ts)
            end) ts) 
    end.

Arguments fold'' {a} {b} _ _.

Lemma fold_same' : forall (a b:Set) (f:a -> list b -> b) (t:tree a), 
    fold f t = fold'' f t.
Proof. 
    intros a b f. apply tree_nested_ind. intros x ts IH. simpl.
    fold (map (fold'' f) ts). apply All_map in IH. rewrite IH.
    reflexivity.
Qed.

Definition fmap_callback (a b:Set) (f:a -> b) : a -> list (tree b) -> tree b :=
    fun (x:a) (ts : list (tree b)) => Node (f x) ts.

Arguments fmap_callback {a} {b} _ _ _.

Lemma fmap_is_a_fold : forall (a b:Set) (f:a -> b) (t:tree a), 
    fmap f t = fold (fmap_callback f) t.
Proof.
    intros a b f. apply tree_nested_ind. intros x ts IH. simpl.
    unfold fmap_callback at 1. apply All_map in IH. rewrite <- IH.
    reflexivity.
Qed.

Fixpoint sum (ls:list nat) : nat :=
    match ls with
    | nil       => 0
    | n :: ns   => plus n (sum ns)
    end.


(* Another definition which succeeds with map but fails with map'             *)
Fixpoint tree_size' (a:Set) (t:tree a) : nat :=
    match t with
    | Node _ ts     => S (sum (map (tree_size' a) ts))
    end.

Arguments tree_size' {a} _.

(* Another definition which succeeds with map but fails with map'             *)
Definition tree_size (a:Set) : tree a -> nat :=
    fix g (t:tree a) : nat :=
        match t with
        | Node _ ts => S (sum (map g ts))
        end.

Arguments tree_size {a} _.

Lemma tree_size_same : forall (a:Set) (t:tree a),
    tree_size t = tree_size' t.
Proof.
    intros a. apply tree_nested_ind. intros x ts IH. simpl.
    apply All_map in IH. rewrite IH. reflexivity.
Qed.

(* Some notion is tree splicing. The point is that preserves sizes            *)
Fixpoint tree_splice' (a:Set) (t1 t2:tree a) : tree a :=
    match t2 with
    | Node x nil        => Node x (t1 :: nil)
    | Node x (t :: ts)  => Node x (tree_splice' a t1 t :: ts)
    end.

Arguments tree_splice' {a} _ _.

(* In the same spirit                                                         *)
Definition tree_splice (a:Set) (t1:tree a) : tree a -> tree a :=
    fix g (t:tree a) : tree a :=
        match t with
        | Node x nil        => Node x (t1 :: nil)
        | Node x (t :: ts)  => Node x (g t :: ts)
        end.

Arguments tree_splice {a} _ _.

Lemma tree_splice_same : forall (a:Set) (t1 t2:tree a),
    tree_splice t1 t2 = tree_splice' t1 t2.
Proof.
    intros a t1. apply tree_nested_ind. intros x ts. destruct ts as [|t ts].
    - reflexivity.
    - intros [H1 H2]. simpl. rewrite H1. reflexivity.
Qed.


Theorem tree_size_splice: forall (a:Set) (t1 t2:tree a), 
    tree_size (tree_splice t1 t2) = plus (tree_size t1) (tree_size t2).
Proof.
    intros a t1. apply tree_nested_ind. intros x ts. destruct ts.
    - intros. simpl. apply plus_n_Sm.
    - intros [H1 H2]. simpl. rewrite H1. rewrite <- plus_n_Sm.
      rewrite plus_assoc. reflexivity.
Qed.





