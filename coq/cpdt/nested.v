Require Import List.

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


(*
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


(* This has nothing to do with 'tree a' but since 'tree a' contains a list... *)
Fixpoint map (a b:Set) (f:a -> b) (xs:list a) : list b :=
    match xs with
    | nil       => nil
    | cons x xs => cons (f x) (map a b f xs)
    end.

Arguments map {a} {b} _ _.

(* This 'map'-based solution fails despite looking very legitimate            *)

(*
Fixpoint fmap (a b:Set) (f:a -> b) (t:tree a) {struct t} : tree b :=
    match t with
    | Node x ts     => Node (f x) (map (fmap a b f) ts)
    end. 
                                                                              *)


(* Another case when nested induction saves the day. however in practice,     *)
(* this definition seems like a nightmare to handle proofs (at least given    *)
(* current skills). We would like the following equality to hold:             *) 
(*                                                                            *)
(* fmap f (Node x ts) = Node (f x) (map (fmap f) ts)                          *)
(*                                                                            *)
(* to hold.                                                                   *)

Fixpoint fmap (a b:Set) (f:a -> b) (t:tree a) : tree b :=
    match t with
    | Node x ts     => Node (f x) 
        ((fix map (ts':list (tree a)) : list (tree b) :=
            match ts' with
            | nil       => nil
            | cons t ts => cons (fmap a b f t) (map ts)
            end) ts)  

    end.

Arguments fmap {a} {b} _ _. 


(* Checking the obvious does work well though                                 *)
Lemma fmap_check1 : forall (a b:Set) (f:a -> b) (x:a), 
    fmap f (Node x nil) = Node (f x) nil.
Proof. intros  a b f x. reflexivity. Qed.

(* However, proving the equality:                                             *)
(*                                                                            *)
(* fmap f (Node x ts) = Node (f x) (map (fmap f) ts)                          *)
(*                                                                            *)
(* appears to be difficult. One successful way is via an indirect route       *)

(* let us implement a value accessor                                          *)
Definition tree_val (a:Set) (t:tree a) : a :=
    match t with
    | Node x _  => x
    end.

Arguments tree_val {a} _.

(* as well as a list accessor                                                 *)
Definition tree_list (a:Set) (t:tree a) : list (tree a) :=
    match t with
    | Node _ ts     => ts
    end.

Arguments tree_list {a} _.

(* If two trees have same values and list, then they are the same tree        *)
Lemma tree_equal : forall (a:Set) (t1 t2: tree a), 
    tree_val t1 = tree_val t2 -> 
    tree_list t1 = tree_list t2 -> 
    t1 = t2.
Proof.
    intros a t1 t2 H1 H2. destruct t1, t2.
    simpl in H1. simpl in H2. subst. reflexivity.
Qed.

(* So we prove that fmap behaves the way we expect at the 'list' level...     *)

Lemma tree_list_fmap : forall (a b:Set) (f:a -> b) (t:tree a),
    tree_list (fmap f t) = map (fmap f) (tree_list t).
Proof.
    intros a b f. apply tree_nested_ind2.
    - intros x. reflexivity.
    - intros x t ts H0 H1. simpl. unfold map.
        fold (map (fmap f) ts).
        remember (
            fix map (ts : list (tree a)) : list (tree b) :=
               match ts with
               | nil => nil
               | t :: ts => fmap f t :: map ts
               end) as g eqn:Hg. 
        assert (forall (ts:list (tree a)), g ts = map (fmap f) ts) as E.
        + clear t ts H1 H0. induction ts as [| t ts IH].
            { rewrite Hg. reflexivity. }
            { rewrite Hg, <- Hg, IH. reflexivity. }
        + rewrite E. reflexivity.
Qed.

(* So we can now obtain what we want                                          *)

Lemma fmap_check2 : forall (a b:Set) (f:a -> b) (x:a) (ts:list (tree a)),
    fmap f (Node x ts) = Node (f x) (map (fmap f) ts).
Proof.
    intros a b f x ts. apply tree_equal.
    - reflexivity.
    - rewrite tree_list_fmap. simpl. reflexivity.
Qed.



(* Another failure, leading to the need for nested recursion                  *)

(*
Fixpoint fold (a b:Set) (f:a -> list b -> b) (t:tree a) {struct t} : b :=
    match t with 
    | Node x ts     => f x (map (fold a b f) ts)
    end.
                                                                              *)

(* Another case when nested induction saves the day                           *)
Fixpoint fold (a b:Set) (f:a -> list b -> b) (t:tree a) : b :=
    match t with 
    | Node x ts     => f x 
        ((fix map (ts': list (tree a)) : list b :=
            match ts' with
            | nil       => nil
            | cons t ts => cons (fold a b f t) (map ts)
            end) ts) 
    end.

Arguments fold {a} {b} _ _.

(* Once again, we were not able to define fold in the obvious way with map    *)
(* The odds are this will make proofs very difficult to perform               *)
(* So we should probably spend time proving that the obvious holds            *)

Lemma fold_check1 : forall (a b:Set)(f:a -> list b -> b)(x:a), 
    fold f (Node x nil) = f x nil.
Proof. reflexivity. Qed.

Lemma fold_check2 : 
    forall (a b:Set) (f:a -> list b -> b) (x:a) (ts:list (tree a)),
    fold f (Node x ts) = f x (map (fold f) ts).
Proof.
    intros a b f x ts. induction ts as [|t ts' IH].
    - reflexivity.
    - simpl. remember (
        fix map (ts : list (tree a)) : list b :=
            match ts with
            | nil => nil
            | t :: ts => fold f t :: map ts
            end) as g eqn:Eg.
      assert (forall (ts:list (tree a)), g ts = map (fold f) ts) as Hg.
      { induction ts as [|t' ls H].
        - rewrite Eg. reflexivity.
        - rewrite Eg. simpl. rewrite <- Eg. rewrite H. reflexivity.
      }
      rewrite Hg. reflexivity.
Qed.

Definition fmap_callback (a b:Set) (f:a -> b) : a -> list (tree b) -> tree b :=
    fun (x:a) (ts : list (tree b)) => Node (f x) ts.

Arguments fmap_callback {a} {b} _ _ _.

(* fmap is just an example of fold *)
Lemma fmap_is_a_fold : forall (a b:Set) (f:a -> b) (t:tree a), 
    fmap f t = fold (fmap_callback f) t.
Proof.
    intros a b f. apply tree_nested_ind2; intros x.
    - unfold fmap_callback. reflexivity.
    - intros t ts H1 H2. rewrite fold_check2. unfold fmap_callback at 1.
      rewrite fmap_check2. simpl. rewrite <- H1.
      rewrite fmap_check2 in H2. rewrite fold_check2 in H2. 
      unfold fmap_callback in H2 at 1.
      injection H2. intros H. rewrite <- H. reflexivity.
Qed.


Fixpoint sum (ls:list nat) : nat :=
    match ls with
    | nil       => 0
    | n :: ns   => plus n (sum ns)
    end.

(*
Fixpoint tree_size (a:Set) (t:tree a) : nat :=
    match t with
    | Node _ ts     => S (sum (map (tree_size a) ts))
    end.
*)
*)
