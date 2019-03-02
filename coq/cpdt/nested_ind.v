Require Import List.

(* We are using the type we are defining as the argument of 
   parameterized type family: this is a nested inductive type
*)

Inductive tree (a:Set) : Set :=
| Node : a -> list (tree a) -> tree a
.

Arguments Node {a} _ _.

(* useless
Check tree_rect.
*)

Fixpoint All (a:Set) (P:a -> Prop) (xs:list a) : Prop :=
    match xs with
    | nil       => True
    | cons x xs => P x /\ All a P xs
    end. 


Arguments All {a} _ _.

(* This definition should be fine but is rejected by Coq     

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

(* instead of mutually inductive definition, we shall used nested induction *)


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

Lemma tree_nested_ind2 : forall (a:Set) (P:tree a-> Prop),
    (forall (x:a), P (Node x nil)) ->
    (forall (x:a) (t:tree a) (ts:list (tree a)), P t -> P (Node x ts) -> P (Node x (t :: ts))) ->
    forall (t:tree a), P t.
Proof.
    intros a P Hnil Hcons.
    apply tree_nested_ind. intros x. induction ts as [|t ts IH].
    - intros. apply Hnil.
    - intros [H0 H1]. apply Hcons.
        + assumption.
        + apply IH. assumption.
Qed.


(* This has nothing to do with 'tree a' but used here to illustrate a point *) 
Fixpoint map (a b:Set) (f:a -> b) (xs:list a) : list b :=
    match xs with
    | nil       => nil
    | cons x xs => cons (f x) (map a b f xs)
    end.

Arguments map {a} {b} _ _.

(* This 'map'-based solution fails despite looking very legitimate
Fixpoint fmap (a b:Set) (f:a -> b) (t:tree a) {struct t} : tree b :=
    match t with
    | Node x ts     => Node (f x) (map (fmap a b f) ts) 
    end. 
*)

(* another case when nested induction saves the day *)
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

Lemma fmap_check1 : forall (a b:Set) (f:a -> b) (x:a), 
    fmap f (Node x nil) = Node (f x) nil.
Proof. intros  a b f x. reflexivity. Qed.


Definition extract (a:Set) (t:tree a) : list (tree a) :=
    match t with
    | Node _ ts     => ts
    end.

Arguments extract {a} _.

Lemma extract_fmap : forall (a b:Set) (f:a -> b) (t:tree a),
    extract (fmap f t) = map (fmap f) (extract t).
Proof.
    intros a b f. apply tree_nested_ind2.
    - intros x. reflexivity.
    - intros x t ts H0 H1. simpl. unfold map. reflexivity.

Show.


(*
Lemma fmap_check2 : forall (a b:Set) (f:a -> b) (x:a) (ts:list (tree a)),
    fmap f (Node x ts) = Node (f x) (map (fmap f) ts).
Proof.
    intros a b f x ts. remember (Node x ts) as t eqn:H. revert x ts H.
    apply (tree_nested_ind2 a (fun t =>
        forall (x : a) (ts : list (tree a)), t = Node x ts -> 
            fmap f t = Node (f x) (map (fmap f) ts))).
    - intros x y ts H. injection H. intros. subst. reflexivity.
    - clear t. intros x t ts H0 H1 y ts' H2. injection H2. intros. subst.
      

Show.
*)

(*
(* Another failure, leading to nested recursion
Fixpoint fold (a b:Set) (f:a -> list b -> b) (t:tree a) {struct t} : b :=
    match t with 
    | Node x ts     => f x (map (fold a b f) ts)
    end.
*)



(* another case when nested induction saves the day *)
Fixpoint fold (a b:Set) (f : a -> list b -> b) (t:tree a) : b :=
    match t with 
    | Node x ts     => f x 
        ((fix map (ts': list (tree a)) : list b :=
            match ts' with
            | nil       => nil
            | cons t ts => cons (fold a b f t) (map ts)
            end) ts) 
    end.

Arguments fold {a} {b} _ _.




Definition fmap_callback (a b:Set) (f:a -> b) : a -> list (tree b) -> tree b :=
    fun (x:a) (ts : list (tree b)) => Node (f x) ts.

Arguments fmap_callback {a} {b} _ _ _.

(* We are going to need the induction principle
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
*)

(* fmap is just an example of fold *)
Lemma fmap_is_a_fold : forall (a b:Set) (f:a -> b) (t:tree a), 
    fmap f t = fold (fmap_callback f) t.
Proof. intros a b f t.
       apply (tree_nested_ind a (fun (t:tree a) =>
            fmap f t = fold (fmap_callback f) t)).
       intros x. induction ts as [|t' ts' IH].
       - simpl. unfold fmap_callback. intros. reflexivity.
       - intros H. destruct H as [H1 H2]. apply IH in H2.
Show.
*)
