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


Fixpoint map (a b:Set) (f:a -> b) (xs:list a) : list b :=
    match xs with
    | nil       => nil
    | cons x xs => cons (f x) (map a b f xs)
    end.

Arguments map {a} {b} _ _.

(* This fails despite looking very legitimate
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

Definition g (a b:Set) (f:a -> b) (t:tree a) : tree b :=
    match t with
    | Node x ts     => Node (f x) (map (fmap f) ts)
    end.

Arguments g {a} {b} _ _.

Lemma fmap_check : forall (a b:Set) (f:a -> b) (t:tree a),
    fmap f t = g f t.
Proof.
    intros a b f. apply (tree_nested_ind a
        (fun (t:tree a) => fmap f t = g f t)).
    intros x ts. induction ts as [|t ts IH].
    - reflexivity.
    - intros [H1 H2]. apply IH in H2.
Show.


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

