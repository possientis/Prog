Class ordered (T : Type) :=
  { eq  : T -> T -> bool
  ; lt  : T -> T -> bool
  ; leq : T -> T -> bool

  ; eq_sym
      : forall (t1 t2 : T)
      , eq t1 t2 = eq t2 t1
  ; lt_asym
      : forall (t1 t2 : T) (b : bool)
      , lt t1 t2 = true -> lt t2 t1 = false
  ; eq_implies_leq
      : forall (t1 t2 : T)
      , eq t1 t2 = true -> leq t1 t2 = true
  ; lt_implies_leq
      : forall (t1 t2 : T)
      , lt t1 t2 = true -> leq t1 t2 = true
  ; lt_not_eq
      : forall (t1 t2 : T)
      , lt t1 t2 = true -> eq t1 t2 = false
  }.

Class heap (H : Type) (E : Type) `{o : ordered E} : Type :=
  { empty     : H
  ; isEmpty   : H -> bool
  ; insert    : E -> H -> H
  ; merge     : H -> H -> H
  ; findMin   : H -> option E
  ; deleteMin : H -> option H

  ; empty_is_empty
      : isEmpty empty = true
  ; non_empty_is_not_empty
      : forall (h : H) (e : E)
      , isEmpty (insert e h) = true
  ; merge_empty_left
      : forall (h : H)
      , merge empty h = h
  ; merge_empty_right
      : forall (h : H)
      , merge h empty = h
  ; empty_findMin
      : findMin empty = None
  ; empty_deleteMin
      : deleteMin empty = None
  ; insert_min
      : forall (h : H) (e1 e2 : E)
      , findMin h = Some e1 -> lt e2 e1 = true -> findMin (insert e2 h) = Some e2
  ; insert_non_min
      : forall (h : H) (e1 e2 : E)
      , findMin h = Some e1 -> lt e2 e1 = false -> findMin (insert e2 h) = Some e1
  ; merge_min_left
      : forall (h1 h2 : H) (e1 e2 : E)
      , findMin h1 = Some e1 -> findMin h2 = Some e2 -> lt e1 e2 = true -> findMin (merge h1 h2) = Some e1
  ; merge_min_right
      : forall (h1 h2 : H) (e1 e2 : E)
      , findMin h1 = Some e1 -> findMin h2 = Some e2 -> lt e2 e1 = true -> findMin (merge h1 h2) = Some e2
  ; delete_min
      : forall (h1 h2 : H) (e1 e2 : E)
      , findMin h1 = Some e1 -> lt e2 e1 = true -> deleteMin (insert e2 h1) = Some h2 -> findMin h2 = Some e1
  }.

Require Import Arith.

Inductive leftish_heap (E : Type) : Type :=
  | Empty : leftish_heap E
  | Node  : nat -> E -> leftish_heap E -> leftish_heap E -> leftish_heap E
  .

Definition lh_empty {E : Type} : leftish_heap E :=
  Empty E.

Definition lh_isEmpty {E : Type} (h : leftish_heap E) : bool :=
  match h with
    | Empty _         => true
    | Node  _ _ _ _ _ => false
  end.

Definition lh_findMin {E : Type} `{o : ordered E} (h : leftish_heap E) : option E :=
  match h with
    | Empty _ => None
    | Node _ _ x _ _ => Some x
  end.

Definition rank {E : Type} (e : leftish_heap E) : nat :=
  match e with
    | Empty _         => 0
    | Node  _ r _ _ _ => r
  end.

(* Cannot guess decreasing argument of fix. *)
Definition makeT {E : Type} (x : E) (a : leftish_heap E) (b : leftish_heap E) : leftish_heap E :=
  if (rank b) <? (rank a)
    then Node E (rank b + 1) x a b
    else Node E (rank a + 1) x b a.

(* FAIL *)
Fail Fixpoint lh_merge1 {E : Type} {o : ordered E} (e1 : leftish_heap E) (e2 : leftish_heap E) : leftish_heap E :=
  match e1, e2 with
    | h, Empty _ => h
    | Empty _, h => h
    | Node _ _ x a1 b1 as h1, Node _ _ y a2 b2 as h2 =>
        if leq x y
          then makeT x a1 (lh_merge1 b1 h2)
          else makeT y a2 (lh_merge1 h1 b2)
  end.

(* the name 'merge' seems to be in scope already *)
Fixpoint lh_merge (E:Type) (o:ordered E) (e1 e2:leftish_heap E) : leftish_heap E :=
match e1 with
| Empty _ => e2
| Node _ _ x a1 b1 as h1  =>
   (fix g (e2' : leftish_heap E) : leftish_heap E :=
        match e2' with
        | Empty _   => e1
        | Node _ _ y a2 b2 as h2 =>
           if leq x y
              then makeT x a1 (lh_merge _ _ b1 h2)
              else makeT y a2 (g b2) 
        end) e2
end.

(* declares arguments as implicit going forward *)
Arguments lh_merge {E} {o}.
Arguments Empty  {E}.
Arguments Node {E}.

(* These 4 lemmas to check that lh_merge as the intended semantics *)
Lemma checkMerge1 : forall (E:Type) (o:ordered E) (e:leftish_heap E),
  lh_merge Empty e = e.
Proof.
  intros E o e.
  reflexivity.
Qed.

Lemma checkMerge2 : forall (E:Type) (o:ordered E) (e:leftish_heap E),
  lh_merge e Empty = e.
Proof.
  intros E o. destruct e as [|x a b]; reflexivity.
Qed.

Lemma checkMerge3
  : forall (E:Type) (o:ordered E) (e1 e2:leftish_heap E)
  , forall (n m:nat) (x y:E) (a1 b1 a2 b2:leftish_heap E) ,
  e1 = Node n x a1 b1 ->
  e2 = Node m y a2 b2 ->
  leq x y = true ->
  lh_merge e1 e2 = makeT x a1 (lh_merge b1 e2).
Proof.
  intros E o e1 e2 n m x y a1 b1 a2 b2 H1 H2 H.
  rewrite H1, H2. simpl. rewrite H. reflexivity.
Qed.

Lemma checkMerge4
  : forall (E:Type) (o:ordered E) (e1 e2:leftish_heap E), 
    forall (n m:nat) (x y:E) (a1 b1 a2 b2:leftish_heap E),
  e1 = Node n x a1 b1 ->
  e2 = Node m y a2 b2 ->
  leq x y = false ->
  lh_merge e1 e2 = makeT y a2 (lh_merge e1 b2).
Proof.
  intros E o e1 e2 n m x y a1 b1 a2 b2 H1 H2 H.
  rewrite H1, H2. simpl. rewrite H. reflexivity.
Qed.

Definition lh_insert {E : Type} `{o : ordered E} (x : E) (h : leftish_heap E) : leftish_heap E :=
  lh_merge (Node 1 x Empty Empty) h.

Definition lh_deleteMin {E : Type} `{o : ordered E} (h : leftish_heap E) : option (leftish_heap E) :=
  match h with
    | Empty         => None
    | Node  _ x a b => Some (lh_merge a b)
  end.

Theorem lh_empty_is_empty
  : forall (E : Type)
  , @lh_isEmpty E lh_empty = true.
Proof.
    intros E. reflexivity. 
Qed.

Lemma makeT_is_not_empty 
  : forall (E : Type) (x : E) (a b : leftish_heap E)
  , lh_isEmpty (makeT x a b) = false.
Proof.
    intros E x a b. unfold makeT. destruct (rank b <? rank a); reflexivity.
Qed.

Theorem lh_non_empty_is_not_empty
  : forall (E : Type) (o : ordered E) (h : leftish_heap E) (e : E)
  , lh_isEmpty (lh_insert e h) = false.
Proof.
    intros E o h e. destruct h as [|n x h1 h2].
    - reflexivity.
    - unfold lh_insert, lh_merge. destruct (leq e x).
        + reflexivity.
        + apply makeT_is_not_empty.
Qed.


Theorem lh_merge_empty_left
  : forall (E : Type) (o : ordered E) (h : leftish_heap E)
  , lh_merge lh_empty h = h.
Proof.
    intros E o h. reflexivity.
Qed.



Theorem lh_merge_empty_right
  : forall (E : Type) (o : ordered E) (h : leftish_heap E)
  , lh_merge h lh_empty = h.
Proof.
    intros E o h. destruct h; reflexivity.
Qed.



Theorem lh_empty_findMin
  : forall (E : Type) (o : ordered E)
  , lh_findMin lh_empty = None.
Proof.
    intros E o. reflexivity.
Qed.



Theorem lh_empty_deleteMin
  : forall (E : Type) (o : ordered E)
  , lh_deleteMin lh_empty = None.
Proof.
    intros E o. reflexivity.
Qed.


Theorem lh_insert_min
  : forall (E : Type) (o : ordered E) (h : leftish_heap E) (e1 e2 : E)
  , lh_findMin h = Some e1 -> lt e2 e1 = true -> lh_findMin (lh_insert e2 h) = Some e2.
Proof.
    intros E o h e1 e2 H1 H2. unfold lh_insert, lh_findMin. destruct h.
    - reflexivity.
    - simpl. unfold lh_findMin in H1. inversion H1. subst.
      assert (leq e2 e1 = true) as H3. { apply lt_implies_leq. assumption. } 
      rewrite H3. reflexivity.
Qed.


Theorem lh_insert_non_min
  : forall (E : Type) (o : ordered E) (h : leftish_heap E) (e1 e2 : E)
  , lh_findMin h = Some e1 -> lt e2 e1 = false -> lh_findMin (lh_insert e2 h) = Some e1.
Proof.
    intros E o h e1 e2 H1 H2. unfold lh_insert, lh_findMin. destruct h.
    - inversion H1.
    - simpl. unfold lh_findMin in H1. inversion H1. subst. destruct (leq e2 e1) eqn:H3.
        + simpl. 
          assert (e2 = e1).

Show.
(*

Theorem lh_merge_min_left
  : forall (E : Type) (o : ordered E) (h1 h2 : leftish_heap E) (e1 e2 : E)
  , lh_findMin h1 = Some e1 -> lh_findMin h2 = Some e2 -> lt e1 e2 = true -> lh_findMin (lh_merge h1 h2) = Some e1.
Proof.
Admitted.

Theorem lh_merge_min_right
  : forall (E : Type) (o : ordered E) (h1 h2 : leftish_heap E) (e1 e2 : E)
  , lh_findMin h1 = Some e1 -> lh_findMin h2 = Some e2 -> lt e2 e1 = true -> lh_findMin (lh_merge h1 h2) = Some e2.
Proof.
Admitted.

Theorem lh_delete_min
  : forall (E : Type) (o : ordered E) (h1 h2 : leftish_heap E) (e1 e2 : E)
  , lh_findMin h1 = Some e1 -> lt e2 e1 = true -> lh_deleteMin (lh_insert e2 h1) = Some h2 -> lh_findMin h2 = Some e1.
Proof.
Admitted.

Instance leftish {E : Type} `{o : ordered E} : heap (leftish_heap E) E :=
  { empty     := lh_empty
  ; isEmpty   := lh_isEmpty
  ; insert    := lh_insert
  ; merge     := lh_merge
  ; findMin   := lh_findMin
  ; deleteMin := lh_deleteMin

  (* Type and ordered instance come from the type class, thus we use _ _ *)
  ; empty_is_empty          := lh_empty_is_empty _
  ; non_empty_is_not_empty  := lh_non_empty_is_not_empty _ _
  ; merge_empty_left        := lh_merge_empty_left _ _
  ; merge_empty_right       := lh_merge_empty_right _ _
  ; empty_findMin           := lh_empty_findMin _ _
  ; empty_deleteMin         := lh_empty_deleteMin _ _
  ; insert_min              := lh_insert_min _ _
  ; insert_non_min          := lh_insert_non_min _ _
  ; merge_min_left          := lh_merge_min_left _ _
  ; merge_min_right         := lh_merge_min_right _ _
  ; delete_min              := lh_delete_min _ _
  }.
*)
