Set Implicit Arguments.
Require Import Arith.

Inductive set : Set := 
  | Empty     : set
  | Singleton : set -> set
  | Union     : set -> set -> set.

Fixpoint order (s:set) : nat :=
  match s with 
    | Empty         => 0
    | Singleton x   => 1 + order x
    | Union x y     => 1 + max (order x) (order y) 
  end.

Definition successor (s:set) : set :=
  Union s (Singleton s).

Fixpoint embed (n:nat) : set :=
  match n with
    | 0   => Empty
    | S p => successor (embed p)
  end.

Definition zero   := embed 0.
Definition one    := embed 1.
Definition two    := embed 2.
Definition three  := embed 3.
Definition four   := embed 4.
Definition five   := embed 5.
Definition six    := embed 6.
Definition seven  := embed 7.
Definition eight  := embed 8.
Definition nine   := embed 9.
Definition ten    := embed 1.

Fixpoint subset_n (n:nat) : set -> set -> bool :=
  match n with 
    | 0   => (fun _ _     => true)
    | S p => (fix subset (a:set) : set -> bool :=
      match a with
        | Empty           => (fun _ => true)
        | Singleton x     => (fix f (b:set) : bool :=
          match b with
            | Empty       => false
            | Singleton y =>  if subset x y then subset_n p y x else false
            | Union y z   => if (f y) then true else (f z)
          end)
        | Union x y   => (fun z => if subset x z then subset y z else false)
      end)
  end.

Definition subset (a b:set) : bool := subset_n (order a + order b) a b.

Lemma subset_def1: forall b:set, subset Empty b = true.
Proof.
  intro b. elim b.
  unfold subset. simpl. trivial. 
  intros s H. unfold subset. simpl. trivial.
  intros s H t H'. unfold subset. simpl. trivial.
Qed. 

Lemma subset_def2: forall x:set, subset (Singleton x) Empty = false.
Proof.
  intro x. unfold subset. simpl. trivial.
Qed.



Lemma test : forall (n:nat),
 forall (a b:set),  order a + order b <= n -> subset a b = subset_n n a b.
Proof.
  intro n. elim n. intros a b. intro H. unfold subset. 
  cut ( 0 = order a + order b). intro H'. rewrite <- H'. trivial.
  apply le_n_0_eq. exact H. clear n. intro n. intro IH. intros a. 
  elim a. intro b. intro H0. unfold subset. simpl. case (order b).
  simpl. trivial. intro m. simpl. trivial. intro x. intro H. 
  intro b. intro H'. elim b. unfold subset. simpl. trivial. intro y.
  intro H0.
(*
Lemma subset_def3: forall x y:set,
subset (Singleton x) (Singleton y) = if (subset x y) then (subset y x) else false.
Proof.
  intros x y. unfold subset.
*)






