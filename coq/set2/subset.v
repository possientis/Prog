Require Import Arith.
Require Import Arith.Max.

Require Import set.
Require Import order.

(******************************************************************************)
(*                       subset : set -> set -> Prop                          *)
(******************************************************************************)
(*
  We have defined a type 'set' which is meant to represent a subclass of the 
  set theoretic class of finite sets. However, we know that equality on 'set'
  is of no value and an appropriate equivalence relation needs to be defined.
  One key step on the path to defining equivalence between sets is to define
  the inclusion relation <= on sets. Set membership is another important 
  relation on sets, but we shall find it more convenient to focus first on 
  the inclusion relation as a primitive, and define 'x in y' as {x} <= y. 
    
  The inclusion relation <= should satisfy the following properties:

  (i)   0 <= x                                , forall x
  (ii)  ¬({x} <= 0)                           , forall x
  (iii) {x} <= {y}  <-> (x <= y) /\ (y <= x)  , forall x,y
  (iv)  {x} <= yUz  <-> {x] <= y \/ {x} <= z  , forall x,y,z
  (v)   xUy <= z    <->  x <= z  /\  y <= z   , forall x,y,z

  Property (i) states that the empty set is a subset of all sets. 
  Property (ii) states that no singleton set {x} is ever a subset of the 
  empty set. Property (iii) states that a singleton set {x} is a subset
  of another singleton {y} if and only if x and y are 'equal' (we do not
  mean 'equal' as elements of 'set' of course), that is 'equivalent' (as 
  we shall later define it) which means that x and y are both subsets of 
  each other. Property (iv) states that a singleton set {x} is a subset of
  a union yUz if and only if x is an element of y or x is an element of z, 
  which in turn means that {x} is a subset of y or {x} is a subset of z.
  Property (v) states that a union xUy is a subset of z, if and only if
  both x and y are subsets of z. 

  All these properties are pretty natural, and we expect them to hold for 
  a binary relation <=, if it is to be viewed as a suitable candidate for 
  modelling the inclusion relation on 'set'. However, because properties 
  (i)-(v) appear to be very similar to a definition by recursion of <= 
  (viewed as a curried operator with boolean values <= : set -> set -> bool), 
  it is tempting to believe that these are actually defining properties. 
  In other words, it is tempting to believe that not only does there exists
  a relation on set which satisfies properties (i)-(v), but such relation
  is in fact unique. Proving existence and uniqueness of this relation is 
  the purpose of what follows. 
  
  Defining the Haskell type: 
  
    data Set = O | S Set | U Set Set
  
  the relation <= can be viewed as a map: subset :: Set -> Set -> Bool 
  which (following properties (i)-(v)) could be defined as follows:

  subset O _            = True                                  -- prop (i)
  subset (S x) O        = False                                 -- prop (ii)
  subset (S x) (S y)    = (subset x y) && (subset y x)          -- prop (iii)
  subset (S x) (U y z)  = (subset (S x) y) || (subset (S x) z)  -- prop (iv)
  subset (U x y) z      = (subset x z) && (subset y z)          -- prop (v)

  This looks like a recursive definition: first 'subset 0' is defined.
  Then 'subset (S x)' is defined and lastly 'subset (U x y)'. The definition 
  of 'subset (U x y)' involves 'subset x' and 'subset y' which is legtimate 
  for a structural recursion. Now the definition of 'subset (S x)' itself 
  looks like a structural recursion: it is first defined on O, then on (S y) 
  and finally on (U y z). The definition on (U y z) only involves evaluations
  of subset (S x) on y and z which is also very nice. However, something is
  not quite right when defining subset (S x) on (S y). A normal recursive
  definition of subset (S x) on (S y) should involve subset (S x) evaluated
  at y. Unfortunately, this is not what we have: our definition of subset (S x)
  on (S y) involves subset x y and subset y x. 

  Hence we cannot claim that the above Haskell definition constitutes a
  mathematically acceptable recursive definition. We may have valid 
  Haskell syntax and possibly prove that function evaluations would 
  always terminate, but we cannot claim to have 'mathematically' proved
  the existence of a binary relation <= on set, which satisfies (i)-(v).

  In fact, attempting to replicate this definition in Coq will not yield
  valid code: "Error: Recursive definition of subset is ill-formed."

  Fixpoint subset (a:set): set -> Prop :=
    match a with
      | Empty       => (fun b => True)
      | Singleton x => (fun b =>
        match b with
          | Empty             => False
          | Singleton y       => subset x y /\ subset y x   (* problem here *) 
          | Union y z         => subset a y \/ subset a z 
        end)
      | Union x y   => (fun b => subset x b /\ subset y b) 
    end.

  Rather than attempting to define a map subset : set -> set -> Prop directly,
  we shall define a sequence of maps Rn : set -> set -> Prop indexed by the 
  natural numbers. This sequence will be defined by a standard recursion on N, 
  making sure the map Rn for (n >= 1) is solely defined in terms of R(n-1).
  While we consider Rn to have values in 'Prop' when working with Coq, when
  translating the argument into standard ZF-based mathematics, we shall 
  regard Rn: set -> set -> 2 = {0,1}. Defining R0 x y = 1, for n >=1 we set: 

    Rn 0 _      = 1
    Rn {x} 0    = 0
    Rn {x} {y}  = R(n-1) x y /\ R(n-1) y x   
    Rn {x} yUz  = R(n-1) {x} y \/ R(n-1) {x} z
    Rn xUy z    = R(n-1) x z /\ R(n-1) y z

*)

Fixpoint subset_n (n:nat) : set -> set -> Prop :=
  match n with 
    | 0   => (fun _ _     => True)
    | S p => (fun a b     =>
      match a with
        | Empty           => True
        | Singleton x     => 
          match b with
            | Empty       => False
            | Singleton y => subset_n p x y /\ subset_n p y x
            | Union y z   => subset_n p (Singleton x) y \/
                             subset_n p (Singleton x) z 
          end
        | Union x y       => subset_n p x b /\ subset_n p y b
      end)
  end.

(* 

Once we have defined the sequence of mappings Rn: set -> set -> 2,
the key is to realize that given a b:set, the boolean sequence
(Rn a b) is eventually constant. Specifically, we have:

  order(a) + order(b) <= n -> Rn a b = R(n+1) a b

*)

Lemma subset_n_Sn : forall (n:nat) (a b:set),
  order a + order b <= n -> (subset_n n a b <-> subset_n (S n) a b).
Proof. 
  (* induction on n *)
  intro n. elim n.
  (* n = 0 *)
  intros a b. intro H. cut(a = Empty). intro H'. rewrite H'. simpl. tauto.
  apply order_sum_eq_0_l with (b:=b). symmetry. apply le_n_0_eq. exact H.
  (* n -> n+1 *)(* induction on a *)
  clear n. intros n IH. intro a. elim a.
  (* a = Empty *)
  intro b. simpl. tauto.
  (* a = Singleton x *)(* induction on b *)
  clear a. intros x Hx. intro b. elim b.
  (* b = Empty *)
  intro H. simpl. tauto.
  (* b = Singleton y *)
  clear b. intros y Hy H.
  unfold subset_n at 1. fold subset_n.
  cut(subset_n (S (S n)) (Singleton x) (Singleton y) <-> 
     (subset_n (S n) x y)/\(subset_n (S n) y x)). 
  intro H'. rewrite H'. rewrite <- IH, <- IH. tauto.
  apply order_sum_singleton. rewrite plus_comm. exact H.
  apply order_sum_singleton. exact H.
  simpl. reflexivity.
  (* b = Union y z *)
  clear b. intros y Hy z Hz H.
  unfold subset_n at 1. fold subset_n.
  cut(subset_n (S (S n)) (Singleton x) (Union y z) <->
     (subset_n (S n) (Singleton x) y)\/(subset_n (S n) (Singleton x) z)).
  intro H'. rewrite H'. rewrite <- IH, <- IH. tauto.
  apply order_sum_union_Rr with (y:=y). exact H.
  apply order_sum_union_Rl with (z:=z). exact H. 
  simpl. reflexivity.
  (* a = Union x y *)
  clear a. intros x Hx y Hy b H.
  unfold subset_n at 1. fold subset_n.
  cut(subset_n (S (S n)) (Union x y) b <-> 
     (subset_n (S n) x b)/\(subset_n (S n) y b)).
  intro H'. rewrite H'. rewrite <- IH, <- IH. tauto.
  apply order_sum_union_Lr with (x:=x). exact H.
  apply order_sum_union_Ll with (y:=y). exact H.
  simpl. reflexivity.
  Qed.

(* This allows us to define R: set -> set -> 2 as by setting
R a b = Rn a b for n large enough, specifically n = order a + order b
*)
Definition subset (a b:set) : Prop :=
  let n:= order a + order b in subset_n n a b.


(*
We now check the obvious, namely that R a b = Rn a b for n large enough
*)

Lemma subset_subset_n : forall (n:nat) (a b:set),
  order a + order b <= n -> (subset a b <-> subset_n n a b).
Proof.
  (* induction on n *)
  intros n. elim n.
  (* n = 0 *)
  intros a b H. cut (a = Empty). cut (b = Empty). intros Hb Ha. rewrite Ha, Hb.
  unfold subset. simpl. tauto.
  apply order_sum_eq_0_r with (a:=a). symmetry. apply le_n_0_eq. exact H.
  apply order_sum_eq_0_l with (b:=b). symmetry. apply le_n_0_eq. exact H.
  (* n -> n+1 *)
  clear n. intros n IH a b H.
  (* either order a + order b < S n or = S n *)
  cut((order a + order b < S n)\/(order a + order b = S n)). intro H0. elim H0.
  (* order a + order b < S n *)
  intro H1. rewrite IH. apply subset_n_Sn. 
  apply le_S_n. exact H1. apply le_S_n. exact H1. 
  (* order a + order b = S n *)
  intro H1. unfold subset. rewrite H1. tauto.
  (* finally *)
  apply le_lt_or_eq. exact H.
Qed.

(* 
At this stage we have defined a relation R: set -> set -> 2.
It remains to prove that R satisfies properties (i)-(v).

  (i)   0 <= x                                , forall x
  (ii)  ¬({x} <= 0)                           , forall x
  (iii) {x} <= {y}  <-> (x <= y) /\ (y <= x)  , forall x,y
  (iv)  {x} <= yUz  <-> {x] <= y \/ {x} <= z  , forall x,y,z
  (v)   xUy <= z    <->  x <= z  /\  y <= z   , forall x,y,z

  We start with (i)
*)
Proposition subset_0_all : forall (b:set), subset Empty b.
Proof.
  (* induction on b *)
  intro b. elim b.
  (* b = Empty *)
  unfold subset. simpl. apply I.
  (* b = Singleton x *)
  clear b. intros x H. unfold subset. simpl. apply I.
  (* b = Union x y *)
  clear b. intros x Hx y Hy. unfold subset. simpl. apply I.
Qed.

(*
property (ii)
*)

Proposition subset_single_0 : forall (x:set), ~subset (Singleton x) Empty.
Proof.
  (* not structural induction necessary *)
  intro x. unfold subset. simpl. tauto.
Qed.

(*
property (iii)
*)

Proposition subset_single_single : forall (x y:set),
  subset (Singleton x) (Singleton y) <-> (subset x y)/\(subset y x).
Proof.
  intros x y. unfold subset at 1. simpl. 
  rewrite <- subset_subset_n, <- subset_subset_n. tauto.
  rewrite plus_comm. apply plus_le_compat_l. apply le_S. apply le_n.
  apply plus_le_compat_l. apply le_S. apply le_n.
Qed.

(*
property (iv)
*)

Proposition subset_single_union: forall (x y z:set),
  subset (Singleton x) (Union y z) <-> 
  (subset (Singleton x) y)\/(subset (Singleton x) z).
Proof.
  intros x y z. unfold subset at 1. simpl.
  rewrite <- subset_subset_n, <- subset_subset_n. tauto. 
  simpl. rewrite <- plus_n_Sm. apply le_n_S. 
  apply plus_le_compat_l. apply le_max_r.
  simpl. rewrite <- plus_n_Sm. apply le_n_S. 
  apply plus_le_compat_l. apply le_max_l.
Qed.

(*
property (v)
*)

Proposition subset_union_all : forall (x y b:set),
  subset (Union x y) b <-> (subset x b)/\(subset y b).
Proof.
  intros x y b. unfold subset at 1. simpl.
  rewrite <- subset_subset_n, <- subset_subset_n. tauto.
  apply plus_le_compat_r. apply le_max_r. apply plus_le_compat_r. apply le_max_l.
Qed.

(*
Wrapping things up for the existence result: defining a few predicates
on relations of type set -> set -> 2. Each predicate refers to one
of the properties (i)-(v) which we have proved our inclusion 
relation satisfies
*)

Definition subset_prop_1 (relation: set -> set -> Prop) : Prop :=
  forall (b:set), relation Empty b.

Definition subset_prop_2 (relation: set -> set -> Prop) : Prop :=
  forall (x:set), ~relation (Singleton x) Empty.

Definition subset_prop_3 (relation: set-> set -> Prop) : Prop :=
  forall (x y:set),
  relation (Singleton x) (Singleton y) <-> relation x y /\ relation y x.

Definition subset_prop_4 (relation: set -> set -> Prop) : Prop :=
  forall (x y z:set),
  relation (Singleton x) (Union y z) <->
  relation (Singleton x) y \/ relation (Singleton x) z.

Definition subset_prop_5 (relation: set -> set -> Prop) : Prop :=
  forall (x y b:set),
  relation (Union x y) b <-> relation x b /\ relation y b.

(*
There exists a binary relation on set which satisfies (i)-(v)
  (i)   0 <= x                                , forall x
  (ii)  ¬({x} <= 0)                           , forall x
  (iii) {x} <= {y}  <-> (x <= y) /\ (y <= x)  , forall x,y
  (iv)  {x} <= yUz  <-> {x] <= y \/ {x} <= z  , forall x,y,z
  (v)   xUy <= z    <->  x <= z  /\  y <= z   , forall x,y,z
*)

Lemma subset_exist :
  subset_prop_1 subset /\
  subset_prop_2 subset /\
  subset_prop_3 subset /\
  subset_prop_4 subset /\
  subset_prop_5 subset.
Proof.
  split. unfold subset_prop_1. apply subset_0_all.
  split. unfold subset_prop_2. apply subset_single_0.
  split. unfold subset_prop_3. apply subset_single_single.
  split. unfold subset_prop_4. apply subset_single_union.
  unfold subset_prop_5. apply subset_union_all.
Qed.

(*
Such relation is in fact unique.
*)

Lemma subset_unique : forall (relation : set -> set -> Prop),
  subset_prop_1 relation ->
  subset_prop_2 relation ->
  subset_prop_3 relation ->
  subset_prop_4 relation ->
  subset_prop_5 relation ->
  forall (a b:set), relation a b <-> subset a b.
Proof.
  intros relation H1 H2 H3 H4 H5 a b.
  (* proof by induction on order a + order b <= n *)
  cut(forall n:nat, order a + order b <= n -> (relation a b <-> subset a b)).
  intro H. apply H with (n:= order a + order b). apply le_n.
  intro n. generalize a b. clear a b. elim n.
  (* order a + order b <= 0 *) 
  intros a b H. cut (a = Empty). intro H'. rewrite H'.
  split. intros. apply subset_0_all. intros. apply H1.
  apply order_sum_eq_0_l with (b:=b). symmetry. apply le_n_0_eq. exact H.
  (* true for <= n -> true for <= n+1 *)
  (* induction on a *)  
  clear n. intros n IH a. elim a.
  (* a = Empty *)
  intros b H. split. intros. apply subset_0_all. intros. apply H1.
  (* a = Singleton x *)(* induction on b *)
  clear a. intros x H b. elim b.
  (* b = Empty *)
  intros. split. 
  intros. apply False_ind. apply H2 with (x:=x). exact H6.
  intros. apply False_ind. apply subset_single_0 with (x:=x). exact H6. 
  (* b = Singleton y *)
  clear b. intros y H' H''. unfold subset_prop_3 in H3. 
  rewrite H3, subset_single_single, IH, IH. tauto.
  rewrite plus_comm. apply order_sum_singleton. exact H''.
  apply order_sum_singleton. exact H''.
  (* b = Union y z *)
  clear b. intros y Hy z Hz H'. unfold subset_prop_4 in H4.
  rewrite H4, subset_single_union, IH, IH. tauto.
  apply order_sum_union_Rr with (y:=y). exact H'.
  apply order_sum_union_Rl with (z:=z). exact H'.
  (* a = Union x y *)
  clear a. intros x Hx y Hy b H. unfold subset_prop_5 in H5.
  rewrite H5, subset_union_all, IH, IH. tauto.
  apply order_sum_union_Lr with (x:=x). exact H.
  apply order_sum_union_Ll with (y:=y). exact H.
Qed.

