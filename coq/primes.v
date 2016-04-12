Set Implicit Arguments.
Require Import Arith.
Require Import List.

Inductive cmp : Set :=
  | Less :    cmp
  | Equal:    cmp
  | Greater : cmp.

Fixpoint three_way_compare (n m: nat) : cmp :=
  match n,m with
    | 0, 0        => Equal
    | 0, S q      => Less
    | S p, 0      => Greater
    | S p, S q    => three_way_compare p q
  end.

Eval compute in three_way_compare 34 67.
Eval compute in three_way_compare 67 67.
Eval compute in three_way_compare 90 67.

Print list.

Fixpoint update_primes (k:nat)(l: list (nat*nat)) : (list (nat*nat))*bool :=
  match l with
    | nil     => (nil, false)
    | a::ls   => let rs := update_primes k ls in
                    match three_way_compare k (snd a) with
                      | Less    => (nil,false)  (* should not happen *) 
                      | Equal   => ((fst a, (snd a) + (fst a))::(fst rs), true)     
                      | Greater => ((fst a, snd a)::(fst rs), (snd rs)) 
                    end
  end.

Fixpoint prime_sieve (k:nat) : list (nat*nat) :=
  match k with
    | 0             => nil
    | S 0           => nil
    | S (S 0)       => (2,4)::nil
    | S (S (S k'))  => nil 
  end.
