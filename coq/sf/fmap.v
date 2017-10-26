Require Import nat.
Require Import bool.
Require Import list.

Fixpoint map (a b:Type) (f:a -> b) (l:list a) : list b :=
    match l with
    | []        => []
    | x :: xs   => f x :: map a b f xs
    end.

Arguments map {a} {b} _ _.

Example map_test1 : map (plus 3) [2,0,2] = [5,3,5].
Proof. reflexivity. Qed.

Example map_test2: map oddb [2,1,2,5] = [false,true,false,true].
Proof. reflexivity. Qed.

Example map_test3: map (fun n => [evenb n,oddb n]) [2,1,2,5]
    = [[true,false],[false,true],[true,false],[false,true]].
Proof. reflexivity. Qed.


(* proving the naturality square which expresses the fact 
   that rev : list => list is a natural transformation 
   from the functor list to itself.
*)

Theorem map_rev: forall (a b:Type) (f: a -> b) (l:list a),
    map f (rev l) = rev (map f l).
Proof.
    intros a b f. induction l as [|x xs H].
    - reflexivity.
    - simpl.

Show.
