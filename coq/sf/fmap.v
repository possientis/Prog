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

Theorem fmap_app : forall (a b:Type) (f:a -> b) (l k:list a),
    map f (l ++ k) = map f l ++ map f k.
Proof.
    induction l as [| x xs H].
    - reflexivity.
    - intros k. simpl. rewrite H. reflexivity.
Qed.

Theorem map_rev: forall (a b:Type) (f: a -> b) (l:list a),
    map f (rev l) = rev (map f l).
Proof.
    intros a b f. induction l as [|x xs H].
    - reflexivity.
    - simpl. rewrite fmap_app. simpl. rewrite H. reflexivity.
Qed.

Fixpoint flat_map (a b:Type) (f: a -> list b) (l:list a) : list b :=
    match l with
    | []        => []
    | x :: xs   => f x ++ flat_map a b f xs
    end.

Arguments flat_map {a} {b} _ _.

Example test_flat_map1 : flat_map (fun n => [n,n+1,n+2]) [1,5,10] = 
    [1,2,3,5,6,7,10,11,12].
Proof. reflexivity. Qed.


Example test_flat_map2 : flat_map (fun n => [n,n,n]) [1,5,4] = [1,1,1,5,5,5,4,4,4].
Proof. reflexivity. Qed.


Definition option_map (a b:Type) (f:a -> b) (o:option a) : option b :=
    match o with
    | None      => None
    | Some x    => Some (f x)
    end.


