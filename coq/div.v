Require Import ZArith.

Open Scope Z_scope.

Fixpoint div_bin (n m:positive) : Z*Z :=
  match n with
    | 1%positive    =>  match m with
                          | 1%positive    => (1,0)
                          | v             => (0,1)
                        end
    | xO n'         =>  let (q',r') := div_bin n' m in
                        match Z_lt_ge_dec (2*r')(Zpos m) with
                          | left _    => (2*q', 2*r')
                          | right _   => (2*q'+1, 2*r' - (Zpos m))
                        end
    | xI n'         =>  let (q',r') := div_bin n' m in 
                        match Z_lt_ge_dec (2*r'+1)(Zpos m) with
                          | left _    => (2*q', 2*r' + 1)
                          | right _   => (2*q' + 1, (2*r'+1)-(Zpos m))
                        end
  end.


Lemma rem_1_1_interval : 0 <= 0 < 1.
Proof.
  auto with zarith. (* omega also works *)
Qed.


Lemma rem_1_even_interval : forall m: positive, 
  0 <= 1 < Zpos (xO m).
Proof.
  intros m. split. 
  auto with zarith.
(*
Nothing comes up
SearchPattern (1 < Zpos _).
*)
(*
Locate "_ < _".
  Notation            Scope     
  "x < y" := Pos.lt x y          : positive_scope
                        
  "x < y" := lt x y    : nat_scope
                        
  "x < y" := Z.lt x y  : Z_scope (default interpretation)
  "x < y" := N.lt x y  : N_scope
*)
(*
Print Z.lt.
Z.lt = fun x y : Z => (x ?= y) = Lt
     : Z -> Z -> Prop
*)
compute. (* trick !!!! simpl fails but compute works !!! *)
reflexivity.
Qed.

Lemma rem_1_odd_interval : forall m:positive,
  0 <= 1 < Zpos(xI m).
Proof.
  intros m. split.
  auto with zarith.
  compute. reflexivity.
Qed.





