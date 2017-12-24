Require Import Category.
Require Import Eq_Category.
Require Import Category2.
Require Import CategoryAsCategory2.
Require Import Category2AsCategory.


Theorem ToCatToCat2 : forall (A:Type) (c:Category A),
    toCategory (toCategory2 c) = c.
Proof.
    intros A c. apply eq_Category.
    - intros f. reflexivity.
    - intros f. reflexivity.
    - intros f g. reflexivity.
Qed.

(* When creating a Category from a Category2, we are effectively discarding 
   the type of objects Obj, which is not needed since it can be replaced 
   by the type of identity arrows. If we attempt to go back to an object
   of type Category2, we are constructing a new type of objects based on
   the identity arrows. There is no hope to recover the initial 'Obj' from
   this construction, and therefore, the equality of the following theorem
   is not even properly typed, let alone true or false... 

   We know that toCategory . toCategory2 is the identity on Category A,
   but we are not able to write anything like toCategory2 . toCategory 
   being the identity on Category2 Obj Mor   
*)

(*
Theorem ToCat2ToCat : forall (Obj Mor:Type) (c:Category2 Obj Mor),
    toCategory2 (toCategory c) = c.
*)




