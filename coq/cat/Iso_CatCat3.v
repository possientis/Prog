Require Import Category.
Require Import Eq_Category.
Require Import Category3.
Require Import CategoryAsCategory3.
Require Import Category3AsCategory.


Theorem ToCatToCat3 : forall (A:Type) (c:Category A),
    toCategory (toCategory3 c) = c.
Proof. 
    intros A c. apply eq_Category.
    -intros f. reflexivity.
    -intros f. reflexivity.
    - intros f g. reflexivity.
Qed.





