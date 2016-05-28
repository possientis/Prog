Require Import List.

Section list_product.

Variable A:Type.
Variable op: A -> A -> A.

(* product l m should be the new list [ op x y | x <- l, y <- l ] *) 
