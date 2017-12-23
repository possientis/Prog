Require Import Category.
Require Import PreorderAsCategory.
Require Import natAsPreorder.

Definition NatPreorderCategory : Category (Mor NatPreorder) := 
    toCategory NatPreorder.
