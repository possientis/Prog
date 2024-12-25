Require Import ZF.Binary.
Require Import ZF.Binary.OneToOne.


(* A binary class is a bijection if and only if it is one-to-one.               *)
Definition Bijection (F:Binary) : Prop := OneToOne F.
