Require Import Ascii.
Require Import String.

Open Scope string_scope.

Inductive Star (P:string -> Prop) : string -> Prop :=
| Empty : Star P ""
| Iter  : forall (s1 s2:string), P s1 -> Star P s2 -> Star P (s1 ++ s2)
.

Inductive Regexp : (string -> Prop) -> Type :=
| RChar   : forall (c:ascii), Regexp (fun s => s = String c "")
| RConcat : forall (P1 P2:string -> Prop) (r1:Regexp P1) (r2:Regexp P2),
    Regexp (fun s => exists (s1 s2:string), s = s1 ++ s2 /\ P1 s1 /\ P2 s2)
| ROr     : forall (P1 P2:string -> Prop) (r1:Regexp P1) (r2:Regexp P2),
    Regexp (fun s => P1 s \/ P2 s)
| RStar   : forall (P:string -> Prop) (r:Regexp P), Regexp (Star P) 
.

(* I give up *)
