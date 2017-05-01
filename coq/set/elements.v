Require Import set.

(******************************************************************************)
(*                        elements : set -> list set                          *)
(******************************************************************************)

Fixpoint elements (a:set) : list set :=
  match a with
    | Empty         => nil
    | Singleton x   => x::nil
    | Union x y     => (elements x) ++ (elements y) 
  end.



