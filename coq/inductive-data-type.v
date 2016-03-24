Set Implicit Arguments.

Print bool. (* Inductive bool : Set :=  true : bool | false : bool *)

Inductive month : Set := 
  | January : month | February : month  | March : month
  | April : month   | May : month       | June : month
  | July : month    | August : month    | September : month
  | October : month | November : month  | December : month.



Inductive whatever : Set := | A | B | C | D. (* simpler syntax *)

Check month_ind.
(*
forall P : month -> Prop,
       P January ->
       P February ->
       P March ->
       P April ->
       P May ->
       P June ->
       P July ->
       P August ->
       P September ->
       P October -> P November -> P December -> forall m : month, P m
*)

Check month_rec.
(*
forall P : month -> Set,
       P January ->
       P February ->
       P March ->
       P April ->
       P May ->
       P June ->
       P July ->
       P August ->
       P September ->
       P October -> P November -> P December -> forall m : month, P m
*)

Inductive season : Set :=
  | Spring : season
  | Summer : season
  | Autumn : season
  | Winter : season.

Definition month_to_season : month -> season :=
  month_rec (fun m => season)
            Winter Winter Spring
            Spring Spring Summer
            Summer Summer Autumn
            Autumn Autumn Winter.

Eval compute in month_to_season January.
Eval compute in month_to_season February.
Eval compute in month_to_season March.
Eval compute in month_to_season April.
Eval compute in month_to_season May.
Eval compute in month_to_season June.
Eval compute in month_to_season July.
Eval compute in month_to_season August.
Eval compute in month_to_season September.
Eval compute in month_to_season October.
Eval compute in month_to_season November.
Eval compute in month_to_season December.

Check bool_ind. (* forall P : bool -> Prop, P true -> P false -> forall b : bool, P b *)
Check bool_rec. (* forall P : bool -> Set, P true -> P false -> forall b : bool, P b  *)
Check bool_rect.(* forall P : bool -> Type, P true -> P false -> forall b : bool, P b *) 








