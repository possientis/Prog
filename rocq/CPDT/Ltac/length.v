Require Import List.
Import ListNotations.

Ltac length ls :=
    match ls with
    | nil           => O
    | _ :: ?ls'     => let n := length ls' in constr:(S n)
    end.


Goal False.
let n := length(1::2::3::nil) in pose n.
Abort.

Ltac map T f :=
    let rec map' ls :=
        match ls with
        | nil           => constr:(@nil T)
        | ?x :: ?ls'    =>
            let x' := f x in
                let ls'' := map' ls' in
                    constr:(x' :: ls'')
        end in map'.
