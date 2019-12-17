Definition id1 {a:Type} (x:a) : a := x.
Definition id2 (a:Type) (x:a) : a := x.
Definition id3 (a:Type) (x:a) : a := x.
Definition id4 (a:Type) (x:a) : a := x.
Definition id5 (a:Type) (x:a) : a := x.

Arguments id2 [a].
Arguments id3 {a}.
Arguments id4 [a] _.
Arguments id5 {a} _.




