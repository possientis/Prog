Require Import ZArith.

Import Z.

Search Z.mul Z.add "distr".

Search "+" "*" "distr".

Search "+"%Z "*"%Z "distr".

Open Scope Z_scope.

Search "+" "*" "distr".



Search "+" "*" "distr" -positive -Prop.


Search (?x * _ + ?x * _).
Search (?x * _ + ?x * _) outside OmegaLemmas.









