(def x [1 2 3 4 5])

(println (get x 2)) ; 3
(println (nth x 2)) ; 3
(println (x 2))     ; 3

(println (get x 10)); nil
;(println (nth x 10)); throws an exception
;(println (x 10))  ; throws an exception

(def y (assoc x 5 6)) ; returns new immutable vector

(println x) ; [1 2 3 4 5]
(println y) ; [1 2 3 4 5 6]
