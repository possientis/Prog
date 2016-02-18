
(def x
  (let [l (list 1 2 3 4)]
    (list
      l
      (first l)
      (rest l)
      (next l)
      (list? l)
      (empty? l)
      (empty? (list))
      (cons 0 l))))

(println x)

(def y (list 1 2 3 4 5))
(def y0 (conj y 6))   ;  usual pre-append it seems despite syntax 
(def y1 (cons 0 y))   ;  also pre-append but result not a 'list' but a 'cons'

(println y0 ":" (list? y0))   ; true
(println y1 ":" (list? y1))   ; false 

(println (type y0)) ; clojure.lang.PersistentList
(println (type y1)) ; clojure.lang.Cons

