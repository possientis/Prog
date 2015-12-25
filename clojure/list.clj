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

