(def x
  (for [alpha "abc"
        beta (range 1 9)
        gamma '("x23" "x45" "x12")]
    (str alpha beta gamma)))

; simple trial at emulating nested loops
(def y
  (loop [i 0 j 0 k 0 res '()]
    (if (< i 5)
      (if (< j 5)
        (if (< k 5)
          (recur i j (+ 1 k) (cons [i j k] res))
          (recur i (+ j 1) 0 res))
        (recur (+ i 1) 0 0 res))
      res)))

; semantic equivalent of above 'for' expression
(def z
  (loop [alpha "abc" beta (range 1 9) gamma '("x23" "x45" "x12") res '()]
    (if (not (empty? alpha))
      (if (not (empty? beta))
        (if (not (empty? gamma))
          (recur alpha beta (rest gamma) (cons (str (first alpha) (first beta) (first gamma)) res))
          (recur alpha (rest beta) '("x23" "x45" "x12") res))
        (recur (rest alpha) (range 1 9) '("x23" "x45" "x12") res))
      res)))







(println (sort x))
(println (sort z))
