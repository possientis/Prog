(defmacro infix [expr]
  (let [[left op right] expr]
    (list op left right)))

(println (macroexpand '(infix (2 + 5))))  ; (+ 2 5)

(println (infix (2 + 5))) ; 7
