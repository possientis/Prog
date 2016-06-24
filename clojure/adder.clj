(defn adder [num1 num2]
  (let [x (+ num1 num2)]
    (fn [y]
      (+ x y))))

(def add-5 (adder 2 3))

(println (add-5 10))  ; 15






