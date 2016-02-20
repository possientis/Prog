;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; map as the usual function on lists
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(println (+ 1 2 3 4))

; using map on 4 arguments function '+'
(println (map + '(1 2 3) '(1 2 3) '(1 2 3) '(1 2 3)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; map as a datatype, associative array, dictionary
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def x {:a 1 :b 2 :c 3})
(def y {:a 1, :b 2, :c 3}) ; comma ',' optional 
(println x)
(println y)
(println (= x y)) ; true

(def z (hash-map :a 1 :b 2 :c 3))
(println z)
(println (= x z)) ; true

; a map is also a function excepting key as parameter
(println (list (x :a) (x :b) (x :c))) ; (1 2 3)
; a keyword is also a function expecting a sequence as parameter
(println (list (:a x) (:b y) (:c z))) ; (1 2 3)


(def u (assoc x :d 4))  ; returning new immutable map
(println u)

(def v (dissoc u :a))   ; returning new immutable map
(println v) 

(def nested1
  {
   :a { 
       :a1 3 
       :a2 4
      }
   :b { :b1 6 
        :b2 {
          :b21 78
          :b22 79
        }
      }
   })

(println nested1)

; quick access syntax
(def query1 (get-in nested1 [:a :a2])) ; 4
(println query1);
(def query2 (get-in nested1 [:b :b2 :b22]))
(println query2)  ; 79

; quick insert syntax
(def nested2 (assoc-in nested1 [:a :a3] 5))
(println nested2)

; quick update syntax: provide function + arguments
; (you can achieve identical semantics with assoc-in by providing
; new value, after reading old value and applying function...)
(def nested3 (update-in nested2 [:b :b2 :b22] + 21))
(println nested3)







