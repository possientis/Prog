; overloading, variadic function
(defn total-cost 
  ([item-cost num-items]    ; two arguments version
   (* item-cost num-items))
  ([item-cost]              ; single argument version
   (total-cost item-cost 1)))


(println (total-cost 120 5))  ; 600
(println (total-cost 480))    ; 480


; variadic function
(defn total-numbers [& numbers]
  (apply + numbers))


(println (total-numbers))       ; 0
(println (total-numbers 4))     ; 4
(println (total-numbers 4 3))   ; 7
(println (total-numbers 4 3 8)) ; 15

(defn f [arg1 arg2 & rest-args] ; '& rest-args'... not '&rest-args'
  (println (list? rest-args))   ; false
  (println (vector? rest-args)) ; false
  (println (seq? rest-args)))   ; true

(f 1 2 3 4)
