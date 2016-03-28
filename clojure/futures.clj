; futures
(defn long-calculation [num1 num2]
 (Thread/sleep 1000)
 (* num1 num2)) 


(defn long-run[]
  (let [x (long-calculation 11 13)
        y (long-calculation 13 17)
        z (long-calculation 17 19)]
    (* x y z)))

(time (long-run)) ; "Elapsed time: 3000.523824 msecs"

; (future & body)

(defn fast-run[]
  (println "fast-run is running")
  (let [x (future (long-calculation 11 13))
        y (future (long-calculation 13 17))
        z (future (long-calculation 17 19))]
    (* @x @y @z)))  ; will block until value of future available

(time (fast-run)) ; "Elapsed time: 1035.487662 msecs"


(def x (future (fast-run))) ; this defines future and triggers run too
(println (future-done? x))  ; false
(println (future? x))       ; true
(println @x)
(println (future-done? x))  ; true
(future-cancel x)           ; won't do anything if already started
(println (future-cancelled? x)) ; false 


(shutdown-agents) ; needed to terminate threads
