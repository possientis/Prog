; The 'thread-first' macro ->

; not very readable
(defn redemption [principle rate periods]
  (* principle (Math/pow (+ 1 (/ rate 100)) periods)))

(defn redemption-> [principle rate periods]
  (-> rate
      (/ 100) ; macro places 'rate' in second position
      (+ 1)
      (Math/pow periods)
      (* principle)))


(println (redemption 100 5 20))
(println (redemption-> 100 5 20))


