; Abstract Factory design pattern
(defn Shape [hook]
  (letfn
    ; interface
    [(this [m]
       (cond (= m :draw) (hook)
             :else (println "Shape: unknown operation error")))]
    ; returning interface
    this))

(defn AbstractShape [hook]
  (let
    ; data
    [base (Shape hook)
     _color false]
    (letfn
      ;interface
      [(this [m]
         (cond (= m :setColor) setColor
               (= m :color) _color
               (= m :asString) asString
               :else (base m)))
       (setColor [color]
         (def _color color))
       (asString [color]
         (cond (= color :RED) "red"
               (= color :GREEN) "green"
               (= color :BLUE) "blue"
               :else "unknown color"))]
      ; returning interface
      this)))

(def x (AbstractShape (fn [] (println "okie"))))
(x :draw)
(println (x :color))
((x :setColor) :RED)
(println ((x :asString)(x :color)))

