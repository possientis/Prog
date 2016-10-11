; Bridge design pattern
(ns bridge
  (:gen-class))
; bridge implementation interface
(def DrawAPI      ; constructor
  (letfn 
    ; object created from data is message passing interface
    [(this [data]     
      (fn [m]
        (cond (= m :drawCircle) (drawCircle data)
              :else (println "DrawAPI: unknown operation error"))))
     (drawCircle [data]
       (fn [radius x y]
        (println "DrawAPI::drawCircle is not implemented")))]
    ; returning no argument constructor
    (fn [] (this :ignored)))) 


; concrete bridge implementation classes implementing DrawAPI interface
(def RedCircle    ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]                         
      (fn [m]
        (cond (= m :drawCircle) (drawCircle data)
              :else ((base data) m))))    ; passing message to base object
     (base [data] data)                   ; data = base
     (drawCircle [data]
       (fn [radius x y]
         (print "Drawing Circle[ color: red  , radius: ")
         (print radius)
         (print ", x: ") (print x) 
         (print ", y: ") (print y) 
         (println "]")))]
    ; returning no argument constructor
    (fn [] (this (DrawAPI)))))            ; data = base = (DrawAPI)

(def GreenCircle  ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]                         
      (fn [m]
        (cond (= m :drawCircle) (drawCircle data)
              :else ((base data) m))))    ; passing message to base object
     (base [data] data)                   ; data = base
     (drawCircle [data]
       (fn [radius x y]
         (print "Drawing Circle[ color: green, radius: ")
         (print radius)
         (print ", x: ") (print x) 
         (print ", y: ") (print y) 
         (println "]")))]
    ; returning no argument constructor
    (fn [] (this (DrawAPI)))))            ; data = base = (DrawAPI)

; create an abstract class Shape using the DrawAPI interface.
(def Shape        ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :draw) (draw data)
               (= m :drawAPI) (drawAPI data)
               :else (println "Shape: unknown operation error"))))
     (drawAPI [data] data)                ; data = drawAPI
     (draw [data]
       (println "Shape::draw is not implemented"))]
     ; returning on argument constructor
    (fn [draw-api] (this draw-api))))


; create concrete class implementing the Shape interface (abstract class)
(def Circle       ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :draw) (draw data)
               :else ((base data) m))))   ; passing message to base object
     (base [data] (first data))
     (draw [[base x y radius]]
       (let [drawAPI (base :drawAPI)]
         ((drawAPI :drawCircle) radius x y)))]
     ; returning on argument constructor
    (fn [x y radius draw-api] (this [(Shape draw-api) x y radius]))))

; Use Shape and DrawAPI classes to draw different colored circles
; implementation of concrete circles selected at run time.
(defn -main []
  (def redCircle (Circle 100 100 10 (RedCircle)))
  (def greenCircle (Circle 100 100 10 (GreenCircle)))
  (redCircle :draw)
  (greenCircle :draw))

;(-main)


