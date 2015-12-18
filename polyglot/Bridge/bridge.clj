; Bridge design pattern

; bridge implementation interface
(def DrawAPI              ; constructor
  (let [_static false]    ; dummy field
    ; object built from data is a message passing interface
    (declare drawCircle)
    (defn this [data]
      (fn [m]
        (cond (= m :drawCircle) (drawCircle data)
              :else (println "DrawAPI: unknown operation error"))))
    (defn drawCircle [data]
      (fn [radius x y]
        (println "DrawAPI::drawCircle is not implemented")))
    ; returning no argument constructor
    (fn [] (this :ignored))))

; concrete bridge implementation classes implementing DrawAPI interface
(def RedCircle            ; constructor
  (let [_static false]    ; dummy field
    ; object built from data is a message passing interface
    (declare drawCircle)
    (declare base)
    (defn this [data]
      (fn [m]
        (cond (= m :drawCircle) (drawCircle data)
              :else ((base data) m))))    ; passing message to base object
    (defn base [data]
      data)                               ; data = base
    (defn drawCircle [data]
      (fn [radius x y]
        (print "Drawing Circle[ color: red  , radius: ")
        (print radius)
        (print ", x: ") (print x) 
        (print ", y: ") (print y) 
        (print "]\n")))
    ; returning no argument constructor
    (fn [] (this (DrawAPI)))))            ; data = base = (DrawAPI)

;(def GreenCircle          ; constructor
;  (let [_static false]    ; dummy field
;    ; object built from data is a message passing interface
;    (declare drawCircle)
;    (declare base)
;    (defn this [data]
;      (fn [m]
;        (cond (= m :drawCircle) (drawCircle data)
;              :else ((base data) m))))    ; passing message to base object
;    (defn base [data]
;      data)                               ; data = base
;    (defn drawCircle [data]
;      (fn [radius x y]
;        (print "Drawing Circle[ color: green, radius: ")
;        (print radius)
;        (print ", x: ") (print x) 
;        (print ", y: ") (print y) 
;        (print "]\n")))
;    ; returning no argument constructor
;    (fn [] (this (DrawAPI)))))            ; data = base = (DrawAPI)

; create an abstract class Shape using the DrawAPI interface.
;(def Shape                ; constructor
;  (let [_static false]    ; dummy field
;    ; object built from data is a message passing interface
;    (declare draw)
;    (declare drawAPI)
;    (defn this [data]
;      (println "I am running")
;      (fn [m]
;        (cond (= m :draw) (draw data)
;              (= m :drawAPI) (drawAPI data)
;              :else (println "Shape: unknown operation error"))))
;    (defn drawAPI [data]
;      data)               ; data = drawAPI
;    (defn draw [data]
;      (println "Shape::draw is not implemented"))
;    ; returning on argument constructor
;    (fn [drawapi] (this drawapi))))

(println this)
(println drawCircle)
(println DrawAPI)
(println base)






