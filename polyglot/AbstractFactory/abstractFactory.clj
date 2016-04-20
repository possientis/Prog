; Abstract Factory design pattern
(ns abstractFactory (:gen-class))


(defn Shape [hook]
  (letfn
    ; interface
    [(this [m]
       (cond (= m :draw) (hook)
             :else (println "Shape: unknown operation error")))]
    ; returning interface
    this))

(defn AbstractShape [hook color]
  (let
    ; data
    [_base (Shape hook)
     _color color]
    (letfn
      ;interface
      [(this [m]
         (cond (= m :color) _color
               (= m :asString) asString
               :else (_base m)))
       (asString [color]
         (cond (= color :RED) "red"
               (= color :GREEN) "green"
               (= color :BLUE) "blue"
               :else "unknown color"))]
      ; returning interface
      this)))

(def Rectangle      ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m] 
         (cond (= m :draw) (draw data)
         :else ((base data) m)))) ; passing message to base object
     (base [data] data)           ; data = base object
     (draw [data]
       (print "Drawing ")
       (print (((base data) :asString) ((base data) :color)))
       (println " rectangle"))]
    ; returning single constructor
    (fn [color] (this (AbstractShape (fn [] :ignored) color)))))

(def Square      ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m] 
         (cond (= m :draw) (draw data)
         :else ((base data) m)))) ; passing message to base object
     (base [data] data)           ; data = base object
     (draw [data]
       (print "Drawing ")
       (print (((base data) :asString) ((base data) :color)))
       (println " square"))]
    ; returning single constructor
    (fn [color] (this (AbstractShape (fn [] :ignored) color)))))

(def Circle      ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m] 
         (cond (= m :draw) (draw data)
         :else ((base data) m)))) ; passing message to base object
     (base [data] data)           ; data = base object
     (draw [data]
       (print "Drawing ")
       (print (((base data) :asString) ((base data) :color)))
       (println " circle"))]
    ; returning single constructor
    (fn [color] (this (AbstractShape (fn [] :ignored) color)))))


(defn AbstractShapeFactory [hook]
  (let [_hook hook]
    (letfn
      [(this [m]
         (cond (= m :getColor) (_hook)
               (= m :getShape) getShape
               :else (println "AbstractShapeFactory: unknown operation error")))
       (getShape [shapeType]
         (cond (= (.toUpperCase shapeType) "CIRCLE") (Circle (_hook))
               (= (.toUpperCase shapeType) "RECTANGLE")(Rectangle(_hook))
               (= (.toUpperCase shapeType) "SQUARE") (Square (_hook))
               :else nil))]
      ; returning interface
      this)))

(defn RedShapeFactory []
  (AbstractShapeFactory (fn [] :RED)))

(defn GreenShapeFactory []
  (AbstractShapeFactory (fn [] :GREEN)))

(defn BlueShapeFactory []
  (AbstractShapeFactory (fn [] :BLUE)))

(defn FactoryProducer []
  (letfn
    [(this [m]
     (cond (= :getFactory) getFactory
           :else (println "FactoryProducer: unknown operation error")))
     (getFactory [factoryType]
       (cond (= (.toUpperCase factoryType) "RED") (RedShapeFactory)
             (= (.toUpperCase factoryType) "GREEN") (GreenShapeFactory)
             (= (.toUpperCase factoryType) "BLUE") (BlueShapeFactory)
             :else nil))]
    ; returning interface
    this))


(defn -main []

(def producer (FactoryProducer))

; producing set of red widgets
(def redFactory ((producer :getFactory) "Red"))
(def shape1 ((redFactory :getShape) "CIRCLE"))
(def shape2 ((redFactory :getShape) "RECTANGLE"))
(def shape3 ((redFactory :getShape) "SQUARE"))
(shape1 :draw)
(shape2 :draw)
(shape3 :draw)

; producing set of green widgets
(def greenFactory ((producer :getFactory) "Green"))
(def shape4 ((greenFactory :getShape) "CIRCLE"))
(def shape5 ((greenFactory :getShape) "RECTANGLE"))
(def shape6 ((greenFactory :getShape) "SQUARE"))
(shape4 :draw)
(shape5 :draw)
(shape6 :draw)

; producing set of blue widgets
(def blueFactory ((producer :getFactory) "Blue"))
(def shape7 ((blueFactory :getShape) "CIRCLE"))
(def shape8 ((blueFactory :getShape) "RECTANGLE"))
(def shape9 ((blueFactory :getShape) "SQUARE"))
(shape7 :draw)
(shape8 :draw)
(shape9 :draw))

;(-main)



