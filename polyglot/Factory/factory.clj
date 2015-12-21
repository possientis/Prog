; Factory design pattern

(defn Shape [hook]
  (letfn 
    ; interface
    [(this [m]
       (cond (= m :draw) (hook)
             :else (println "Shape: unknown operation error")))]
    ; returning interface
    this))

(defn Rectangle []
  (let [this (Shape (fn [] (println "Inside Rectangle::draw() method.")))]
    ; returning interface
    this))

(defn Square []
  (let [this (Shape (fn [] (println "Inside Square::draw() method.")))]
    ; returning interface
    this))

(defn Circle []
  (let [this (Shape (fn [] (println "Inside Circle::draw() method.")))]
    ; returning interface
    this))

(defn ShapeFactory []
  (letfn
    ; interface
    [(this [m]
       (cond (= m :getShape) getShape
             :else (println "ShapeFactory: unknown operation error")))
    ; private member
     (getShape [shapeType]
       (cond (= shapeType "") nil
             (= (.toUpperCase shapeType) "CIRCLE") (Circle)
             (= (.toUpperCase shapeType) "RECTANGLE") (Rectangle)
             (= (.toUpperCase shapeType) "SQUARE") (Square)
             :else nil))]
    ;returning interface
    this))

(def factory (ShapeFactory))

; get an object of type Circle and call its draw method
(def shape1 ((factory :getShape) "CIRCLE"))
(shape1 :draw)


; get an object of type Rectangle and call its draw method
(def shape2 ((factory :getShape) "RECTANGLE"))
(shape2 :draw)


; get an object of type Square and call its draw method
(def shape3 ((factory :getShape) "SQUARE"))
(shape3 :draw)

