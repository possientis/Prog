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
             :else nil))]
    ;returning interface
    this))





