; Prototype design pattern
; Imagine that in order to instantiate certain objects we need to carry out
; expensive database queries. In order to improve performance, it would 
; be beneficial to cache whatever object is created from the database
; and return a copy of the cached object whenever a subsequent request
; for object instantiation arises.
(ns prototype (:gen-class))

(def ICloneable         ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :clone) (clone data)
               :else (println "Cloneable: unknown operation error"))))
     ;
     (clone [data]
       (println "Cloneable::clone is not implemented"))]
    ; returning no argument constructor
    (fn [] (this :ignored))))

(def Shape              ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :getId) (getId data)
               (= m :setId) (setId data)
               (= m :draw) (draw data)
               :else (let [[base id] data] (base m)))))
     ;
     (getId [[base id]] id)
     ;
     (setId [[base _]]
       (fn [id] (this [base id])))  ; returns function returning new immutable obj
     ;
     (draw [data]
       (println "Shape::draw is not implemented"))]
    ; returning no argument constructor
    (fn [] (this [(ICloneable) nil]))))

(def Rectangle          ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :draw) (draw data)
               (= m :clone) (clone data)
               (= m :setId) (setId data)
               :else (data m))))  ; data is simply base object
     ;
     (draw [data]
       (println "Inside Rectangle::draw() method."))
     ;
     (clone [data] (this data)) ; not much to do, object immutable
     ;
     (setId [data]
       (fn [id] (this ((data :setId) id))))]; function returning new immutable obj
    ; returning no argument constructor
    (fn [] (this (Shape)))))

(def Square             ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :draw) (draw data)
               (= m :clone) (clone data)
               (= m :setId) (setId data)
               :else (data m))))  ; data is simply base object
     ;
     (draw [data]
       (println "Inside Square::draw() method."))
     ;
     (clone [data] (this data)) ; not much to do, object immutable
     ;
     (setId [data]
       (fn [id] (this ((data :setId) id))))]; function returning new immutable obj
    ; returning no argument constructor
    (fn [] (this (Shape)))))

(def Circle             ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :draw) (draw data)
               (= m :clone) (clone data)
               (= m :setId) (setId data)
               :else (data m))))  ; data is simply base object
     ;
     (draw [data]
       (println "Inside Circle::draw() method."))
     ;
     (clone [data] (this data)) ; not much to do, object immutable
     ;
     (setId [data]
       (fn [id] (this ((data :setId) id))))]; function returning new immutable obj
    ; returning no argument constructor
    (fn [] (this (Shape)))))

(def PrototypeManager   ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :getShape) (getShape data)
               (= m :loadCache) (loadCache data))))
     ;
     (getShape [data]
       (fn [shapeId] (data shapeId))) ; data is hash-map
     ;
     (loadCache [data]
       (let [rect (((Rectangle) :setId) "1")
             square (((Square) :setId) "2")
             circle (((Circle) :setId) "3")
             shapeMap (conj {"1" rect}
                            (conj {"2" square}
                                  (conj {"3" circle} {})))]
         (this shapeMap)))]
    ; returning constructor with single optional argument
    (fn [&[data]] (this data))))
(defn -main []
; need a prototype manager, with a few registered prototypes
(def manager ((PrototypeManager) :loadCache))
; manager can now be used as factory object
(def clonedShape1 ((manager :getShape) "1"))
(clonedShape1 :draw)

(def clonedShape2 ((manager :getShape) "2"))
(clonedShape2 :draw)

(def clonedShape3 ((manager :getShape) "3"))
(clonedShape3 :draw))

;(-main)




