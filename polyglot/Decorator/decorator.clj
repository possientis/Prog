; Decorator Design Pattern

(ns decorator (:gen-class))

(defmulti description :type)
(defmulti cost        :type)
(defmulti wrapped     :type)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                 Pizza                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def Pizza  ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [class-dictionary { :description description
                                :cost        cost }]   
         (fn [m]
           (let [operation  (class-dictionary m :notfound)]
             (if (= operation :notfound)
               (throw (new Exception (format "Pizza: unknown operation %s" m)))
               (operation data))))))]
    ;
    ; returning no argument constructor
    ;
    (fn [] (this {:type ::pizza}))))  ; data encapsulates type only


(defmethod description ::pizza [data] 
  (throw (new Exception "Pizza::description is not implemented")))

(defmethod cost ::pizza [data] 
  (throw (new Exception "Pizza::cost is not implemented")))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                               PlainPizza                                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::plain-pizza ::pizza)

(def PlainPizza   ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [class-dictionary { :description description
                                :cost        cost }]   
         (fn [m]
           (let [operation  (class-dictionary m :notfound)]
             (if (= operation :notfound)
               ((:base data) m)             ; passing on message to base object
               (operation data))))))]
    ;
    ; returning no argument constructor
    ;
    (fn [] (this {:type ::plain-pizza :base (Pizza)}))))  

(defmethod description  ::plain-pizza [data] "Plain pizza")
(defmethod cost         ::plain-pizza [data] 3.0)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                              PizzaDecorator                                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::pizza-decorator ::pizza)

(def PizzaDecorator ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [class-dictionary { :description  description
                                :cost         cost 
                                :wrapped      wrapped}] ; should be protected    
         (fn [m]
           (let [operation  (class-dictionary m :notfound)]
             (if (= operation :notfound)
               ((:base data) m)             ; passing on message to base object
               (operation data))))))]
    ;
    ; returning single argument constructor
    ;
    (fn [pizza] (this { :type ::pizza-decorator 
                        :base (Pizza) 
                        :pizza pizza  }))))  

(defmethod description  ::pizza-decorator [data] ((:pizza data) :description))
(defmethod cost         ::pizza-decorator [data] ((:pizza data) :cost))
(defmethod wrapped      ::pizza-decorator [data] (:pizza data))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                              WithExtraCheese                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::with-extra-cheese ::pizza-decorator)

(def WithExtraCheese  ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [class-dictionary { :description description
                                :cost        cost }]   
         (fn [m]
           (let [operation  (class-dictionary m :notfound)]
             (if (= operation :notfound)
               ((:base data) m)             ; passing on message to base object
               (operation data))))))]
    ;
    ; returning single argument constructor
    ;
    (fn [pizza] (this { :type ::with-extra-cheese 
                        :base (PizzaDecorator pizza)  }))))

(defmethod description ::with-extra-cheese [data] 
  (str (((:base data) :wrapped) :description) 
       " + extra cheese"))

(defmethod cost ::with-extra-cheese [data] 
  (+ (((:base data) :wrapped) :cost) 0.5))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                              WithExtraOlives                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::with-extra-olives ::pizza-decorator)

(def WithExtraOlives  ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [class-dictionary { :description description
                                :cost        cost }]   
         (fn [m]
           (let [operation  (class-dictionary m :notfound)]
             (if (= operation :notfound)
               ((:base data) m)             ; passing on message to base object
               (operation data))))))]
    ;
    ; returning single argument constructor
    ;
    (fn [pizza] (this { :type ::with-extra-olives 
                        :base (PizzaDecorator pizza)  }))))

(defmethod description ::with-extra-olives [data] 
  (str (((:base data) :wrapped) :description) 
       " + extra olives"))

(defmethod cost ::with-extra-olives [data] 
  (+ (((:base data) :wrapped) :cost) 0.7))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                              WithExtraAnchovies                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::with-extra-anchovies ::pizza-decorator)

(def WithExtraAnchovies  ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [class-dictionary { :description description
                                :cost        cost }]   
         (fn [m]
           (let [operation  (class-dictionary m :notfound)]
             (if (= operation :notfound)
               ((:base data) m)             ; passing on message to base object
               (operation data))))))]
    ;
    ; returning single argument constructor
    ;
    (fn [pizza](this{ :type ::with-extra-anchovies 
                      :base (PizzaDecorator pizza)  }))))

(defmethod description ::with-extra-anchovies [data] 
  (str (((:base data) :wrapped) :description) 
       " + extra anchovies"))

(defmethod cost ::with-extra-anchovies [data] 
  (+(((:base data):wrapped):cost) 0.8))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                   Main                                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn -main []) ; bizarrely, the code outside of -main does run

(def plain-pizza  (PlainPizza))

(def nice-pizza   (WithExtraCheese (PlainPizza))) 

(def super-pizza  (WithExtraOlives 
                  (WithExtraCheese (PlainPizza))))

(def ultra-pizza  (WithExtraAnchovies 
                  (WithExtraOlives 
                  (WithExtraCheese (PlainPizza)))))

(println "Plain Pizza:"
         "\tCost: "         (plain-pizza :cost)
         "\tDescription: "  (plain-pizza :description))

(println "Nice Pizza:"
         "\tCost: "         (nice-pizza :cost)
         "\tDescription: "  (nice-pizza :description))

(println "Super Pizza:"
         "\tCost: "         (super-pizza :cost)
         "\tDescription: "  (super-pizza :description))

(println "Ultra Pizza:"
         "\tCost: "         (ultra-pizza :cost)
         "\tDescription: "  (ultra-pizza :description))



