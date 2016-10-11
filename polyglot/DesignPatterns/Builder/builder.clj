; Builder Design Pattern
(ns builder (:gen-class))
; The main idea behind the builder design pattern is
; to provide an abstract interface for a 'builder object'
; A concrete builder object is not a factory object which returns
; a ready-made object of a certain type. A concrete builder object
; should be viewed as a toolbox allowing someone else (that someone
; else is called 'a director' within the context of the builer design
; pattern) to build an object of some type according to some plan.

; Let us define a possible 'director' class, whose purpose
; it is to manufacture meals

(def DirectorCook       ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :makeMeal) (makeMeal data)
               (= m :builder) (builder data)
               :else (println "DirectorCook: unknown operation error"))))
    ; This is the main method of the director, which creates an object
    ; based on some logic and algorithm which is encapsulated in the
    ; method body, and uses the tools provided by the builder interface.
     (makeMeal [data] ; data is simply a Builder object used to build DirectorCook
       (let [builder1 (data :startNewMeal)
             builder2 (builder1 :addBurger)
             builder3 (builder2 :addDrink)]
         (DirectorCook builder3)))
     ;
     (builder [data] data)] ; returning underlying builder
    ; returning single argument constructor
    (fn [builder] (this builder))))

; Note that the manufacture algorithm contained in the director
; is very general and does not tell us anything about the type of
; the object being created, let alone its internal representation.

(def MealBuilder        ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :startNewMeal) (startNewMeal data)
               (= m :addBurger) (addBurger data)
               (= m :addDrink) (addDrink data)
               :else (println "MealBuilder: unknown operation error"))))
     ;
     (startNewMeal [data]
       (println "MealBuilder::startNewMeal is not implemented")
       (MealBuilder))
     ;
     (addBurger [data]
       (println "MealBuilder::addBurger is not implemented")
       (MealBuilder))
     ;
     (addDrink [data]
       (println "MealBuilder::addDrink is not implemented"))]
    ; returning no argument constructor
    (fn [] (this :ignored))))

; We can implement MealBuilder in many different ways, so as to 
; construct objects of many possible types which do not even need
; to be related by a common base class 'Meal'

; However, at some point we need to retrieve the constructed object
; so there must be some method 'getObject'. In general, because the
; return type of 'getObject' may be arbitrary, the method declaration
; cannot be part of the interface MealBuilder as this would constrain
; the implementation to a specific type being constructed.

; In this example, we shall consider two concrete implementations of
; MealBuilder, a 'VegetarianMealBuilder' and a 'NonVegetarianMealBuilder'.
; Both implementation will allow the construction of objects of the same
; type, but one should remember that this need not be the case when 
; applying the builder design pattern.

; Concrete implementations of MealBuilder will hold an object of type
; Meal (the object being constructed), and will have a getObject() method.

(declare Meal)

(declare VegBurger)
(declare Coke)
(def VegetarianMealBuilder
 (letfn 
   ; object created from data is message passing interface
   [(this [data]
      (fn [m]
        (cond (= m :startNewMeal) (startNewMeal data)
              (= m :addBurger) (addBurger data)
              (= m :addDrink) (addDrink data)
              (= m :getMeal) (getMeal data)
              :else (let [[base meal] data] (this [(base m) meal]))))) 
    ;
    (startNewMeal [[base meal]]
      (this [base (Meal)]))
    ;
    (addBurger [[base meal]]
      (this [base ((meal :addItem) (VegBurger))]))
    ;
    (addDrink [[base meal]]
      (this [base ((meal :addItem) (Coke))]))
    ;
    (getMeal [[base meal]]
      meal)]
   ; returning no argument constructor
   (fn [] (this [(MealBuilder) nil]))))

(declare ChickenBurger)
(declare Pepsi)
(def NonVegetarianMealBuilder
 (letfn 
   ; object created from data is message passing interface
   [(this [data]
      (fn [m]
        (cond (= m :startNewMeal) (startNewMeal data)
              (= m :addBurger) (addBurger data)
              (= m :addDrink) (addDrink data)
              (= m :getMeal) (getMeal data)
              :else (let [[base meal] data] (this [(base m) meal]))))) 
    ;
    (startNewMeal [[base meal]]
      (this [base (Meal)]))
    ;
    (addBurger [[base meal]]
      (this [base ((meal :addItem) (ChickenBurger))]))
    ;
    (addDrink [[base meal]]
      (this [base ((meal :addItem) (Pepsi))]))
    ;
    (getMeal [[base meal]]
      meal)]
   ; returning no argument constructor
   (fn [] (this [(MealBuilder) nil]))))

; Both of the above concrete builders happen to produce objects
; of the same type 'Meal' implemented as a list of 'Item'

(def Meal
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :addItem) (addItem data)
               (= m :getCost) (getCost data)
               (= m :showItems) (showItems data)
               :else (println "Meal: unknown operation error"))))
     ;
     (addItem [data]
       (fn [item] (this (cons item data))))
     ;
     (getCost [data]
       (loop [cost 0.0 items data]
         (if (empty? items)
           cost
           (recur (+ cost ((first items) :price)) (rest items)))))
     ;
     (showItems [data]
       (loop [items data]
         (if (empty? items)
           :done
           (let [item (first items)]
             (print "Item : ")
             (print (item :name))
             (print ", Packing : ")
             (print ((item :packing) :pack))
             (print ", Price : ")
             (println (item :price))
             (recur (rest items))))))]
    ; returning no argument constructor
    (fn [] (this nil))))

(def Item
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :price) (price data)
               (= m :name) (name data)
               (= m :packing) (packing data)
               :else (println "Item: unknown operation error"))))
     ;
     (price [data]
       (println "Item::price is not implemented"))
     ;
     (name [data]
       (println "Item::name is not implemented"))
     ;
     (packing [data]
       (println "Item::packing is not implemented"))]
    ; returning no argument interface
    (fn [] (this :ignored))))

(def Packing
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :pack) (pack data)
               :else (println "Packing: unknown operation error"))))
     ;
     (pack [data]
       (println "Packing::pack is not implemented"))]
     ; returning no argument constructor
     (fn [] (this :ignored))))

(def Wrapper
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :pack) (pack data)
               :else (data m))))  ; data is base object
     ;
     (pack [data] "Wrapper")]
    ; returning no argument constructor
    (fn [] (this (Packing)))))

(def Bottle
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :pack) (pack data)
               :else (data m))))  ; data is base object
     ;
     (pack [data] "Bottle")]
    ; returning no argument constructor
    (fn [] (this (Packing)))))

(def Burger
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :packing) (packing data)
               :else (data m))))
     ;
     (packing [data]
       (Wrapper))]
    ; returning no argument constructor
    (fn [] (this (Item)))))

(def ColdDrink
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :packing) (packing data)
               :else (data m))))
     ;
     (packing [data]
       (Bottle))]
    ; returning no argument constructor
    (fn [] (this (Item)))))

(def VegBurger
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :price) 2.5
               (= m :name) "Veg Burger"
               :else (data m))))]   ; data is base object
    ; returning no argument constructor
    (fn [] (this (Burger)))))

(def ChickenBurger
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :price) 5.05 
               (= m :name) "Chicken Burger"
               :else (data m))))]   ; data is base object
    ; returning no argument constructor
    (fn [] (this (Burger)))))

(def Coke
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :price) 3.0 
               (= m :name) "Coke"
               :else (data m))))]   ; data is base object
    ; returning no argument constructor
    (fn [] (this (ColdDrink)))))

(def Pepsi
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :price) 3.5 
               (= m :name) "Pepsi"
               :else (data m))))]   ; data is base object
    ; returning no argument constructor
    (fn [] (this (ColdDrink)))))

(defn -main []
; creating vegetarian meal
; First we create the appropriate concrete builder
(def vegBuilder (VegetarianMealBuilder))
; Next we create a director which will use this builder
(def cook (DirectorCook vegBuilder))
; Next we let the cook prepare the meal
(def cook1 (cook :makeMeal))
; Next we retrieve the object from the builder
(def vegMeal ((cook1 :builder) :getMeal))
; outputting results
(println "Veg Meal")
(vegMeal :showItems)
(print "Total Cost: ")
(println (vegMeal :getCost))

; same for non-vegetarian meal
(def nonVegBuilder (NonVegetarianMealBuilder))
; Next we create a director which will use this builder
(def cook (DirectorCook nonVegBuilder))
; Next we let the cook prepare the meal
(def cook1 (cook :makeMeal))
; Next we retrieve the object from the builder
(def nonVegMeal ((cook1 :builder) :getMeal))
; outputting results
(println "\nNon-Veg Meal")
(nonVegMeal :showItems)
(print "Total Cost: ")
(println (nonVegMeal :getCost)))

;(-main)






