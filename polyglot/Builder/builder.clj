; Builder Design Pattern

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
               :else (println "DirectorCook: unknown operation error"))))
    ; This is the main method of the director, which creates an object
    ; based on some logic and algorithm which is encapsulated in the
    ; method body, and uses the tools provided by the builder interface.
     (makeMeal [data] ; data is simply a Builder object used to build DirectorCook
       (data :startNewMeal)
       (data :addBurger
 


