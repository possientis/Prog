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

(define DirectorCook
  (begin
    ; public interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'makeMeal)(makeMeal data))
              (else (display "DirectorCook: unknown operation error\n")))))
    ; This is the main method of the director, which creates an object
    ; based on some logic and algorithm which is encapsulated in the
    ; method body, and uses the tools provided by the builder interface.
    (define (makeMeal data)
      (data 'startNewMeal)
      (data 'addBurger)
      (data 'addDrink))
    ;
    (lambda data
      (let ((_builder (car data)))
        (this _builder)))))
  
; Note that the manufacture algorithm contained in the director
; is very general and does not tell us anything about the type of
; the object being created, let alone its internal representation.

(define MealBuilder
  (begin
    ; public interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'startNewMeal) (startNewMeal data))
              ((eq? m 'addBurger) (addBurger data))
              ((eq? m 'addDrink) (addDrink data))
              (else (display "MealBuilder: unknown operation error\n")))))
    ;
    (define (startNewMeal data)
      (display "MealBuilder::startNewMeal is not implemented\n"))
    (define (addBurger data)
      (display "MealBuilder::addBurger is not implemented\n"))
    (define (addDrink data)
      (display "MealBuilder::addDrink is not implemented\n"))
    ;
    (lambda data
      (this #f))))

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


