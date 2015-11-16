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
  (let ((namespace #f)) ; just name hiding
    ; public interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'makeMeal)(makeMeal data))
              (else (display "DirectorCook: unknown operation error\n")))))
    ; This is the main method of the director, which creates an object
    ; based on some logic and algorithm which is encapsulated in the
    ; method body, and uses the tools provided by the builder interface.
    (define (makeMeal data)
      ((data 'builder) 'startNewMeal)
      ((data 'builder) 'addBurger)
      ((data 'builder) 'addDrink))
    ;
    (lambda args
      (define _builder (car args))
      (define (data m)
        (cond ((eq? m 'builder) _builder)
              (else (display "DirectorCook: should not happen\n"))))
      (this data))))
  
; Note that the manufacture algorithm contained in the director
; is very general and does not tell us anything about the type of
; the object being created, let alone its internal representation.

(define MealBuilder
  (let ((namespace #f)) ; just name hiding
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
    (lambda args
      (this #f))))  ; args ignored

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

(define VegetarianMealBuilder
  (let ((namespace #f)) ; just name hiding
    ; public interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'startNewMeal)(startNewMeal data))
              ((eq? m 'addBurger)(addBurger data))
              ((eq? m 'addDrink)(addDrink data))
              ((eq? m 'getMeal)(getMeal data))
              (else ((data 'base) m)))))  ; not useful, just practicing
    ;
    (define (startNewMeal data)
      (data 'new))
    ;
    (define (addBurger data)
      (((data 'meal) 'addItem) (VegBurger)))
    ;
    (define (addDrink data)
      (((data 'meal) 'addItem) (Coke)))
    ;
    (define (getMeal data)
      (data 'meal))
    ;
    (lambda args  ; args ignored
      (define _meal #f)
      (define _base (MealBuilder))  ; not really useful, just practicing
      (define (data m)
        (cond ((eq? m 'new)(set! _meal (Meal)))
              ((eq? m 'meal) _meal)
              ((eq? m 'base) _base)
              (else (display "VegetarianMealBuilder: should not happen\n"))))
      (this data))))

(define NonVegetarianMealBuilder
  (let ((namespace #f)) ; just name hiding
    ; public interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'startNewMeal)(startNewMeal data))
              ((eq? m 'addBurger)(addBurger data))
              ((eq? m 'addDrink)(addDrink data))
              ((eq? m 'getMeal)(getMeal data))
              (else ((data 'base) m)))))  ; not useful, just practicing
    ;
    (define (startNewMeal data)
      (data 'new))
    ;
    (define (addBurger data)
      (((data 'meal) 'addItem) (ChickenBurger)))
    ;
    (define (addDrink data)
      (((data 'meal) 'addItem) (Pepsi)))
    ;
    (define (getMeal data)
      (data 'meal))
    ;
    (lambda args  ; args ignored
      (define _meal #f)
      (define _base (MealBuilder))  ; not really useful, just practicing
      (define (data m)
        (cond ((eq? m 'new)(set! _meal (Meal)))
              ((eq? m 'meal) _meal)
              ((eq? m 'base) _base)
              (else (display "NonVegetarianMealBuilder: should not happen\n"))))
      (this data))))

; Both of the above concrete builders happen to produce objects
; of the same type 'Meal' implemented as a list of 'Item'

(define Meal
  (let ((namespace #f)) ; just name hiding
    ; public interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'addItem)(addItem data))
              ((eq? m 'getCost)(getCost data))
              ((eq? m 'showItems)(showItems data))
              (else (display "Meal:unknown operation error\n")))))
    ;
    (define (addItem data)
      (data 'add!))
    ;
    (define (getCost data)
      (let loop ((cost 0) (items (data 'items)))
        (if (null? items)
          cost
          (loop (+ cost ((car items) 'price)) (cdr items)))))
    ;
    (define (showItems data)
      (let loop ((items (data 'items)))
        (if (null? items)
          'done
          (begin
            (let ((that (car items))) ; Scheme case insensitive, need 'that'
              (display "Items : ")
              (display (that 'name))
              (display ", Packing : ")
              (display ((that 'packing) 'pack))
              (display ", Price : ")
              (display (that 'price))
              (newline))
            (loop (cdr items))))))
    ;
    (lambda args  ;args ignored
      (define _items '())
      (define (data m)
        (cond ((eq? m 'items) _items)
              ((eq? m 'add!) (lambda (x) (set! _items (cons x _items))))
              (else (display "Meal: should not happen\n"))))
      (this data))))

(define Item
  (let ((namespace #f)) ; just name hiding
    ; public interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'price)) (price data)
              ((eq? m 'name) (name data))
              ((eq? m 'packing) (_packing data))
              (else (display "Item: unknown operation error\n")))))
    ;
    (define (price data)
      (display "Item::price is not implemented\n"))
    ;
    (define (name data)
      (display "Item::name is not implemented\n"))
    ;
    (define (_packing data) ; Scheme case insensitive, hence '_packing'
      (display "Item::packing is not implemented\n"))
    ;
    (lambda args
      (this #f))))

(define Packing
  (let ((namespace #f)) ; just name hiding
    ; public interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'pack)(pack data))
              (else (display "Packing: unknown operation error\n")))))
    ;
    (define (pack data)
      (display "Packing::pack is not implemented\n"))
    ;
    (lambda args
      (this #f))))

(define Wrapper
  (let ((namespace #f)) ; just name hiding
    ; public interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'pack)(pack data))
              (else ((data 'base) m)))))
    ;
    (define (pack data)
      "Wrapper")
    ;
    (lambda args
      (define _base (Packing))  ; not useful
      (define (data m)
        (cond ((eq? m 'base) _base)
              (else (display "Wrapper: should not happen\n"))))
      (this data))))

(define Bottle
  (let ((namespace #f)) ; just name hiding
    ; public interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'pack)(pack data))
              (else ((data 'base) m)))))
    ;
    (define (pack data)
      "Bottle")
    ;
    (lambda args
      (define _base (Packing))  ; not useful
      (define (data m)
        (cond ((eq? m 'base) _base)
              (else (display "Bottle: should not happen\n"))))
      (this data))))

(define Burger
  (let ((namespace #f)) ; just name hiding
    ; public interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'packing) (_packing data))
              (else ((data 'base) m)))))
    ;
    (define (_packing data)
      (Wrapper))
    ;
    (lambda args
      (define _base (Item))
      (define (data m)
        (cond ((eq? m 'base) _base)
              (else (display "Burger: should not happen\n"))))
      (this data))))

(define ColdDrink
  (let ((namespace #f)) ; just name hiding
    ; public interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'packing) (_packing data))
              (else ((data 'base) m)))))
    ;
    (define (_packing data)
      (Bottle))
    ;
    (lambda args
      (define _base (Item))
      (define (data m)
        (cond ((eq? m 'base) _base)
              (else (display "ColdDrink: should not happen\n"))))
      (this data))))

(define VegBurger
  (let ((namespace #f)) ; just name hiding
    ; public interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'price) 2.5)
              ((eq? m 'name) "Veg Burger")
              (else ((data 'base) m)))))
    ;
    (lambda args
      (define _base (Burger))
      (define (data m)
        (cond ((eq? m 'base) _base)
              (else (display "VegBurger: should not happen\n"))))
      (this data))))

(define ChickenBurger
  (let ((namespace #f)) ; just name hiding
    ; public interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'price) 5.05)
              ((eq? m 'name) "Chicken Burger")
              (else ((data 'base) m)))))
    ;
    (lambda args
      (define _base (Burger))
      (define (data m)
        (cond ((eq? m 'base) _base)
              (else (display "ChickenBurger: should not happen\n"))))
      (this data))))

(define Coke
  (let ((namespace #f)) ; just name hiding
    ; public interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'price) 3.0)
              ((eq? m 'name) "Coke")
              (else ((data 'base) m)))))
    ;
    (lambda args
      (define _base (ColdDrink))
      (define (data m)
        (cond ((eq? m 'base) _base)
              (else (display "Coke: should not happen\n"))))
      (this data))))

(define Pepsi
  (let ((namespace #f)) ; just name hiding
    ; public interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'price) 3.5)
              ((eq? m 'name) "Pepsi")
              (else ((data 'base) m)))))
    ;
    (lambda args
      (define _base (ColdDrink))
      (define (data m)
        (cond ((eq? m 'base) _base)
              (else (display "Pepsi: should not happen\n"))))
      (this data))))

; creating vegetarian meal
; First we create the appropriate concrete builder
(define vegBuilder (VegetarianMealBuilder))
; Next we create a director which will use this builder
(define cook (DirectorCook vegBuilder))
; Next we let the cook prepare the meal
(cook 'makeMeal)
; Next we retrieve the object from the builder
(define vegMeal (vegBuilder 'getMeal))
; outputting result
(display "Veg Meal\n")
(vegMeal 'showItems)
(display "Total Cost: ")
(display (vegMeal 'getCost))
(newline)
;
; same for non-vegetarian meal
(define nonVegBuilder (NonVegetarianMealBuilder))
(define cook (DirectorCook nonVegBuilder))
(cook 'makeMeal)
(define nonVegMeal (nonVegBuilder 'getMeal))
; outputting result
(display "\nNon-Veg Meal\n")
(nonVegMeal 'showItems)
(display "Total Cost: ")
(display (nonVegMeal 'getCost))
(newline)

