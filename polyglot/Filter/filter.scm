; Filter design pattern

; This pattern allows to use a list of objects and perform
; a filtering operation on that list so as to obtain a new
; list comprised of those objects in the initial list which
; satisfy a given predicate. Since the introduction of
; lambda expressions within Java 8 and the introduction
; of functional interfaces such as Predicate<T>, this 
; pattern is not very useful in practice and amounts 
; mainly to a coding exercise aiming at re-implementing
; the Predicate<T> java interface. This pattern is not
; useful either in functional languages which directly 
; support first class functions and filter operations on lists.


(define Person            ; constructor
  (let ((_static #f))
    ; object built from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'name)(name data))
              ((eq? m 'gender) (gender data))
              ((eq? m 'marital-status)(marital-status data))
              ((eq? m 'equals?)(equals? data))
              ((eq? m 'to-string)(to-string data))
              (else (error "Person: unknown operation error" m)))))
    ;
    ; implementation of public interface
    ;
    (define (name data) (car data))   ; data = (name gender marital-status)
    (define (gender data) (cadr data))
    (define (marital-status data) (caddr data))
    (define (equals? data)
      (lambda (p) (equal? (string-upcase (name data)) (string-upcase (p 'name))))) 
    ;
    (define (to-string data)
      (string-append 
        "(" (name data) "," (gender data) "," (marital-status data) ")"))
    ;
    ; implementation of static interface
    ;
    (define male '())
    (define female '())
    (define single '())
    (define single-male '())
    (define single-or-female '())
    ;
    (define (people)
      (list (Person "Robert" "Male" "Single")
            (Person "John" "Male" "Married")
            (Person "Laura" "Female" "Married")
            (Person "Diana" "Female" "Single")
            (Person "Mike" "Male" "Single")
            (Person "Bobby" "Male" "Single")))
    ;
    (define (print-list seq)
      (map (lambda (p) (display (p 'to-string))(display "\t")) seq))
    ;
    (define (filter-list seq predicate)
      seq)
    ; returning static interface
    ;
    (lambda args
      (if (null? (cdr args))          ; single argument       
        (let ((m (car args)))
          (cond ((eq? m 'people) (people))
                ((eq? m 'print) print-list)
                ((eq? m 'filter) filter-list)
                ((eq? m 'male) male)
                ((eq? m 'female) female)
                ((eq? m 'single) single)
                ((eq? m 'singleMale) single-male)
                ((eq? m 'singleOrFemale) single-or-female)
                (else (error "Person: unknown static member error" m))))
        (this args)))))               ; returning object instance


(define john2 (Person "John" "Male" "Married"))
(define notJohn '())

(define people (Person 'people))
(define males ((Person 'filter) people (Person 'male)))
(define females ((Person 'filter) people (Person 'female)))
(define singleMales ((Person 'filter) people (Person 'singleMale)))
(define singleOrFemales ((Person 'filter) people (Person 'singleOrFemale)))
(define notJohns ((Person 'filter) people notJohn))

(display "Everyone:\t\t")((Person 'print) people)
(display "\nNot John:\t\t")((Person 'print) notJohns)
(display "\nSingle or Female:\t")((Person 'print) singleOrFemales)
(display "\nMales:\t\t\t")((Person 'print) males)
(display "\nSingle Males:\t\t")((Person 'print) singleMales)
(display "\nFemales:\t\t")((Person 'print) females)
(newline)


