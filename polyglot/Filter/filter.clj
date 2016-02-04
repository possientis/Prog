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

(def Predicate            ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :test) (p-test data)
               (= m :not)  (p-not data)
               (= m :and)  (p-and data)
               (= m :or)   (p-or data)
               :else (println(format"Predicate: unknown operation error: %s" m)))))
     ;
     ; implementation of public interface
     ;
     (p-test [data] data) ; data is of type Person -> Bool
     ;
     (p-not [data] (Predicate (fn [x] (not (data x))))) 
     ;
     (p-and [data] 
       (fn [other] (Predicate (fn [x] (and (data x) ((other :test) x))))))
     ;
     (p-or [data]
       (fn [other] (Predicate (fn [x] (or (data x) ((other :test) x))))))
     ;
     ; implementation of static interface
     ;
     (is-equal [target-ref]
       (Predicate (fn [x] ((x :equals?) target-ref)))) 
     ;
     ; definition of single argument static interface
     (class-object [arg]
       (if (keyword? arg)
         (cond (= arg :equal?) is-equal
               :else (println(format "Predicate: unknown static op error: %s" arg)))
         ; single constructor argument is not a keyword
         (this arg)))]  ; returning class instance. 'arg' of type Person -> Bool
    ;
    ; returning static interface
    ;
    class-object))

(def Person               ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :name)            (p-name data)
               (= m :gender)          (gender data)
               (= m :marital-status)  (marital-status data)
               (= m :equals?)         (equals? data)
               (= m :to-string)       (to-string data)
               :else (println(format "Person: unknown operation error: %s" m))))) 
     ;
     ; implementation of instance public interface
     ;
     (p-name [[pname gender maritalStatus]] pname)
     (gender [[pname gender maritalStatus]] gender)
     (marital-status [[pname gender maritalStatus]] maritalStatus)
     ;
     (equals? [[pname gender maritalStatus]]
       (fn [other] (= (.toUpperCase pname) (.toUpperCase (other :name)))))
     ;
     (to-string [[pname gender maritalStatus]] 
       (str "(" pname "," gender "," maritalStatus ")"))  ; append
     ;
     ; implementation of static interface
     ;
     (male []   (Predicate (fn [p](= (.toUpperCase (p :gender)) "MALE"))))
     (female [] (Predicate (fn [p](= (.toUpperCase (p :gender)) "FEMALE"))))
     (single [] (Predicate (fn [p](= (.toUpperCase (p :marital-status))"SINGLE"))))
     (single-male []       (((single) :and) (male)))
     (single-or-female []  (((single) :or) (female)))
     ;
     (people []
       (list (Person "Robert" "Male" "Single")
             (Person "John" "Male" "Married")
             (Person "Laura" "Female" "Married")
             (Person "Diana" "Female" "Single")
             (Person "Mike" "Male" "Single")
             (Person "Bobby" "Male" "Single")))
     ;
     (print-list [plist]
       ; 'map' seems to be lazy, using 'dorun' to force evaluation
       (dorun (map (fn [p] (print (p :to-string) "\t")) plist)))
     ;
     (filter-list [plist predicate]
       (if (nil? predicate) plist (filter (predicate :test) plist)))
     ;
     ; definition of static interface
     ;
     (class-object [& args]
       (let [[x y z] args]
         (if (keyword? x)
           (cond (= x :people)            (people)
                 (= x :print)             print-list 
                 (= x :filter)            filter-list
                 (= x :male)              (male)
                 (= x :female)            (female)
                 (= x :single)            (single)
                 (= x :singleMale)        (single-male)
                 (= x :singleOrFemale)    (single-or-female)
                 :else (println 
                        (format "Person: unknown static operation error: %s" x)))
          ; first constructor argument not a keyword
           (this [x y z]))))]  ; returning instance, no argument validation
    ;
    ; returning static interface
    ;
    class-object))

(def john2 (Person "John" "Male" "Married"))
(def notJohn (((Predicate :equal?) john2) :not))

(def people            (Person :people))
(def males            ((Person :filter) people (Person :male))) 
(def females          ((Person :filter) people (Person :female))) 
(def singleMales      ((Person :filter) people (Person :singleMale))) 
(def singleOrFemales  ((Person :filter) people (Person :singleOrFemale))) 
(def notJohns         ((Person :filter) people notJohn))

(print "Everyone:\t\t")         ((Person :print) people)
(print "\nNot John:\t\t")       ((Person :print) notJohns)
(print "\nSingle or Female:\t") ((Person :print) singleOrFemales)
(print "\nMales:\t\t\t")        ((Person :print) males)
(print "\nSingle Males:\t\t")   ((Person :print) singleMales)
(print "\nFemales:\t\t")        ((Person :print) females)
(print "\n")



