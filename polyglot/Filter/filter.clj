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
     ; implementation of public interface
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
    (people []
      (list (Person "Robert" "Male" "Single")
            (Person "John" "Male" "Married")
            (Person "Laura" "Female" "Married")
            (Person "Diana" "Female" "Single")
            (Person "Mike" "Male" "Single")
            (Person "Bobby" "Male" "Single")))
     ;
     (print-list [plist]
       (map (fn [p] (print (p :to-string))) plist))]
    ;
    ;
    ; returning static interface
    ;
    (fn [& args]
      (let [[x y z] args]
        (if (keyword? x)
          (cond (= x :people) (people)
                (= x :print) print-list 
                :else (println 
                        (format "Person: unknown static operation error: %s" x)))
          ; first constructor argument not a keyword
          (this [x y z]))))))  ; returning instance 


(def john2 (Person "John" "Male" "Married"))
(println (john2 :to-string))
(map (fn [x] (print x)) '(1 2 3 4))
;((Person :print) (Person :people))

(println "complete")




