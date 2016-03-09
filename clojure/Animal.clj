; using multimethods to achieve subtype (single dispatch) polymorphism
; what is the lesson here?
; we have emulated OOP in Scheme. we need to do things differently
; in clojure, leverging on two key features:

; 1. multimethods which allows single and multiple dispatch, and not just on types
; 2. the ability to use namespace-qualified keywords ::cat ::dog  with 'derive'

(ns Animal)
(declare foo bar)
(def Animal ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [dictionary { :foo foo 
                          :bar bar }] 
         (fn [m]
           (let [operation (dictionary m :notfound)]
             (if (= operation :notfound)
               (throw (Exception. (format "Animal: unknown operation %s" m)))
               (operation data))))))]
    ;
    ; returning single argument constructor
    ;

    (fn[a-type] (this {:type a-type}))))

(derive ::cat ::animal)
(def Cat (fn [] (Animal ::cat)))

(derive ::dog ::animal)
(def Dog (fn [] (Animal ::dog)))

(defmulti foo :type)
(defmethod foo ::cat [data] (println "Cat::foo is running"))
(defmethod foo ::dog [data] (println "Dog::foo is running"))

(defmulti bar :type)
(defmethod bar ::animal [data] (println "Animal::bar is running")) 


(def c (Cat))
(def d (Dog))

(c :foo)
(d :foo)

(c :bar)
(d :bar)

(ns Person)
(println (all-ns))


