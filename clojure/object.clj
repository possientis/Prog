; adapted from Scheme:

(def MyClass  ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :foo) (foo data)
               (= m :bar) (bar data)
               (= m :baz) (baz data)
               :else (println "MyClass: unknown operation error" m))))
     ;
     (foo [data] "foo is a property value") 
     ;
     (bar [data]
       (fn [arg] (println "bar is a method taking one argument: " arg)))
    ;
    (baz [data] data)]
    ;
    ; returning one argument constructor 
    ;
    (fn [value] (this value))))

(def myObject (MyClass 42))
(println (myObject :foo))
((myObject :bar) "Hello, world!")
(println "The object has value: " (myObject :baz))

; Unlike Scheme, Clojure natively supports dictionary.
; it also allows the syntax (myDict :key)

(def YourClass  ; constructor
  (letfn
    ; object created from data is essentially a dictionary
    [(this [data]
       (let [interface {:foo (foo data) 
                        :bar (bar data)
                        :baz (baz data)}]
         (fn [m] (interface m (println "YourClass: unknown operation error" m)))))
     ;
     (foo [data] "foo is a property value")
     ;
     (bar [data]
       (fn [arg] (println "bar is a method taking one argument: " arg)))
     ;
     (baz [data] data)]
    ;
    ; returning one argument constructor
    ;
    (fn [value] (this value))))

(def yourObject (YourClass 42))
(println (yourObject :foo))
((yourObject :bar) "Hello, world!")
(println "The object has value: " (yourObject :baz))
(yourObject :zzz)







