; incorrect

(defmacro def-logged-fn [fn-name args & body]
  `(defn ~fn-name ~args
     (let [now (System/currentTimeMillis)]
       (println "[" now "] Call to" (str (var ~fn-name)))
       ~@body)))

(println (var println)) ; #'clojure.core/println

(def x 23)
(println (var x))       ; #'user/x
(println (str (var x))) ; idem

(println (str (macroexpand-1 '(def-logged-fn printname [name]
  (println "hi" name)))))

(clojure.core/defn printname [name] 
  (clojure.core/let [now (java.lang.System/currentTimeMillis)] 
    (clojure.core/println "[" now "] Call to" (clojure.core/str (var printname))) 
    (println "hi" name)))

(printname "john")

(defmacro def-logged [fn-name args & body]
  `(defn ~fn-name ~args
     (let [now# (System/currentTimeMillis)] ; unique variable name generated to avoid capture 
       (println "[" now# "] Call to" (str (var ~fn-name)))
       ~@body)))

(println (str (macroexpand-1 '(def-logged printName [name] (println "hi" name)))))

(comment  ; multiline comment 

(clojure.core/defn printName [name] 
  (clojure.core/let [now__17__auto__ (java.lang.System/currentTimeMillis)] 
    (clojure.core/println "[" now__17__auto__ "] Call to" (clojure.core/str (var printName))) 
    (println "hi" name)))
)
(println "start")
(println (str (macroexpand-1 '(comment (println "hello world"))))) 
(println "end")


; (comment (( ) needs a syntactically correst S-expression in inside
; or use ""

(comment "any nonsen
         you want (((
         ")

; using macro
(def-logged printName [name]
  (println "hi" name))

(printname "john")

(println (str (macroexpand '(declare add multiply subtract divide))))
; (do (def add) (def multiply) (def subtract) (def divide))

(println (str (macroexpand '(defn f [x] (* x x)))))

(def f (fn ([x] (* x x))))
(println (f 5))
(def g (fn [x] (* x x )))
(println (g 5))



