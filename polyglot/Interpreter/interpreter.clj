; Interpreter Design Pattern
(ns interpreter 
  (:gen-class)
  (:require [clojure.string :as string]))
; from the Gang of Four book:
; "If a particular kind of problem occurs often enough, then it might be
; worthwhile to express instances of the problem as sentences in a simple
; language. Then you can build an interpreter that solves the problem by 
; interpreting these sentences. For example, searching for strings that 
; match a pattern is a common problem. Regular expressions are a standard 
; language for specifying patterns of strings. Rather than building custom 
; algorithms to match each pattern against strings, search algorithms could 
; interpret a regular expression that specifies a set of strings to match."
;
; Each regular expression r has an associated language L(r) (which is a set
; of strings) defined by the recursion:
;
;  - r = Lit(s)        -> L(r) = {s}
;  - r = And(r1, r2)   -> L(r) = L(r1).L(r2)     (see definition of '.')
;  - r = Or(r1, r2)    -> L(r) = L(r1) U L(r2)
;  - r = Many(r1)      -> L(r) = U_k L(r1)^k     (see definition of '.')
;
;  where given A,B sets of strings the product A.B is defined as the set of 
;  strings A.B = { a ++ b | a in A, b in B }, and where it is understood that
;  A^0 = {""} and A^1 = A. 
;
; Given a regular expression r and a string s, many reasonable questions 
; can be asked in relation to r and s. When using the command 'grep', the
; question being asked is whether there exist a substring s' of s which
; belongs to the language of r. One of the first questions of interest is
; of course whether s itself belongs to L(r).

(defmulti to-string :type)
(defmulti interpret :type)   

; Exp virtual table
(defmethod to-string ::exp [data] (throw (Exception. "to-string not implemented")))
(defmethod interpret ::exp [data] (throw (Exception. "interpret not implemented")))

; Lit virtual table
(derive ::lit ::exp)
(defmethod to-string ::lit [data] (:literal data))
(defmethod interpret ::lit [data] 
  (fn [input]
    (let [literal (:literal data)]
      (if (.startsWith  input literal)
        (list literal)
        '())))) 


; And virtual table
(derive ::and ::exp)
(defmethod to-string ::and [ {:keys [left right]} ]
  (str (left :to-string) (right :to-string)))
(defmethod interpret ::and [ {:keys [left right]} ]
  (fn [input]
    (let [left-list ((left :interpret) input)]
      (for [s1 left-list
            remainder (list (.substring input (.length s1)))
            right-list (list ((right :interpret) remainder))
            s2 right-list]
            (str s1 s2)))))

; Or virtual table
(derive ::or ::exp)
(defmethod to-string ::or [ {:keys [left right]} ]
  (str "(" (left :to-string) "|" (right :to-string) ")"))
(defmethod interpret ::or [ {:keys [left right]} ] 
  (fn [input]
    (concat ((left :interpret) input) ((right :interpret) input))))



; Many virtual table
(derive ::many ::exp)
(defmethod to-string ::many [data] (str "(" ((:regex data) :to-string) ")*"))
(defmethod interpret ::many [data] 
  (fn [input]
    (let [regex (:regex data)
          left-list ((regex :interpret) input)]
      (for [s1 (filter #(not (= "" %)) left-list)
            remainder (list (.substring input (.length s1)))
            right-list (list ((interpret data) remainder))  ; recursive call
            s2 right-list] 
        (str s1 s2)))))

; not virtual
(defn recognize [data] (fn [input] :TODO))

(def Exp  ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :to-string) (to-string data)
               (= m :interpret) (interpret data)
               (= m :recognize) (recognize data)
               :else (throw (Exception. "Exp: unknown operation error")))))]
    ;
    ; returning single argument constructor
    ;
    (fn [data] (this data))))

(def Lit  ; constructor
  ; returning single argument constructor
  (fn [literal]
    (Exp {:type ::lit :literal literal})))

(def And  ; constructor
  ; returning two arguments constructor
  (fn [left right]
    (Exp {:type ::and :left left :right right})))

(def Or   ; constructor
  ; returning two arguments constructor
  (fn [left right]
    (Exp {:type ::or :left left :right right})))

(def Many ; constructor
  ; returning single argument constructor
  (fn [regex]
    (Exp {:type ::many :regex regex})))



(defn -main []
  (def a (Lit "a"))
  (def b (Lit "b"))
  (def c (Lit "c"))

  (def aa (And a (Many a))) ; one or more 'a'
  (def bb (And b (Many b))) ; onr or more 'b'
  (def cc (And c (Many c))) ; one or more 'c'

  (def regex (Many (And (Or aa bb) cc)))
  (def input "acbbccaaacccbbbbaaaaaccccc")
  (println "regex =" (regex :to-string))
  (println "string =" (str "\"" input "\""))
  (println "The recognized prefixes are:")

  (println((aa :interpret) "aaabcde"))

  (def x '("" "a" "aa" "aaa"))

  (def y (filter #(not (= "" %)) x))
  (println x)
  (println y)

  (println "exiting now ...")
)


