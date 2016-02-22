(declare hat) ; required declare statement

; mutually recursive functions which will blow
; the stack for large enough input
(defn cat [n]
  (if-not (zero? n)
    (do
        (if (= 0 (rem n 100))
          (println "cat:" n))
      (hat (dec n)))))

(defn hat [n]
  (if-not (zero? n)
    (do
        (if (= 0 (rem n 100))
          (println "hat:" n))
      (cat (dec n)))))


(declare hatt)

; function returns a thunk rather than making recursive call
(defn catt [n]
  (if-not (zero? n)
    (do
        (if (= 0 (rem n 100))
          (println "catt:" n))
      #(hatt (dec n)))))  ; lambda expression shortcut

; function returns a thunk rather than making recursive call
(defn hatt [n]
  (if-not (zero? n)
    (do
        (if (= 0 (rem n 100))
          (println "hatt:" n))
;      #(catt (dec n)))))       ; shortcut
      (fn [] (catt (dec n)))))) ; same semantics

(trampoline catt 100000)        ; this won't blow the stack 
