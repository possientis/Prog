; doesn't work yet
;(import '(java.util.ArrayList))

; actually it may do, just need to be careful with syntax
(import '(java.util ArrayList))

; but we still have a problem

;(defn start []
;  (let [l (ArrayList. 3)] ; (new ArrayList 3)
;    (.set l 0 "abc")      
;    (.set l 1 "def")
;    (.set l 2 "ghi")))
;    (println (.get l 0))
;    (println (.get l 1))
;    (println (.get l 2))))

(def my-list (new ArrayList 3))
(def your-list (ArrayList. 3))

(.set my-list 0 "abc")
