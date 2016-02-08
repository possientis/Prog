; doesn't work yet
(import '(java.util.ArrayList))

(defn start []
  (let [l (ArrayList. 3)]
    (.set l 0 "abc")
    (.set l 1 "def")
    (.set l 2 "ghi"))
  (println (.get l 0))
  (println (.get l 1))
  (println (.get l 2)))
