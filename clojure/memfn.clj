; using memfn

; you need to create anonymous function because member functions
; cannot be used as regular higher-order clojure functions
(def seq1 (map (fn [x] (.getBytes x)) ["amit" "rob" "kyle"]))
(def seq2 (map #(.getBytes %) ["amit" "rob" "kyle"]))

(println seq1) ; (#<byte[] [B@1356d4d4> #<byte[] [B@c03cf28> #<byte[] [B@1329eff>)
(println seq2) ; (#<byte[] [B@46fa7c39> #<byte[] [B@1fb700ee> #<byte[] [B@4f67eb2a>)

(println (= seq1 seq2)) ; false


; this is where the memfn function (macro?) comes in
(def seq3 (map (memfn getBytes) ["amit" "rob" "kyle"]))
(println seq3)


(println (.subSequence "Clojure" 2 5))  ; oju
; no verbosity gain, but may be useful
(println ((memfn subSequence start end) "Clojure" 2 5))


