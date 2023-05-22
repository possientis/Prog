(def untrusted (with-meta {:command "clean-table" :subject "users"} ; actual value
                          {:safe false :io true}))  ; meta data, not part of value

(println untrusted) ; meta data does not appear
(println (meta untrusted))  ; meta function to retrieve meta data

(def still-suspect (assoc untrusted :complete? false))
(println still-suspect)
(println (meta still-suspect))  ; meta data carries over


(defn 
  testing-meta "testing meta data for functions"
  {:safe true :console true}
  []
  (println "Hello from meta!"))

(testing-meta)  ; Hello from meta!
(println (meta testing-meta)) ; nil
; meta data not associated with function object itself
; meta data is associated with the var testing-meta

; TODO: fix the ${HOME} issue
(println (meta (var testing-meta))) 
; { :ns       #<Namespace user>, 
;   :name     testing-meta, 
;   :file     ${HOME}/Prog/clojure/meta-example.clj, 
;   :column   1, 
;   :line     12, 
;   :console  true, 
;   :safe     true, 
;   :arglists ([]), 
;   :doc      testing meta data for functions
; }


