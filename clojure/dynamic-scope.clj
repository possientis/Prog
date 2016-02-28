; dynamic scope in action
(def ^:dynamic *eval-me* 10)

(defn print-the-var [label]
  (println label *eval-me*))

(print-the-var "A:")        ;; 10
(binding [*eval-me* 20]     ;; the first binding 
  (print-the-var "B:")      ;; 20
  (binding [*eval-me* 30]   ;; the second binding
    (print-the-var "C:"))   ;; 30
  (print-the-var "D:"))     ;; 20
(print-the-var "E:")        ;; 10

; lexical scope in action
(def eval-me 100)

(defn print-the-let [label]
  (println label eval-me))

(print-the-let "A:")        ;; 100
(let [eval-me 200]          
  (print-the-let "B:")      ;; 100
  (let [eval-me 300]
    (print-the-let "C:"))   ;; 100
  (print-the-let "D:"))     ;; 100
(print-the-let "E:")        ;; 100
