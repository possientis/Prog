(def an-atom (atom 0))

(defn on-change [the-key the-ref old-value new-value]
  (println the-key "Hey, seeing change from" old-value "to" new-value))

(add-watch an-atom :whatever on-change) ;

(println "an-atom =" @an-atom)  ; (deref an-atom)

(swap! an-atom inc) ; :whatever Hey, seeing change from 0 to 1
(println "an-atom =" @an-atom)  ; (deref an-atom)


(swap! an-atom inc) ; :whatever Hey, seeing change from 1 to 2
(println "an-atom =" @an-atom)  ; (deref an-atom)

(remove-watch an-atom :whatever)

(swap! an-atom inc) ; no message this time, as watcher was removed
(println "an-atom =" @an-atom)  ; (deref an-atom)

