; clojurec -cp /usr/share/java/clojure-contrib.jar parse_line
(ns parse_line
  (:require [clojure.contrib.io :as io])
  (:gen-class))

(defn parse-line [line]
  (let [tokens (.split (.toLowerCase line) " ")]
    (map #(vector % 1) tokens)))


;([twas 1] [brillig 1] [and 1] [the 1] [slithy 1] [toves 1])
(println (parse-line "Twas brillig and the slithy toves"))

; ????????
(defn combine [mapped]
  (->> (apply concat mapped)
       (group-by first)
       (map (fn [[k v]]
              {k (map second v)}))
       (apply merge-with conj)))

(def lines (io/read-lines "jabberwocky.txt"))

(println (str lines)) ; clojure.lang.LazySeq@cc97fe7e


; Twas brillig and the slithy toves
; Did gyre and gimble in the wabe
; All mimsy were the borogoves
; And the mome raths outgrabe
(doseq [l lines]
  (println l))


; ([twas 1] [brillig 1] [and 1] [the 1] [slithy 1] [toves 1] [did 1] [gyre 1] 
; [and 1] [gimble 1] [in 1] [the 1] [wabe 1] [all 1] [mimsy 1] [were 1] [the 1] 
; [borogoves 1] [and 1] [the 1] [mome 1] [raths 1] [outgrabe 1])
(println (apply concat (map parse-line lines)))

(defn -main []
  :ok)
