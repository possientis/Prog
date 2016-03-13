; the todo macro

(import '(java.util Calendar))

(defn the-past-midnight-1 []
  (let [calendar-obj (Calendar/getInstance)]
    (.set calendar-obj Calendar/AM_PM Calendar/AM)
    (.set calendar-obj Calendar/HOUR 0)
    (.set calendar-obj Calendar/MINUTE 0)
    (.set calendar-obj Calendar/SECOND 0)
    (.set calendar-obj Calendar/MILLISECOND 0)
    (.getTime calendar-obj)))


(println (the-past-midnight-1))

; using the todo macros allows to eliminate duplication 
; of calendar-obj reference

(defn the-past-midnight-2 []
  (let [calendar-obj (Calendar/getInstance)]
    (doto calendar-obj                  ; feels like VBA construct 'with'
      (.set Calendar/AM_PM Calendar/AM)
      (.set Calendar/HOUR 0)
      (.set Calendar/MINUTE 0)
      (.set Calendar/SECOND 0)
      (.set Calendar/MILLISECOND 0))
    (.getTime calendar-obj)))           ; why isnt this inside 'todo' block?

(println (the-past-midnight-2))

(defn the-past-midnight-3 []
  (let [calendar-obj (Calendar/getInstance)]
    (doto calendar-obj                  ; feels like VBA construct 'with'
      (.set Calendar/AM_PM Calendar/AM)
      (.set Calendar/HOUR 0)
      (.set Calendar/MINUTE 0)
      (.set Calendar/SECOND 0)
      (.set Calendar/MILLISECOND 0)
      (.getTime))))                     ; seems to work too !!!


(println (the-past-midnight-3))








