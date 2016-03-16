; bean macro very useful to convert java bean object into hashmap
(import '(java.util Calendar))

(def x (bean (Calendar/getInstance)))
(println x)
