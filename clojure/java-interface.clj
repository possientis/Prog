; implementing java abstract class or interface

(def x
  (proxy [Runnable] []
  (run []
    (println "Runnable was called"))))

(.run x)




