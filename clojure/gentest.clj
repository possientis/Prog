(ns gentest
   (:import (AbstractJavaClass))
   (:gen-class
    :name gentest.ConcreteClojureClass
    :extends AbstractJavaClass
    :constructors {[String] [String]
                    [String String] [String String]}
    :implements [Runnable]
    :init initialize
    :state localState
    :methods [[stateValue [] String]]
     ))
(defn -initialize
  ([s1]
   (println "Init value:" s1)
   [[s1 "default"] (ref s1)])
  ([s1 s2]
   (println "Init values:" s1 "," s2)
   [[s1 s2] (ref s2)]))
(defn -getCurrentStatus [this]
  "getCurrentStatus from - com.gentest.ConcreteClojureClass")
(defn -stateValue [this]
  @(.localState this))
(defn -run [this]
  (println "In run!")
  (println "I'm a" (class this))
  (dosync (ref-set (.localState this) "GO")))
(defn -main []
  (let [g (new gentest.ConcreteClojureClass "READY")]
    (println (.getCurrentStatus g))
    (println (.getSecret g))
    (println (.stateValue g)))
  (let [g (new gentest.ConcreteClojureClass "READY" "SET")]
    (println (.stateValue g))
    (.start (Thread. g))
    (Thread/sleep 1000)
    (println (.stateValue g))))
