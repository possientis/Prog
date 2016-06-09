(ns rabbitmq_receiver
  (:gen-class)
  (:use test_rabbitmq))


(defn -main []
  (println "rabbitmq-receiver has started ...")
  (println "waiting ...")
  (with-rabbit ["127.0.0.1" "guest" "guest"]
    (println (next-message-from "chapter14-test")))
  (println "rabbitmq-receiver is terminating")

)
