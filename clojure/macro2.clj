; incorrect
(defmacro def-logged-fn [fn-name args & body]
  `(defn ~fn-name ~args
     (let [now (System/currentTimeMillis)]
       (println "[" now "] Call to" (str (var ~fn-name)))
       ~@body)))

(println (var println)) ; #'clojure.core/println

(def x 23)
(println (var x))       ; #'user/x
