(ns stubbing)

(def ^:dynamic mock-calls)

(defmacro defmocktest [test-name & body]
  `(test/deftest ~test-name
     (binding [mock-calls (atom {})]
       (do ~@body))))


(defmacro stubbing [stub-forms & body]
  (let [stub-pairs (partition 2 stub-forms)
        returns (map last stub-pairs)
        stub-fns (map #(list 'constantly %) returns)
        real-fns (map first stub-pairs)]
    `(binding [~@(interleave real-fns stub-fns)]
       ~@body)))


(defn stub-fn [the-function return-value]
  (swap! mock-calls assoc the-function [])
  (fn [& args]
    (swap! mock-calls update-in [the-function] conj args)
    return-value))


(defmacro stubbing2 [stub-forms & body]
  (let [stub-pairs (partition 2 stub-forms)
        real-fns (map first stub-pairs)
        returns (map last stub-pairs)
        stub-fns (map #(list 'stub-fn %1 %2) real-fns returns)]
    `(binding [~@(interleave real-fns stub-fns)]
       ~@body)))


(defn mock-fn [the-function]
  (stub-fn the-function nil))

(defmacro mocking [fn-names & body]
  (let [mocks (map #(list 'mock-fn (keyword %)) fn-names)]
    `(binding [~@(interleave fn-names mocks)]
       ~@body)))

(defmacro verify-call-times-for [fn-name number]
  `(test/is (= ~number (count (@mock-calls ~(keyword fn-name))))))

(defmacro verify-nth-call-args-for [n fn-name & args]
  `(test/is (= '~args (nth (@mock-calls ~(keyword fn-name)) (dec ~n)))))

(defmacro verify-first-call-args-for [fn-name & args]
  `(verify-nth-call-args-for 1 ~fn-name ~@args))

(defn clear-calls []
  (reset! mock-calls {}))





