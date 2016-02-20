; destructuring
; pattern matching
(def my-vector [:a :b :c :d])
(def my-nested-vector [:a :b :c :d [:x :y :z]])
(def my-list (list :a :b :c :d))


(let [[a b c d] my-vector]
  (println a b c d))


(let [[a _ _ d [x y z]] my-nested-vector]
  (println a d x y z))

(let [[a b c] my-vector]
  (println a b c))

(let [[a b & the-rest] my-vector]
  (println a b the-rest))

(let [[a b c d e f g h] my-vector]
  (println a b c d e f g h))

(let [[:as all] my-vector]
  (println all))

(let [[a :as all] my-vector]
  (println a all))

(let [[a _ _ _ [x y z :as nested] :as all] my-nested-vector]
  (println a x y z nested all))

(let [[a b & the-rest :as all] my-vector]
  (println a b the-rest all))


(defn foo [a b & more-args]
  (println a b more-args))

(foo :a :b)
(foo :a :b :c)
(foo :a :b :c :d)

(defn bar [a b & [x y z]]
  (println a b x y z))

(bar :a :b)
(bar :a :b :c)
(bar :a :b :c :d)
(bar :a :b :c :d :e)
(bar :a :b :c :d :e :f)

(def my-hashmap {:a "A" :b "B" :c "C" :d "D"})
(def my-nested-hashmap {:a "A" :b "B" :c "C" :d "D" :q {:x "X" :y "Y" :z "Z"}})
(def my-test {"A" 0 "B" 1 "C" 2})

(let [{a :a d :d} my-hashmap]
  (println a d))

(let [{a :a b :b {x :x y :y} :q} my-nested-hashmap]
  (println a b x y))

(let [{a :a, not-found :not-found, b :b} my-hashmap]
  (println a not-found b))

(let [{x "A" z "C"} my-test]
  (println x z))

(let [{a :a, not-found :not-found, b :b, :or {not-found ":)"}} my-hashmap]
  (println a not-found b))

(let [{a :a, b :b, :as all} my-hashmap]
  (println a b all))

(let [{a :a, b :b, not-found :not-found, :or {not-found ":)"}, :as all} my-hashmap]
  (println a b not-found all))

(let [{:keys [a d]} my-hashmap]
  (println a d))

(let [{:keys [a b], {:keys [x y]} :q} my-nested-hashmap]
  (println a b x y))

(let [{:strs [a d]} {"a" "A", "b" "B", "c" "C", "d" "D"}]
  (println a d))

(let [{:syms [a d]} {'a "A", 'b "B", 'c "B", 'd "D"}]
  (println a d))

(let [{:keys [a b]} '("X", "Y", :a "A", :b "B")]
  (println a b))

(defn baz [a b & {:keys [x y]}]
  (println a b x y))

(baz :a :b)
(baz :a :b :x 3)
(baz :a :b :x :c)
(baz :a :b :x :c :y :d)


(println (conj {:e "E"} my-hashmap))
(println (assoc my-hashmap :e "E"))
(println (my-hashmap :a))



