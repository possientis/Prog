(declare new-object)

(defn new-class [class-name]
  (fn klass [command & args]    ; we are giving a name to lambda
    (condp = command
      :name (name class-name)   ; 'name' converts symbol to string
      :new (new-object klass)))); this feels similar to scheme 'named-let'

(defmacro defclass [class-name]
  `(def ~class-name (new-class '~class-name)))

(defclass Person)

(println (Person :name))  ; Person

(defn new-object [klass]
  (let [state (ref {})]
    (fn [command & args]
      (condp = command
        :class klass
        :class-name (klass :name)
        :set! (let [[k v] args] ; destructuring optional vector args
                (dosync (alter state assoc k v))
                nil)
        :get (let [[key] args]
               (key @state))))))

(def cindy (new-object Person))

(println (cindy :class))          ; #<user$new_class$fn__1 user$new_class$fn__1@3d1cfad4>
(println ((cindy :class) :name))  ; Person
(println (cindy :class-name))     ; Person

(def nancy (Person :new))

(println (nancy :class-name))

(nancy :set! :name "Nancy Warhol")
(println (nancy :get :name))  ; Nancy Warhol

(nancy :set! :name "Nancy Drew")
(println (nancy :get :name))  ; Nancy Drew

(defn method-spec [sexpr]
  (let [name (keyword (second sexpr))
        body (next sexpr)]
    [name (conj body 'fn)]))

(def sexpr '(method age [] (* 2 10)))

(println sexpr)               ; (method age [] (* 2 10))
(println (second sexpr))      ; age 
(println (next sexpr))        ; (age [] (* 2 10))
(println (rest sexpr))        ; (age [] (* 2 10))
(println (method-spec sexpr)) ; [:age (fn age [] (* 2 10))]

(defn method-specs [sexprs]
  (->> sexprs
       (filter #(= 'method (first %)))
       (mapcat method-spec)
       (apply hash-map)))
















