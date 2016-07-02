(declare new-object)

(defn find-method [method-name instance-methods]
  (instance-methods method-name))

(defn new-class [class-name methods]
  (fn klass [command & args]    ; we are giving a name to lambda
    (condp = command
      :name (name class-name)   ; 'name' converts symbol to string
      :new (new-object klass)   ; this feels similar to scheme 'named-let'
      :method (let [[method-name] args]
                (find-method method-name methods)))))

(declare method-specs)
(defmacro defclass [class-name & specs]
  (let [fns (or (method-specs specs) {})]
    `(def ~class-name (new-class '~class-name ~fns))))

(defn method-spec [sexpr]
  (let [name (keyword (second sexpr))
        body (next sexpr)]
    [name (conj body 'fn)]))

(defn method-specs [sexprs]
  (->> sexprs
       (filter #(= 'method (first %)))
       (mapcat method-spec)
       (apply hash-map)))

(declare ^:dynamic this)

(defclass Person
  (method age []
    (* 2 10))
  (method greet [visitor]
    (str "Hello there, " visitor))
  (method about [diff]
    (str "I was born about " (+ diff (this :age)) " years ago")))

(println (Person :name))  ; Person


(defn new-object [klass]
  (let [state (ref {})]
    (fn thiz [command & args]
      (condp = command
        :class klass
        :class-name (klass :name)
        :set! (let [[k v] args] ; destructuring optional vector args
                (dosync (alter state assoc k v))
                nil)
        :get (let [[key] args]
               (key @state))
        (let [method (klass :method command)]
          (if-not method
            (throw (RuntimeException. 
              (str "Unable to respond to " command))))
          (binding [this thiz]
            (apply method args)))))))



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

(def sexpr1 '(method age [] (* 2 10)))

(println sexpr1)               ; (method age [] (* 2 10))
(println (second sexpr1))      ; age 
(println (next sexpr1))        ; (age [] (* 2 10))
(println (rest sexpr1))        ; (age [] (* 2 10))
(println (method-spec sexpr1)) ; [:age (fn age [] (* 2 10))]


(def sexpr2 '(method say [message] (println message)))

(def sexprs (list sexpr1 sexpr2 '(other :ok :okie)))

(def filtered (filter #(= 'method (first %)) sexprs))

(println filtered)  ; ((method age [] (* 2 10)) (method say [message] (println message)))

(println (map method-spec filtered))  ; ([:age (fn age [] (* 2 10))] [:say (fn say [message] (println message))])

(println (mapcat method-spec filtered)) ; (:age (fn age [] (* 2 10)) :say (fn say [message] (println message)))

(println (hash-map :age :object1 :say :object2))  ; {:say :object2, :age :object1}
(println (apply hash-map (mapcat method-spec filtered)))  ; {:say (fn say [message] (println message)), :age (fn age [] (* 2 10))}
(println (method-specs sexprs))                           ; {:say (fn say [message] (println message)), :age (fn age [] (* 2 10))}

(println (Person :method :age))   ; #<user$age user$age@3f6b0be5>
(println ((Person :method :age))) ; 20

(def shelly (Person :new))
(println (shelly :age)) ; 20
(println (shelly :greet "Nancy")) ; Hello there, Nancy
(println (shelly :about 2))       ; I was born about 22 years ago


















