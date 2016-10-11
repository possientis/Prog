; Proxy Design Pattern
(ns proxy (:gen-class))
; This code exercise is borrowed from Design Patterns in C# - 13 Proxy 
; https://www.youtube.com/watch?v=XvbDqLrnkmA

; A proxy is a class which functions as an interface to something else

; There are three participants to the proxy design pattern:
;
; 1. subject
; 2. real subject
; 3. proxy
;

; The subject is the common interface between the real object and proxy
; the real object is that which the proxy is meant to be substituted for

(defmulti getCpuPrice :type)
(defmulti getRamPrice :type)
(defmulti getSsdPrice :type)

; this is the subject
(def ComponentPrice         ; constructor
  (let [class-dictionary {  :getCpuPrice  getCpuPrice
                            :getRamPrice  getRamPrice
                            :getSsdPrice  getSsdPrice }]
   (letfn
    ; object created from data is message passing interface
    [(this [data]
      (fn [m] 
        (let [operation (class-dictionary m :notfound)] 
          (if (= operation :notfound)
            (throw(Exception.(format "ComponentPrice: unknown operation %s\n" m)))
            (operation data)))))]
     ;
     ; returning single argument constructor
     ;
     (fn [sub-type] (this {:type sub-type})))))

(defmethod getCpuPrice ::ComponentPrice [data]
  (throw(Exception."ComponentPrice: getCpuPrice is not implemented"))) 
(defmethod getRamPrice ::ComponentPrice [data]
  (throw(Exception."ComponentPrice: getRamPrice is not implemented"))) 
(defmethod getSsdPrice ::ComponentPrice [data]
  (throw(Exception."ComponentPrice: getSsdPrice is not implemented"))) 

; this is the real subject
(derive ::StoredComponentPrice ::ComponentPrice)
(def StoredComponentPrice   ; constructor
  (fn [] (ComponentPrice ::StoredComponentPrice)))
(defmethod getCpuPrice ::StoredComponentPrice [data] 250.0)
(defmethod getRamPrice ::StoredComponentPrice [data] 32.0)
(defmethod getSsdPrice ::StoredComponentPrice [data] 225.0)

; this is the proxy
(declare requestFromServer)
(derive ::ProxyComponentPrice ::ComponentPrice)
(def ProxyComponentPrice   ; constructor
  (fn [] (ComponentPrice ::ProxyComponentPrice)))
(defmethod getCpuPrice ::ProxyComponentPrice [data] (requestFromServer :CPU))
(defmethod getRamPrice ::ProxyComponentPrice [data] (requestFromServer :RAM))
(defmethod getSsdPrice ::ProxyComponentPrice [data] (requestFromServer :SSD))


(def Server                 ; constructor
  (let [_server (ref nil) ]
    (letfn
      ; object created from data is message passing interface
      [(this [data]
         (fn [m]
           (cond (= m :sendRequest) (sendRequest data)
                 :else (throw (Exception. (format "unknown operation %s" m))))))
       ;
       (toString [request]
         (cond (= request :CPU) "CPU"
               (= request :RAM) "RAM"
               (= request :SSD) "SSD"
               :else "???"))
       ;
       (sendRequest [data]
         (fn [request]
           (println 
             "Server receiving request for" (toString request) " price")
           ; In our example, server uses real subject
           (let [component (StoredComponentPrice)]  ; real subject
             (println 
               "Server responding to request for " (toString request) " price")
             (cond (= request :CPU) (component :getCpuPrice)
                   (= request :RAM) (component :getRamPrice)
                   (= request :SSD) (component :getSsdPrice) 
                   :else (throw (Exception. "Invalid server request"))))))
       ;
       (startServer [] 
         (println "Component pricer server running, awaiting request")
         (dosync (ref-set _server (this {}))))  ; server data = {} 
       ;
       (getInstance [] _server)
       ;
       (static-interface [& args]
         (if (empty? args)        ; no argument, returning server instance
           (this {})
           (let [m (first args)]  ; otherwise, static method call
             (cond (= m :startServer) (startServer)
                   (= m :getInstance) (getInstance)
                   :else (throw 
                           (Exception. 
                             (format "Invalid static member %s" m)))))))]
      ;
      ; simply returning static interface
      ;
      static-interface)))

(defn requestFromServer [request]
  (((Server :getInstance) :sendRequest) request))

(defn -main []
  (Server :startServer)
  ; we can use proxy as if it was real, making client code a lot simpler
  (let [prices (ProxyComponentPrice)
       cpu (prices :getCpuPrice)
       ram (prices :getRamPrice)
       ssd (prices :getSsdPrice)] 
    (println "The CPU price is" cpu)
    (println "The RAM price is" ram)
    (println "The SSD price is" ssd)))

;(-main)



