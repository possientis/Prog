(defn start-job [{:keys [batch-size] :as job} args-seq] ; destructuring
  (println "batch-size:" batch-size "job:" job "args-seq:" args-seq))


; (start-job)                   ; wrong number of args
; (start-job :test)             ; wrong number of args
(start-job :arg1 :arg2)         ; batch-size: nil job: :arg1 args-seq: :arg2
; (start-job :arg1 :arg2 :arg3) ; wrong number of argument
(start-job {:batch-size 128 :field1 "text" :field2 255} :arg2)
;batch-size: 128 job: {:field2 255, :field1 text, :batch-size 128} args-seq: :arg2
