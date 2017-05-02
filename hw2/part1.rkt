#lang racket
(require racket/stream)
(require math/number-theory)
(require racket/trace)

(define stream-enumerate-interval
     (lambda (start end)
       (if (= start end)
           (stream end)
           (stream-cons start (stream-enumerate-interval (+ 1 start) end)))))

(stream-first
  (stream-rest
    (stream-filter prime?
                 (stream-enumerate-interval 10000 1000000))))
                                 
(trace stream-enumerate-interval)