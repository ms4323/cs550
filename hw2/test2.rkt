#lang racket
(require rackunit)
(require rackunit/text-ui)
(require "part2_mceval.rkt")

(define (test-mceval exp)
  (with-handlers ([exn:fail? (lambda (exn) exn)])
    (mceval exp (setup-environment))))


(define delay-force-tests
  (test-suite
   "Test delay and force"
   (check-equal? (test-mceval '(begin (delay (error)) 3))
                 3
                 "(begin (delay (error)) 3)")
   (check-equal? (test-mceval '(force (delay 3)))
                 3
                 "(force (delay 3))")
   (check-equal? (test-mceval '((delay 5)))
                 5
                 "((delay 5))")
   (check-equal? (test-mceval '(let ((x (delay 3))) (force x)))
                 3
                 "(let ((x (delay 3))) (force x))")
   (check-equal? (test-mceval '(force (delay (force (delay 3)))))
                 3
                 "(force (delay (force (delay 3))))")
   (check-equal? (test-mceval '(let ((x (delay (+ 1 2)))) (+ (force x) (force x))))
                 6
                 "(let ((x (delay (+ 1 2)))) (+ (force x) (force x)))")
   (check-equal? (test-mceval '(let ((x 0))
                                 (let ((y (delay (begin (set! x (+ x 1)) x))))
                                   (+ (force y) (force y)))))
                 2
                 "Delayed expression with side-effect")))

(define stream-tests
  (test-suite
   "Test streams"
   (check-equal? (test-mceval '(stream-empty? empty-stream))
                 #t
                 "(stream-empty? empty-stream)")
   (check-equal? (test-mceval '(stream-first (stream-cons 1 empty-stream)))
                 1
                 "(stream-first (stream-cons 1 empty-stream))")
   (check-equal? (test-mceval '(stream-empty? (stream-rest (stream-cons 1 empty-stream))))
                 #t
                 "(stream-empty? (stream-rest (stream-cons 1 empty-stream)))")
   (check-equal? (test-mceval '(stream-first (stream-cons 1 (error))))
                 1
                 "(stream-first (stream-cons 1 (error)))")
   (check-equal? (test-mceval '(stream-first (stream-cons (+ 2 3) (stream-cons (+ 2 3) (error)))))
                 5
                 "(stream-first (stream-cons (+ 2 3) (stream-cons (+ 2 3) (error))))")
   (check-equal? (test-mceval '(stream-first (stream-rest (stream-cons (+ 2 3) (stream-cons (+ 2 3) (error))))))
                 5
                 "(stream-first (stream-rest (stream-cons (+ 2 3) (stream-cons (+ 2 3) (error)))))")))
  
(run-tests delay-force-tests)
(run-tests stream-tests)
