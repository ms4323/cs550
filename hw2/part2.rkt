#lang racket
(require racket/trace)

(define-syntax-rule (mydelay expr) (lambda () expr))

(define-syntax-rule (s-cons a b) (cons a (mydelay b)))

(define (myforce expr) (expr))
 
(define (s-first s) (car s))

(define (s-rest s) (myforce (cdr s)))

(define empty-s '())

(define s-empty? null?)

(define stream-enumerate-interval
     (lambda (start end)
       (if (= start end)
           (stream end)
           (s-cons start (stream-enumerate-interval (+ 1 start) end)))))

(define (divides? a b) (= (remainder b a) 0))

(define (prime-test s n)
  (cond
    ((s-empty? s) #f)
    ((divides? (s-first s) n) #f)
    (else (prime-test (s-rest s) n))))

(define prime?
  (lambda (n)
    (cond ((or (= n 1) (= n 0)) #f)
          ((= n 2) #t)
          ((even? n) #f)
          (else (prime-test (stream-enumerate-interval 2 (- n 1)) n )))))

(define (s-filter pred s)
      (cond ((s-empty? s) empty-s)
            ((pred (s-first s)) (s-cons (s-first s) (s-filter pred (s-rest s))))
            (else (s-filter pred (s-rest s)))))


(trace prime?)