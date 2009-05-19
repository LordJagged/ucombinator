
(define (odd? n) (= (modulo n 2) 1))

(define (even? n) (= (modulo n 2) 0))

(define (cons a b) (lambda (on-cons on-nil) (on-cons a b)))

(define (car c) (c (lambda (a b) a) (lambda () #f)))

(define (cdr c) (c (lambda (a b) b) (lambda () #f)))

(define (cadr c) (car (cdr c)))

(define (error message) (display message))