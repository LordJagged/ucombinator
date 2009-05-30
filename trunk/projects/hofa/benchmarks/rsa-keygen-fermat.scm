;; Fermat and Solovay-Strassen primality testing in Scheme.

;; Author: Matthew Might
;; Site:   http://matt.might.net/


;; Mathematical support.

; square(x) = x^2
(define (square x) (* x x))

; modulo-power: a fast modular exponentiation routine.
; modulo-power(base,exp,n) = base^exp [mod n]
(define (modulo-power base exp n)
  (if (= exp 0)
      1
      (if (odd? exp)
          (modulo (* base (modulo-power base (- exp 1) n)) n)
          (modulo (square (modulo-power base (/ exp 2) n)) n))))


; jacobi: computes the Jacobi symbol, an extension of the Legendre symbol.
(define (jacobi a n)
  (cond
    ((= n 1) 1)
    ((= a 1) 1)
    ((not (= (gcd a n) 1)) 0)
    ((and (= a 2)
          (let ((n-mod-8 (modulo n 8)))
            (cond 
              ((or (= n-mod-8 1) (= n-mod-8 7)) 1)
              ((or (= n-mod-8 3) (= n-mod-8 5)) -1)))))
    ((> a n) (jacobi (modulo a n) n))    
    ((even? a) (* (jacobi (/ a 2) n) (jacobi 2 n)))    
    ((even? n) (* (jacobi a (/ n 2)) (jacobi a 2)))
    (else (* (jacobi n a) (if (even? (/ (* (- a 1) (- n 1)) 4)) 1 -1)))))
                              
    


;; Random number utilities.

(define (random-char) 
  (call-with-input-file "/dev/random" 
    (lambda (port)
     (read-char port))))

(define (random-num)
  (let ((n (char->integer (random-char))))
    (if (= n 65533)
        (random-num)
        n)))

(define (random-bit) (modulo (random-num) 2))

(define (random-byte) (+ (modulo (random-num) 128) (* 128 (random-bit))))

(define (random bytes)
  (if (<= bytes 0)
      0
      (+ (* 256 (random (- bytes 1))) (random-byte))))

(define (random-range lo hi)
  (let ((byte-size (ceiling (/ (/ (log (- hi lo)) (log 2)) 8))))
    (+ lo (modulo (random byte-size) (- hi lo)))))


;; Primality tests.

; is-trivial-composite?: divisibility tests with the first few primes.
(define (is-trivial-composite? n)
  (or (= (modulo n 2) 0)
      (= (modulo n 3) 0)
      (= (modulo n 5) 0)
      (= (modulo n 7) 0)
      (= (modulo n 11) 0)
      (= (modulo n 13) 0)
      (= (modulo n 17) 0)
      (= (modulo n 19) 0)
      (= (modulo n 23) 0)))

; is-fermat-prime?:
; Check, for many values of a:
;  a^(n-1) = 1 [mod n] ?  
;   If yes, could be prime.  
;   If no, then composite.
; Warning: Some Carmichael numbers (though rare) defeat this test.
(define (is-fermat-prime? n iterations)
  (or (<= iterations 0)
      (let* ((a (random-range 2 n)))
        (and (= (modulo-power a (- n 1) n) 1)
             (is-fermat-prime? n (- iterations 1))))))


      
;; Prime generation.

; generate-fermat-prime(byte-size) yields a prime satisfying the Fermat test.
(define (generate-fermat-prime byte-size iterations)
  (let ((n (random byte-size)))
    (if
     (and (not (is-trivial-composite? n)) (is-fermat-prime? n iterations))
     n
     (generate-fermat-prime byte-size iterations))))



;; Example

(define iterations 4)
(define byte-size 50)

(display "Generating prime: ") 
(newline)
(display (generate-fermat-prime byte-size iterations)) 
(newline)
