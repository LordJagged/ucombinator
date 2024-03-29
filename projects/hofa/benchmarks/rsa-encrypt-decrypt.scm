
; extended-gcd = (x,y), such that a*x + b*y = gcd(a,b)
(define (extended-gcd a b)
  (if (= (modulo a b) 0)
      (cons 0 1)
      (let* ((x:y (extended-gcd b (modulo a b)))
             (x (car x:y))
             (y (cdr x:y)))
        (cons y (- x (* y (quotient a b)))))))

; modulo-inverse(a,n) = b, such that a*b = 1 [mod n].
(define (modulo-inverse a n)
  (modulo (car (extended-gcd a n)) n))

; totient(n) = (p - 1)*(q - 1), where pq is the prime factorization of n.
(define (totient p q) (* (- p 1) (- q 1)))

; square(x) = x^2
(define (square x) (* x x))

; modulo-power(base,exp,n) = base^exp [mod n]
(define (modulo-power base exp n)
  (if (= exp 0)
      1
      (if (odd? exp)
          (modulo (* base (modulo-power base (- exp 1) n)) n)
          (modulo (square (modulo-power base (/ exp 2) n)) n))))


; A legal public exponent e is between 1 and totient(n), and gcd(e,totient(n)) = 1
(define (is-legal-public-exponent? e p q)
  (and (< 1 e) 
       (< e (totient p q))
       (= 1 (gcd e (totient p q)))))

; The private exponent is the inverse of the public exponent, mod n.
(define (private-exponent e p q) 
  (if (is-legal-public-exponent? e p q)
      (modulo-inverse e (totient p q))
      (error "Not a legal public exponent for that modulus.")))

; An encrypted message is c = m^e [mod n].
(define (encrypt m e n)
  (if (> m n)
      (error "The modulus is too small to encrypt the message.")
      (modulo-power m e n)))

; A decrypted message is m = c^d [mod n].
(define (decrypt c d n)
  (modulo-power c d n))


(define p 53) ; A "large" prime.
(define q 47) ; Another "large" prime.
(define n (* p q))  ; The public modulus.

(define e 5)        ; The public exponent.

(define d (private-exponent e p q))

(define message 42)              ; The plaintext.

(define c (encrypt message e n)) ; The ciphertext.

(display "The ciphertext is: ")
(display c)
(newline)

(define m (decrypt c d n))       ; The decrypted ciphertext.
(display "The decrypted ciphertext is: ")
(display m)
(newline)

(if (not (= m message))
    (error "RSA fail!"))