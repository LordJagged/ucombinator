(define (countdown n)
  (if
   (> n 0)
   (countdown (- n 1)) 1))

(define count 500000)

(and
    (countdown count) 
    (countdown count))
