(let ((v1 (lambda (x) x)))
  (let ((v2 (lambda (y) y)))
    (((v1 v2) v1) v2)))