
(let* ((void (lambda (z) z))
       
       (incomplete (lambda (not-done) not-done))
       
       (F (lambda (on-true on-false) (on-false)))
       (T (lambda (on-true on-false) (on-true)))

       (U (lambda (f) (f f)))
       
       (Y (lambda (X)
            ((lambda (procedure)
               (X (lambda (arg) ((procedure procedure) arg))))
             (lambda (procedure)
               (X (lambda (arg) ((procedure procedure) arg)))))))
       
       (ifth (lambda (cond th1 th2) (cond th1 th2)))
       
       (cons (lambda (car cdr) (lambda (on-nil on-cons) (on-cons car cdr))))
       (nil                    (lambda (on-nil on-cons) (on-nil)))
       
       (car (lambda (cell) (cell void (lambda (car cdr) car))))
       (cdr (lambda (cell) (cell void (lambda (car cdr) cdr))))

       (match-list (lambda (lst on-nil on-cons) (lst on-nil on-cons)))
       (match-2list (lambda (list1 list2 on-NN on-NC on-CN on-CC)
                      (match-list list1
                                  (lambda () (match-list list2 
                                                         (lambda () (on-NN))
                                                         (lambda (car2 cdr2) (on-NC car2 cdr2))))
                                  (lambda (car1 cdr1) (match-list list2
                                                                  (lambda () (on-CN car1 cdr1))
                                                                  (lambda (car2 cdr2) (on-CC car1 cdr1 car2 cdr2)))))))
       
    
       (list1 (lambda (e1) (cons e1 nil)))
       (list2 (lambda (e1 e2) (cons e1 (cons e2 nil))))
       (list3 (lambda (e1 e2 e3) (cons e1 (cons e2 (cons e3 nil)))))

       (map (U (lambda (map) (lambda (f lst) (match-list lst 
                                                         (lambda () nil)
                                                         (lambda (hd tl) (cons (f hd) ((U map) f tl))))))))
       
       (b0 (lambda (on-0 on-1) (on-0)))
       (b1 (lambda (on-0 on-1) (on-1)))
       (match-bit (lambda (bit on-0 on-1) (bit on-0 on-1)))
       (match-2bit (lambda (bit1 bit2 on-00 on-01 on-10 on-11)
                     (match-bit bit1
                                (lambda () (match-bit bit2 
                                                      (lambda () (on-00))
                                                      (lambda () (on-01))))
                                (lambda () (match-bit bit2
                                                      (lambda () (on-10))
                                                      (lambda () (on-11)))))))
       (match-3bit (lambda (bit1 bit2 bit3 on-000 on-001 on-010 on-011 on-100 on-101 on-110 on-111)
                     (match-bit bit1
                                (lambda () (match-2bit bit2 bit3
                                                      (lambda () (on-000))
                                                      (lambda () (on-001))
                                                      (lambda () (on-010))
                                                      (lambda () (on-011))))
                                (lambda () (match-2bit bit2 bit3
                                                      (lambda () (on-100))
                                                      (lambda () (on-101))
                                                      (lambda () (on-110))
                                                      (lambda () (on-111)))))))
       
       
       (bnot (lambda (bit) 
               (bit (lambda () b1) 
                    (lambda () b0))))
       
       (bor (lambda (bit1 bit2)
              (match-2bit bit1 bit2
                          (lambda () b0)
                          (lambda () b1)
                          (lambda () b1)
                          (lambda () b1))))

       (bxor (lambda (bit1 bit2)
               (match-2bit bit1 bit2
                           (lambda () b0)
                           (lambda () b1)
                           (lambda () b1)
                           (lambda () b0))))
             
       (nat0 (list1 b0))
       (nat1 (list1 b1))
       
       (sum-with-carry (U (lambda (F) (lambda (n1 n2 carry) incomplete))))
                                           
       
       ;; tests
       (tlist1 (cons 1 F))
       
       )
  (car (map (lambda (x) (+ x 1)) (cons 1 nil))))