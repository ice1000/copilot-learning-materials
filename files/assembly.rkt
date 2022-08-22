;; Problem 1
(define (ackermann m n)
  (cond
    [(= m 0) (+ n 1)]
    [(> m 0) (ackermann (- m 1)
     (cond
       [(= n 0) 1]
       [(> n 0) (ackermann m (- n 1))]))]))

#lang racket
;; Problem 2
(define (sum a b) (if (= a b) a (+ b (sum a (- b 1)))))

;; Problem 4
(define zero-to-20
  (list
   '(0 zero) '(1 one) '(2 two) '(3 three) '(4 four) '(5 five)
   '(6 six) '(7 seven) '(8 eight) '(9 nine) '(10 ten)
   '(11 eleven) '(12 twelve) '(13 thirteen) '(14 fourteen) '(15 fifteen)
   '(16 sixteen) '(17 seventeen) '(18 eighteen) '(19 nineteen)))
(define tens
  (list
   '(2 twenty) '(3 thirty) '(4 forty) '(5 fifty)
   '(6 sixty) '(7 seventy) '(8 eighty) '(9 ninety)))
(define (to-words n)
  (cond
    ((< n 0) 'error)
    ((< n 20) (cdr (assoc n zero-to-20)))
    ((< n 100) (append (cdr (assoc (quotient n 10) tens))
                       (let ([q (remainder n 10)]) (if (= 0 q) '() (to-words q)))))
    ((< n 200) (append (to-words (quotient n 100)) '(hundred and) (to-words (remainder n 100))))
    (else 'error)))

;; Problem 5
(define (initialWIList xs) (for/list ([i (in-naturals 0)] [x xs]) (list x i)))
(define (mergeWI x xs) (if (assoc (car x) xs) xs (append xs (list x))))
(define (mergeByWord xs) (reverse (foldr mergeWI '() xs)))
(define wordMaxIndex (compose mergeByWord initialWIList))

;; Problem 3
(define (h-f n) (if (= 0 n) 1 (- n (h-m (h-f (- n 1))))))
(define (h-m n) (if (= 0 n) 0 (- n (h-f (h-m (- n 1))))))

;; Problem 2
(define (minInt_helper k x)
  (cond ((null? x) k)
        ((> k (car x)) (minInt_helper (car x) (cdr x)))
        (else (minInt_helper k (cdr x)))))
(define (minInt x) (if (null? x) 0 (minInt_helper (car x) (cdr x))))

;; Problem 3
(define (manycall n f x)
  (if (<= n 1) x (manycall (- n 2) f (f (f x)))))

(define (bind k v al)
  (append (list (list k v)) al))
(define (lookup k al)
  (let [(look (assoc k al))]
    (if look (cadr look) look)))
(define al '())

;; Problem 1
(define (remove-when f x)
  (cond ((null? x) '())
        ((f (car x)) (remove-when f (cdr x)))
        (else (cons (car x) (remove-when f (cdr x))))))

;; Problem 2
(define (construct_mem f)
  (let ((al '()))
    (lambda (m n)
      (let* [(mn (list m n))
             (look (lookup mn al))]
        (if look
            (begin (display "memoization hit\n") look)
            (let [(feizhu (f m n))]
              (begin (set! al (bind mn feizhu al))
                     feizhu)))))))

(define (ackermann_mem m n)
  (let* [(mn (list m n))
         (look (lookup mn al))]
    (if look
        (begin (display "memoization hit\n") look)
        (let [(feizhu (ackermann m n))]
          (begin (set! al (bind mn feizhu al))
                 feizhu)))))

#lang racket

;; Problem 4
(define (reward amt)
  (cond
    [(<= amt 2000) (* 0.01 amt)]
    [(<= amt 4000) (+ 20 (* 0.015 (- amt 2000)))]
    [(<= amt 5500) (+ 20 30 (* 0.02 (- amt 4000)))]
    [else          (+ 20 30 30 (* 0.025 (- amt 5500)))]))