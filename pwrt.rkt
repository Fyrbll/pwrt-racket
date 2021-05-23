#lang typed/racket #:with-refinements

(require typed/racket/unsafe)

(unsafe-require/typed/provide
 typed/racket/base
 [make-vector (All (A) (-> ([n : Natural]
                            [val : A])
                           (Refine [v : (Vectorof A)]
                             (= n (vector-length v)))))])

(define-type Int Integer)

(define-type Zero (Refine (v : Int) (= v 0)))

(define zero : Zero 0)

(define-type Nat (Refine (v : Int) (<= 0 v)))

(define nats : (Listof Nat) (list 0 1 2 3))

#|
(define-type Pos (Refine (v : Int) (<= 0 v)))

(define poss : (Listof Pos) (list 0 1 2 3))
|#

(define-type Pos (Refine (v : Int) (< 0 v)))

(define poss : (Listof Pos) (list 1 2 3))

(define zero\' : Nat zero)

(define four : Nat (let ((x 3)) (+ x 1)))

(: impossible (All (a) (-> (Refine (v : Any) Bot) a)))
(define (impossible msg) (error msg))

#|
(: safeDiv (-> Int Int Int))
(define (safeDiv x n)
  (match n
    (0 (impossible "divide-by-zero"))
    (_ (quotient x n))))
|#

(: safeDiv (-> Int (Refine (z : Int) (not (= z 0))) Int))
(define (safeDiv x n)
  (match n
    (0 (impossible "divide-by-zero"))
    (_ (quotient x n))))

(: readLn (-> Int))
(define (readLn)
  (let ((__n (read-line)))
    (if (string? __n)
        (let ((_n (string->number __n)))
          (if _n
              (exact-truncate (real-part _n))
              (error "input can't be parsed as a number!")))
        (error "input is empty!"))))

#|
(: calc (-> Void))
(define (calc)
  (displayln "Enter numerator")
  (define n (readLn))
  (displayln "Enter denominator")
  (define d (readLn))
  (printf "Result = ~v~n" (safeDiv n d)))
|#

(: calc (-> Void))
(define (calc)
  (displayln "Enter numerator")
  (define n (readLn))
  (displayln "Enter denominator")
  (define d (readLn))
  (if (= d 0)
      (error "denominator is zero!")
      (printf "Result = ~v~n" (safeDiv n d))))

#|
(: avg (-> (Listof Int) Int))
(define (avg xs)
  (let ((total (apply + xs))
        (n     (length xs)))
    ((safeDiv total) n)))
|#

(: size (All (a) (-> (Listof a) Pos)))
(define (size lst)
  (match lst
    (`()         1)
    (`(,x . ,xs) (let ((n (size xs))) (+ 1 n)))))

(: avg\' (-> (Listof Int) Int))
(define (avg\' xs)
  (let ((total (apply + xs))
        (n     (size xs)))
    (safeDiv total n)))

#|
(: size\' (All (a) (-> (Listof a) Pos)))
(define (size\' l)
  (match l
    (`(,x)                      1)
    (`(_ . ,xs) (+ 1 (size\' xs)))
    (_          (impossible "size"))))
|#

(define-type (List a) (Vectorof a))

(: Emp (All (a) (-> (Refine (l : (List a)) (= (vector-length l) 0)))))
(define (Emp) (vector))

(: ::: (All (a) (-> ((x : a) (xs : (List a)))
                    (Refine (l : (List a))
                            (= (vector-length l) (+ 1 (vector-length xs)))))))
(define (::: x xs) 
  (let ((v (make-vector (+ 1 (vector-length xs)) x)))
    (vector-copy! v 1 xs)
    v))

(define-type (List-2 a) (Pairof Natural (_List a)))
(define-type (_List a) (U _Emp (_::: a)))
(struct _Emp ())
(struct (a) _::: ((head : a) (tail : (_List a))))

(: Emp-2 (All (a) (-> (Refine (l : (List-2 a)) 
                              (and (= (car l) 0) (: (cdr l) _Emp))))))
(define (Emp-2) 
  (ann (cons   0 (_Emp))
       (Pairof 0 _Emp)))

(: :::-2
   (All (a) (-> ((x : a) (xs : (List-2 a)))
                (Refine (l : (List-2 a)) (and (= (car l) (+ (car xs) 1))
                                              (: (cdr l) (_::: a)))))))
(define (:::-2 x xs)
  (ann (cons   (+ (car xs) 1)                              (_::: x (cdr xs)))
       (Pairof (Refine (z : Natural) (= z (+ (car xs) 1)))        (_::: a))))

(: head (All (a) (-> (Refine (l : (List a)) (> (vector-length l) 0)) a)))
(define (head l) (vector-ref l 0))

(: tail (All (a) (-> ((l : (Refine (xs : (List a)) (> (vector-length xs) 0))))
  (Refine (xs : (List a)) (= (vector-length xs) (- (vector-length l) 1))))))
(define (tail l)
  (let ((v (make-vector (- (vector-length l) 1) (head l))))
    (vector-copy! v 0 l 1 (vector-length l))
    v))

(: head-2 (All (a) (-> (Refine (l : (List-2 a)) (: (cdr l) (_::: a))) a)))
(define (head-2 l) (when (_:::? (cdr l)) (_:::-head (cdr l))))

(: tail-2 (All (a) (-> ((l : (Refine 
                              (xs : (List-2 a))
                              (and (> (car xs) 0) (: (cdr xs) (_::: a))))))
                       (Refine (xs : (List-2 a)) (= (car xs) (- (car l) 1))))))
(define (tail-2 l)
  (define _tail : (_List a) (when (_:::? (cdr l)) (_:::-tail (cdr l))))
  (ann (cons   (- (car l) 1)                                 _tail)
       (Pairof (Refine (n : Natural) (= n (- (car l) 1))) (_List a))))

(: ~head-2 (All (a) (-> (Refine (l : (List-2 a)) (> (car l) 0)) a)))
(define (~head-2 l)
  (match (cdr l)
    ((_Emp)     (error "list is empty"))
    ((_::: h _)                     h)))

(: ~tail-2 (All (a) (-> ((l : (Refine (xs : (List-2 a)) (> (car xs) 0))))
                        (Refine (xs : (List-2 a)) (= (car xs) (- (car l) 1))))))
(define (~tail-2 l) 
  (match (cdr l)
    ((_Emp)      (error "list is empty"))
    ((_::: _ xs) 
     (ann (cons   (- (car l) 1)                              xs)
          (Pairof (Refine (n : Natural) (= n (- (car l) 1))) (_List a))))))

(define-type (ListNE a) (Refine (l : (List a)) (> (vector-length l) 0)))

(: foldr (All (a b) (-> (-> a b b) b (List a) b)))
(define (foldr f acc l) 
  (if (= (vector-length l) 0)
      acc
      (f (head l) (foldr f acc (tail l)))))

(: foldr1 (All (a) (-> (-> a a a) (ListNE a) a)))
(define (foldr1 f l) (foldr f (head l) (tail l)))

#|
(: average\' (-> (List Int) Int))
(define (average\' l)
  (let ((total (foldr1 + l))
        (n (vector-length l)))
      (safeDiv total n)))
|#

(: average\' (-> (ListNE Int) Int))
(define (average\' l)
  (let ((total (foldr1 + l))
        (n (vector-length l)))
      (safeDiv total n)))

#|
(define-type (Year a) (List a))
|#

(define-type (Year a) (Refine (l : (List a)) (= (vector-length l) 12)))

(define-type (ListN a n) (Refine (l : (List a)) (: (vector-length l) n)))

#|
(define badYear : (Year Int) (::: 1 (ann (Emp) (|List 0| Int))))
|#

(define-type (|List 0| a) (Refine (l : (List a)) (= (vector-length l) 0)))
(define goodYear : (Year String)
  (::: "jan" (::: "feb" (::: "mar" (::: "apr"  
  (::: "may" (::: "jun" (::: "jul" (::: "aug"
  (::: "sep" (::: "oct" (::: "nov" (::: "dec"
  (ann (Emp) (|List 0| String)))))))))))))))

#|
(: map (All (a b) (-> (-> a b) (List a) (List b))))
(define (map f l) 
  (if (= (vector-length l) 0)
      (Emp)
      (::: (f (head l)) (map f (tail l)))))
|#

(: map (All (a b) (-> ((f  : (-> a b)) 
                       (l : (List a)))
                      (Refine (xs : (List b)) (= (vector-length l) 
                                                 (vector-length xs))))))
(define (map f l)
  (if (= (vector-length l) 0)
      (Emp)
      (::: (f (head l)) (map f (tail l)))))

(struct Weather ((temp : Int) (rain : Int)))

(: tempAverage (-> (Year Weather) Int))
(define (tempAverage y)
  (let ((months (map Weather-temp y)))
    (average\' months)))

#|
(: init (All (a) (-> (-> Int a) Nat (List a))))
(define (init f n)
  (if (<= n 0)
      (Emp)
      (::: (f n) (init f (- n 1)))))
|#

(: init (All (a) (-> ((f : (-> Int a)) (n : Nat))
                     (Refine (l : (List a)) (= (vector-length l) n)))))
(define (init f n) (if (= 0 n) (Emp) (::: (f n) (init f (- n 1)))))

(define sanDiegoTemp : (Year Int) (init (const 72) 12))

#| CHAPTER 4 |#

#|
(: sort (-> (List Int) (List Int)))
(define (sort l)
  (if (= (vector-length l) 0)
      (Emp)
      (insert (head l) (sort (tail l)))))

(: insert (-> Int (List Int) (List Int)))
(define (insert x l)
  (if (= (vector-length l) 0)
      (::: x l)
      (let ((y  (head l))
            (ys (tail l)))
        (if (<= x y)
            (::: x (::: y ys))
            (::: y (insert x ys))))))
|#

(: sort 
  (-> ((l : (List Int)))
    (Refine (m : (List Int)) (= (vector-length m) (vector-length l)))))
(define (sort l)
  (if (= (vector-length l) 0)
      (Emp)
      (insert (head l) (sort (tail l)))))

(: insert (-> ((x : Int) (l : (List Int)))
              (Refine (m : (List Int)) (= (vector-length m)
                                          (+ (vector-length l) 1)))))
(define (insert x l)
  (if (= (vector-length l) 0)
      (::: x l)
      (let ((y  (head l))
            (ys (tail l)))
        (if (<= x y)
            (::: x (::: y ys))
            (::: y (insert x ys))))))

#|
(define-type OrdPair (Pairof Int Int))
|#

(define-type OrdPair (Refine (p : (Pairof Int Int)) (< (car p) (cdr p))))

(define okPair : OrdPair '(2 . 4))

#|
(define badPair : OrdPair '(4 . 2))
|#

(define-type Csv (Pairof (List String) (List (List Int))))

#|
(define scores : Csv
  (let ()
    (define EmpS : (-> (List String))     Emp)
    (define EmpI : (-> (List Int))        Emp)
    (define EmpL : (-> (List (List Int))) Emp)
    (cons (::: "Id" (::: "Midterm" (::: "Final" (EmpS))))
     (::: (::: 1    (::: 25        (::: 88      (EmpI))))
     (::: (::: 2    (::: 27        (::: 83      (EmpI)))) 
     (::: (::: 3    (::: 19        (::: 93      (EmpI)))) 
     (EmpL)))))))
|#

(: Csv-mk (-> ((hdrs : (List String))
               (vals : (hdrs) (List (Refine (row : (List Int)) 
                                            (= (vector-length row)
                                               (vector-length hdrs))))))
              Csv))
(define (Csv-mk hdrs vals)
  (cons hdrs (map (lambda ((x : (List Int))) x) vals)))

(define-type (|List 3| a) (Refine (l : (List a)) (= (vector-length l) 3)))
(define scores : Csv
  (let ()
    (define EmpS : (-> (|List 0| String))         Emp)
    (define EmpI : (-> (|List 0| Int))            Emp)
    (Csv-mk (::: "Id" (::: "Midterm" (::: "Final" (EmpS))))
     (::: (ann (::: 1 (::: 25 (::: 88 (EmpI)))) (|List 3| Int))
     (::: (ann (::: 2 (::: 27 (::: 83 (EmpI)))) (|List 3| Int))
     (::: (ann (::: 3 (::: 19 (::: 93 (EmpI)))) (|List 3| Int))
     (ann (Emp) (|List 0| (|List 3| Int)))))))))

#|
(define-type (|List 2| a) (Refine (l : (List a)) (= (vector-length l) 2)))
(define scores\' : Csv
  (let ()
    (define EmpS : (-> (|List 0| String))         Emp)
    (define EmpI : (-> (|List 0| Int))            Emp)
    (Csv-mk (::: "Id" (::: "Midterm" (::: "Final" (EmpS))))
     (::: (ann (::: 1 (::: 25 (::: 88 (EmpI)))) (|List 3| Int))
     (::: (ann (::: 2         (::: 83 (EmpI)))  (|List 2| Int))
     (::: (ann (::: 3 (::: 19 (::: 93 (EmpI)))) (|List 3| Int))
     (ann (Emp) (|List 0| (|List 3| Int)))))))))
|#

(define-type (OList a) (Listof a))
(define OEmp null)
#|
(define :<: cons)
|#

(: :<: (-> ((oHd : Int) (oTl : (oHd) (OList (Refine (z : Int) (>= z oHd)))))
           (OList (Refine (z : Int) (>= z oHd)))))
(define (:<: oHd oTl) (cons (ann oHd (Refine (z : Int) (>= z oHd))) oTl))

(: oHd (All (a) (-> (OList a) a)))
(define (oHd l) (car l))

(: oTl (All (a) (-> (OList a) (OList a))))
(define (oTl l) (cdr l))

(define okList (:<: 1 (:<: 2 (:<: 3 null))))

(define okListTail : (OList (Refine (z : Int) (>= z 1))) (oTl okList))

#|
(define badList (:<: 1 (:<: 3 (:<: 2 null))))
|#
