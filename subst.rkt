#lang racket

;; ------------------------------------------------------------------
;; INTERFACE

(provide
 ;; (=alpha e_1 e_2) determines whether the two terms
 ;; belong to the same alpha-equivalence class
 =alpha
 
 ;; (subst-n (x_1 e_1) ... e) replaces all occurrences
 ;; of x_1, ... in e with e_1, ... HYGIENICALLY  
 subst-n)

;; ------------------------------------------------------------------
;; IMPLEMENTATION

(require redex)

(define-language Lam
  (e x (λ (x ...) e) (e e))
  (x variable-not-otherwise-mentioned))

;; ------------------------------------------------------------------
;; EQUIVALENCE CLASS

(define (=alpha t1 t2)
  
  (define-extended-language Lam-sd Lam
    (e .... d)
    (d natural))
  
  ;; (sd e0) converts e to de Bruin (static distance) form
  (define-metafunction Lam-sd 
    sd : any -> any
    [(sd any_0) (sd/a any_0 ())])
  
  ;; (sd/a e (x ...)) converts e to static distance form 
  ;; in the context (x ...), the variables on the path 
  ;; from e0 to e 
    (define-metafunction Lam-sd 
      sd/a : any (x ...) -> any
      [(sd/a x (x_c ...)) 
       (distance x (x_c ...) 0)]
      [(sd/a (λ (x) any) (x_c ...)) 
       (λ (dummy) (sd/a any (x x_c ...)))]
      [(sd/a (any_left any_right ...) (x_c ...))
       ((sd/a any_left (x_c ...)) (sd/a any_right (x_c ...)) ...)]
      [(sd/a any (x_c ...)) 
       any])
  
  ;; (distance x env) -- at which position does x occur in env
  (define-metafunction Lam-sd 
    distance : x (x ...) natural -> e
    [(distance x () d) x]
    [(distance x (x x_c ...) d) d]
    [(distance x (x_c x_d ...) d) 
     (distance x (x_d ...) ,(+ (term d) 1))])
  
  ;; -- IN -- 
  
  (define sd1 (term (sd ,t1)))
  (define sd2 (term (sd ,t2)))
  (equal? sd1 sd2))

(module+ test
  (test-equal (=alpha (term (λ (x) x)) (term (λ (y) y))) #t)
  (test-equal (=alpha (term (y (λ (x) x))) (term (y (λ (y) y)))) #t))

;; ------------------------------------------------------------------
;; SUBSTITUTION

(define-metafunction Lam
  subst-n : (x any) ... any -> any
  [(subst-n (x_1 any_1) (x_2 any_2) ... any_3)
   (subst x_1 any_1 (subst-n (x_2 any_2) ... any_3))]
  [(subst-n any_3) 
   any_3])

;; (subst x e_1 e) replaces all occurrences of 
;; x in e with e_1 HYGIENICALLY 
(define-metafunction Lam
  subst : x any any -> any 
  ;; 1. x_1 bound, so don't continue in Î» body
  [(subst x_1 any_1 (λ (x_2 ... x_1 x_3 ...) any_2))
   (λ (x_2 ... x_1 x_3 ...) any_2)]
  ;; 2. general purpose capture avoiding case
  [(subst x_1 any_1 (λ (x_2 ...) any_2))
   (λ (x ...) (subst x_1 any_1 (subst-vars* (x_2 x) ... any_2)))
   (where (x ...) ,(variables-not-in (term (x_1 any_1 any_2)) (term (x_2 ...))))]
  ;; 3. replace x_1 with e_1
  [(subst x_1 any_1 x_1) any_1]
  ;; 4. x_1 and x_2 are different, so don't replace
  [(subst x_1 any_1 x_2) x_2]
  ;; the last two cases cover all other expression forms
  [(subst x_1 any_1 (any_2 ...))
   ((subst x_1 any_1 any_2) ...)]
  [(subst x_1 any_1 any_2) any_2])

;; (subst-vars (x_1 e_1) ... e) replaces all occurrences of 
;; x_1, ... in e with e_1, ... UNCONDITIONALLY 
(define-metafunction Lam
  subst-vars* : (x any) ... any -> any 
  [(subst-vars* any) 
   any]
  [(subst-vars* (x_1 any_1) (x_2 any_2) ... any) 
   (subst-vars x_1 any_1 (subst-vars* (x_2 any_2) ... any))])

;; (subst-vars x e_1 e) replaces all occurrences of 
;; x in e with e_1 UNCONDITIONALLY 
(define-metafunction Lam
  subst-vars : x any any -> any 
  [(subst-vars x_1 any_1 x_1) any_1]
  [(subst-vars x_1 any_1 (any_2 ...)) ((subst-vars x_1 any_1 any_2) ...)]
  [(subst-vars x_1 any_1 any_2) any_2]
  [(subst-vars x_1 any_1 (x_2 any_2) ... any_3) 
   (subst-vars x_1 any_1 (subst-vars ((x_2 any_2) ... any_3)))])

;; ------------------------------------------------------------------
;; TESTS 

(module+ test
  (test-equal (term (subst x y x)) (term y))
  
  (test-equal (term (subst x y z)) (term z))
  
  (test-equal (term (subst x y (x (y z)))) 
              (term (y (y z)))
              #:equiv =alpha)
  
  (test-equal (term (subst x y ((λ (x) x) ((λ (y1) y1) (λ (x) z)))))
              (term ((λ (z) z) ((λ (y2) y2) (λ (x) z))))
              #:equiv =alpha)  ;; note: test fails without =alpha
  
  (test-equal (term (subst x y (if0 (+ 1 x) x x)))
              (term (if0 (+ 1 y) y y))
              #:equiv =alpha)
  
  (test-equal (term (subst x (λ (z) y) (λ (y) x)))
              (term (λ (y1) (λ (z) y)))
              #:equiv =alpha)
  
  (test-equal (term (subst x 1 (λ (y) x)))
              (term (λ (y) 1))
              #:equiv =alpha)
  
  (test-equal (term (subst x y (λ (y) x)))
              (term (λ (y2) y))
              #:equiv =alpha)

  (test-equal (term (subst x (λ (y) y) (λ (z) (z2 z))))
              (term (λ (z1) (z2 z1)))
              #:equiv =alpha)
  
  (test-equal (term (subst x (λ (z) z) (λ (z) (z1 z))))
              (term (λ (z2) (z1 z2)))
              #:equiv =alpha)
  
  (test-equal (term (subst x z (λ (z) (z1 z))))
              (term (λ (z2) (z1 z2)))
              #:equiv =alpha)
  
  (test-equal (term (subst x3 5 (λ (x2) x2)))
              (term (λ (x1) x1))
              #:equiv =alpha)
  
  (test-equal (term (subst z * (λ (z x) 1)))
              (term (λ (z x) 1))
              #:equiv =alpha)
  
  (test-equal (term (subst q (λ (x) z) (λ (z x) q)))
              (term (λ (z1 x1) (λ (x) z)))
              #:equiv =alpha)
  
  (test-equal (term (subst x 1 (λ (x x) x)))
              (term (λ (x x) x))
              #:equiv =alpha)
  
  (test-results))