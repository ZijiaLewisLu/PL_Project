#lang racket 

(require redex "subst.rkt")

;; A PROBLEM WITH EVALUATION : ERRORS
;; Ruling out errors by checking that programs are closed 

;; SYNTAX 
(define-language Lam
  (e ::= ;; expressions 
     x
     (λ (x) e) 
     (e e)
     n
     (+ e e))
  (n integer)
  (x ::= ;; variables
     variable-not-otherwise-mentioned))

(define ex1 (term ((λ (x) x) (λ (w) w))))
(define re1 (term (λ (y) y)))

(define ex2 (term ((λ (x) (λ (y) x)) (λ (w) w))))
(define re2 (term (λ (y) (λ (w) w))))

(define ex3 (term ((λ (x) x) (λ (y) (λ (z) z)))))
(define re3 (term (λ (y) (λ (z) z))))

(define ex10 (term (+ 3 10)))
(define re10 (term 13))

(define ex11 (term (((λ (x) (λ (y) (+ x y))) 40) 2)))
(define re11 (term 42))

;; ------------------------------------------------------------------
;; SEMANTICS

(define-extended-language Lam-red Lam
  (v ::= ;; values 
     n
     (λ (x) e))
  (E ::= ;; evaluation contexts 
     hole 
     (E e)
     (+ E e)
     (+ v E)))

(define ->n
  (reduction-relation 
   Lam-red
   #:domain e 
   (--> (in-hole E ((λ (x) e_b) e)) 
        (in-hole E (subst-n (x e) e_b))
        beta)
   (--> (in-hole E (+ n_1 n_2))
        (in-hole E ,(+ (term n_1) (term n_2))))))

(define-extended-language Lam-typ Lam
  (G ::= (x ...)))
  
(define-metafunction Lam
  closed? : e -> boolean
  [(closed? e_0) (closed/a () e_0)])

;; ACCUM: G is the list of bindings encountered from e_0 to e
(define-metafunction Lam-typ
  closed/a : G e -> boolean
  [(closed/a (x_1 ... x x_r ...) x) #t]
  [(closed/a (x_1 ...) (λ (x) e))
   (closed/a (x x_1 ...) e)]
  [(closed/a G (e_1 e_2))
   ,(and (term (closed/a G e_1)) (term (closed/a G e_2)))]
  [(closed/a G e) #f])


(define-judgment-form Lam-typ
  #:contract (closed G e)
  #:mode (closed I I)
  [ ;; x is in G
   --------------------------------- var
   (closed (x_1 ... x x_r ...) x)]
  
  [(closed (x x_1 ...) e)
   ----------------------------- lam
   (closed (x_1 ...) (λ (x) e))]
   
  [(closed G e_1) 
   (closed G e_2)
   --------------------- app
   (closed G (e_1 e_2))]
  
  [;; ints are always closed
   -------------------------- num
   (closed G n)]
  
  [(closed G e_1)
   (closed G e_2)
   --------------------------- plus
   (closed G (+ e_1 e_2))])
   

;; (evaluate e) determines the value of e using CBN reduction

(module+ test
  (test-equal (term (evaluate ,ex1)) re1 #:equiv =alpha)
  (test-equal (term (evaluate ,ex2)) re2 #:equiv =alpha)
  (test-equal (term (evaluate ,ex3)) re3 #:equiv =alpha)
  (test-equal (term (evaluate ,ex10)) re10 #:equiv =alpha)
  (test-equal (term (evaluate ,ex11)) re11 #:equiv =alpha))

(define-metafunction Lam-red
  evaluate : e -> v or "type error!"
  [(evaluate e) 
   ,(first (apply-reduction-relation* ->n (term e)))
   (side-condition (judgment-holds (closed () e)))]
  [(evaluate e)
   "type error!"])


;; -------------------------------------------------------------------
;; PROBLEMS 

(define bad (term (w (λ (x) x))))
(define (testbad) (term (evaluate ,bad)))
(define bad1 (term (4 (λ (x) x))))
(define (testbad1) (term (evaluate ,bad1)))


(define ex4 (term ((λ (x) ((λ (y) (x y)) w)) (λ (z) z))))
(define (test4) (term (evaluate ,ex4)))
(define (trace4) (traces ->n ex4))
; (show ex4)

(define ex5 (term ((λ (x) ((λ (y) (x y)) (λ (z) z))) 42)))
(define (test5) (term (evaluate ,ex5)))
; (show ex5)

;; ----------------------------

(define (show ex)
  (traces ->n ex
          #:pred
          (lambda (e)
            (if (judgment-holds (closed () ,e))
                "limegreen"
                "pink"))))

