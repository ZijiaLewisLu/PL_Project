#lang racket 

(require redex "tut-subst.rkt")

;; Ruling out run-time errors by type checking

;; SYNTAX 
(define-language Lam
  (e ::= ;; expressions 
     x
     (λ (x t) e) 
     (e e)
     n
     (+ e e))
  (t ::= ;; types
     int
     (t -> t))
  (n integer)
  (x ::= ;; variables
     variable-not-otherwise-mentioned))

(define ex1 (term ((λ (x (int -> int)) x) (λ (w int) w))))
(define re1 (term (λ (w int) w)))

(define ex2 (term ((λ (x (int -> int)) (λ (y int) x)) (λ (w int) w))))
(define re2 (term (λ (y int) (λ (w int) w))))

(define ex3 (term ((λ (x (int -> (int -> int))) x) 
                   (λ (y int) (λ (z int) z)))))
(define re3 (term (λ (y int) (λ (z int) z))))

(define ex10 (term (+ 3 10)))
(define re10 (term 13))

(define ex11 (term (((λ (x int) (λ (y int) (+ x y))) 40) 2)))
(define re11 (term 42))

;; ------------------------------------------------------------------
;; SEMANTICS

(define-extended-language Lam-red Lam  ;; call by value
  (v ::= ;; values 
     n
     (λ (x t) e))
  (E ::= ;; evaluation contexts 
     hole 
     (E e)
     (v E)  
     (+ E e)
     (+ v E)))

(define-metafunction Lam-red
  subst : x e e -> e
  [(subst x e_1 e)
   ,(subst/proc (redex-match Lam-red x)
                (term (x))
                (term (e_1))
                (term e))])

(define ->v
  (reduction-relation 
   Lam-red
   #:domain e 
   (--> (in-hole E ((λ (x t) e_b) v)) 
        (in-hole E (subst x v e_b))
        beta)
   (--> (in-hole E (+ n_1 n_2))
        (in-hole E ,(+ (term n_1) (term n_2))))))

(define-extended-language Lam-typ Lam
  (G ::= ((x t) ...)))

(define-judgment-form Lam-typ
  #:contract (typed G e t)
  #:mode (typed I I O)
  [ ;; x : t \in G
   ------------------------------------------------ tvar
   (typed ((x_1 t_1) ... (x t) (x_2 t_2) ...) x t)]
  [(typed ((x t) (x_1 t_1) ...) e t_r)
   ----------------------------------------------- tlam
   (typed ((x_1 t_1) ...) (λ (x t) e) (t -> t_r))]
  [(typed G e_fun (t_arg -> t_res))
   (typed G e_arg t_arg)
   ---------------------------------- tapp
   (typed G (e_fun e_arg) t_res)]
  [
   ---------------- tnum
   (typed G n int)]
  [(typed G e_1 int)
   (typed G e_2 int)
   --------------------------- tadd
   (typed G (+ e_1 e_2) int)])

;; ----------------------------------------------------------
;; (evaluate e) determines the value of e using CBN reduction

(module+ test
  (test-equal (term (evaluate ,ex1)) re1)
  (test-equal (term (evaluate ,ex2)) re2)
  (test-equal (term (evaluate ,ex3)) re3)
  (test-equal (term (evaluate ,ex10)) re10)
  (test-equal (term (evaluate ,ex11)) re11))

(define-metafunction Lam-red
  evaluate : e -> v or "type error!"
  [(evaluate e) 
   ,(first (apply-reduction-relation* ->v (term e)))
   (side-condition (judgment-holds (typed () e t)))]
  [(evaluate e)
   "type error!"])


;; -------------------------------------------------------------------
;; PROBLEMS 


(define bad (term (w (λ (x int) x))))
(test-equal (term (evaluate ,bad)) "type error!")
(define bad1 (term (4 (λ (x int) x))))
(test-equal (term (evaluate ,bad1)) "type error!")


(define ex4 (term ((λ (x (int -> int)) ((λ (y int) (x y)) 4)) (λ (z int) z))))
(define (test4) (term (evaluate ,ex4)))
(define (trace4) (traces ->v ex4))
; (show ex4)

(define ex5 (term ((λ (x ((int -> int) -> int)) 
                     ((λ (y (int -> int)) (x y)) (λ (z int) z))) 42)))
(define (test5) (term (evaluate ,ex5)))
; (show ex5)

;; ----------------------------

(define (show ex)
  (traces ->v ex
          #:pred
          (lambda (e)
            (if (judgment-holds (typed () ,e t))
                "limegreen"
                "pink"))))

