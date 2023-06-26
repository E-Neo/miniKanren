#lang typed/racket

(struct Var ([name : Symbol]) #:transparent)

(define-type Term (U Var Symbol Null (Pair Term Term)))
(define-type Association (Pair Var Term))
(define-type Substitution (Listof Association))

(define empty-s '())

(define walk : (-> Term Substitution (U Term False))
  (lambda (v s)
    (let ([a (and (Var? v) (assv v s))])
      (cond
        [(pair? a) (walk (cdr a) s)]
        [else v]))))

(define ext-s : (-> Var Term Substitution (U Substitution False))
  (lambda (x v s)
    (cond
      [(occurs? x v s) #f]
      [else (cons `(,x . ,v) s)])))

(define occurs? : (-> Var Term Substitution Boolean)
  (lambda (x v s)
    (let ([v (walk v s)])
      (cond
        [(Var? v) (eqv? v x)]
        [(pair? v) (or (occurs? x (car v) s)
                       (occurs? x (cdr v) s))]
        [else #f]))))

(define unify : (-> Term Term Substitution (U Substitution False))
  (lambda (u v s)
    (let ([u (walk u s)]
          [v (walk v s)])
      (cond
        [(eqv? u v) s]
        [(and (Var? u) v) (ext-s u v s)]
        [(and (Var? v) u) (ext-s v u s)]
        [(and (pair? u) (pair? v))
         (let ([s (unify (car u) (car v) s)])
           (and s (unify (cdr u) (cdr v) s)))]
        [else #f]))))

(define-type (Suspensionof a) (-> a))
(define-type (Streamof a)
  (U Null
     (Pair a (Streamof a))
     (Suspensionof (Streamof a))))

(define-type Stream (Streamof Substitution))
(define-type Goal (-> Substitution Stream))

(define == : (-> Term Term Goal)
  (lambda (u v)
    (lambda (s)
      (let ([s (unify u v s)])
        (if s `(,s) '())))))

(define succeed : Goal
  (lambda (s) `(,s)))
(define fail : Goal
  (lambda (s) '()))

(define disj2 : (-> Goal Goal Goal)
  (lambda (g1 g2)
    (lambda (s)
      (append-stream (g1 s) (g2 s)))))

(define append-stream : (All (a) (-> (Streamof a) (Streamof a) (Streamof a)))
  (lambda (s t)
    (cond
      [(null? s) t]
      [(pair? s) (cons (car s) (append-stream (cdr s) t))]
      [else (lambda () ;; swaps the arguments, and forces the suspension s
              (append-stream t (s)))])))

(define take-stream : (All (a) (-> (U Index False) (Streamof a) (Listof a)))
  (lambda (n s)
    (cond
      [(and n (zero? n)) '()]
      [(null? s) '()]
      [(pair? s) (cons (car s)
                       (take-stream (and n (- n 1)) (cdr s)))]
      [else (take-stream n (s))])))

(define conj2 : (-> Goal Goal Goal)
  (lambda (g1 g2)
    (lambda (s)
      (append-map-stream g2 (g1 s)))))

(define append-map-stream : (All (a b) (-> (-> a (Streamof b))
                                           (Streamof a)
                                           (Streamof b)))
  (lambda (g s)
    (cond
      [(null? s) '()]
      [(pair? s) (append-stream (g (car s))
                                (append-map-stream g (cdr s)))]
      [else (lambda () (append-map-stream g (s)))])))

(define call/fresh : (-> Symbol (-> Var Goal) Goal)
  (lambda (name f)
    (f (Var name))))

(define reify-name : (-> Index Symbol)
  (lambda (n)
    (string->symbol
     (string-append "_" (number->string n)))))

(define walk* : (-> Term Substitution (U Term False))
  (lambda (v s)
    (let ([v (walk v s)])
      (cond
        [(Var? v) v]
        [(pair? v)
         (cons (cast (walk* (car v) s) Term)
               (cast (walk* (cdr v) s) (Listof Term)))]
        [else v]))))

(define reify-s : (-> Term Substitution Substitution)
  (lambda (v r)
    (let ([v (walk v r)])
      (cond
        [(Var? v) (let ([n (length r)])
                    (let ([rn (reify-name n)])
                      (cons `(,v . ,rn) r)))]
        [(pair? v) (let ([r (reify-s (car v) r)])
                     (reify-s (cdr v) r))]
        [else r]))))

(define reify : (-> Term (-> Substitution (U Term False)))
  (lambda (v)
    (lambda (s)
      (let ([v (walk* v s)])
        (and v (let ([r (reify-s v empty-s)])
                 (walk* v r)))))))

(define run-goal : (-> (U Index False) Goal (Listof Substitution))
  (lambda (n g)
    (take-stream n (g empty-s))))

(define-syntax disj
  (syntax-rules ()
    [(disj) fail]
    [(disj g) g]
    [(disj g0 g ...) (disj2 g0 (disj g ...))]))

(define-syntax conj
  (syntax-rules ()
    [(conj) succeed]
    [(conj g) g]
    [(conj g0 g ...) (conj2 g0 (conj g ...))]))

(define-syntax defrel
  (syntax-rules ()
    [(defrel (name x ...) g ...)
     (define (name [x : Term] ...) : Goal
       (lambda (s)
         (lambda ()
           ((conj g ...) s))))]))

(define-syntax run
  (syntax-rules ()
    [(run n (x0 x ...) g ...)
     (run n q (fresh (x0 x ...)
                     (== `(,x0 ,x ...) q) g ...))]
    [(run n q g ...)
     (let ([q (Var 'q)])
       (map (reify q)
            (run-goal n (conj g ...))))]))

(define-syntax run*
  (syntax-rules ()
    [(run* q g ...) (run #f q g ...)]))

(define-syntax fresh
  (syntax-rules ()
    [(fresh () g ...) (conj g ...)]
    [(fresh (x0 x ...) g ...)
     (call/fresh 'x0
                 (lambda (x0)
                   (fresh (x ...) g ...)))]))

(define-syntax conde
  (syntax-rules ()
    [(conde (g ...) ...)
     (disj (conj g ...) ...)]))

(define ifte : (-> Goal Goal Goal Goal)
  (lambda (g1 g2 g3)
    (lambda (s)
      (let loop ([stm (g1 s)])
        (cond
          [(null? stm) (g3 s)]
          [(pair? stm) (append-map-stream g2 stm)]
          [else (lambda () (loop (stm)))])))))

(define once : (-> Goal Goal)
  (lambda (g)
    (lambda (s)
      (let loop ([stm (g s)])
        (cond
          [(null? stm) '()]
          [(pair? stm) (cons (car stm) '())]
          [else (lambda () (loop (stm)))])))))

(define-syntax conda
  (syntax-rules ()
    [(conda (g0 g ...)) (conj g0 g ...)]
    [(conda (g0 g ...) ln ...)
     (ifte g0 (conj g ...) (conda ln ...))]))

(define-syntax condu
  (syntax-rules ()
    [(condu (g0 g ...) ...)
     (conda ((once g0) g ...) ...)]))

(module+ test
  (require typed/rackunit)

  (define u (Var 'u))
  (define v (Var 'v))
  (define w (Var 'w))
  (define x (Var 'x))
  (define y (Var 'y))
  (define z (Var 'z))

  (check-equal? (occurs? x x '()) #t)
  (check-equal? (occurs? x `(,y) `((,y . ,x))) #t)
  (check-equal? (ext-s x `(,x) empty-s) #f)
  (check-equal? (ext-s x `(,y) `((,y . ,x))) #f)
  (check-equal? (let ([s `((,z . ,x) (,y . ,z))])
                  (let ([s (ext-s x 'e s)])
                    (and s (walk y s))))
                'e)

  (define nevero : (-> Goal)
    (lambda ()
      (lambda (s)
        (lambda ()
          ((nevero) s)))))

  (define alwayso : (-> Goal)
    (lambda ()
      (lambda (s)
        (lambda ()
          ((disj2 succeed (alwayso)) s)))))

  (check-equal? (walk w `((,x . b) (,z . ,y) (,w . (,x e ,z)))) `(,x e ,z))
  (check-equal? (walk* w `((,x . b) (,z . ,y) (,w . (,x e ,z)))) `(b e ,y))

  (check-equal? (map (reify x)
                     (take-stream 5
                                  ((disj2 (== 'olive x) (== 'oil x))
                                   empty-s)))
                '(olive oil))
  (check-equal? (map (reify x)
                     (run-goal 5
                               (disj2 (== 'olive x) (== 'oil x))))
                '(olive oil))

  (defrel (addo m n r)
    (conde
     [(== m 'z) (== r n)]
     [(fresh (m-)
             (== m `(s ,m-))
             (addo m- `(s ,n) r))]))

  (defrel (mulo m n r)
    (conde
     [(== m 'z) (== r 'z)]
     [(fresh (m- n+)
             (== m `(s ,m-))
             (addo n+ n r)
             (mulo m- n n+))]))

  (check-equal? (run 1 (x) (mulo '(s (s z)) x '(s (s (s (s (s (s z))))))))
                '(((s (s (s z)))))))
