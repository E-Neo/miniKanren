#lang typed/racket

(struct Var ([c : Natural]) #:transparent)
(define var=? : (-> Var Var Boolean)
  (lambda (x1 x2)
    (= (Var-c x1) (Var-c x2))))

(define-type Term (U Var Symbol Number Null (Pair Term Term)))
(define-type Association (Pair Var Term))
(define-type Substitution (Listof Association))

(define walk : (-> Term Substitution Term)
  (lambda (u s)
    (let ([pr (and (Var? u) (assf (lambda ([v : Var]) (var=? u v)) s))])
      (if pr (walk (cdr pr) s) u))))

(define ext-s : (-> Var Term Substitution Substitution)
  (lambda (x v s)
    `((,x . ,v) . ,s)))

(define-type (Suspensionof a) (-> a))
(define-type (Streamof a)
  (U Null
     (Pair a (Streamof a))
     (Suspensionof (Streamof a))))

(define-type State (Pair Substitution Natural))
(define-type Stream (Streamof State))
(define-type Goal (-> State Stream))

(define == : (-> Term Term Goal)
  (lambda (u v)
    (lambda (s/c)
      (let ([s (unify u v (car s/c))])
        (if s (unit `(,s . ,(cdr s/c))) mzero)))))

(define unit : (-> State Stream)
  (lambda (s/c) (cons s/c mzero)))

(define mzero '())

(define unify : (-> Term Term Substitution (U Substitution False))
  (lambda (u v s)
    (let ([u (walk u s)] [v (walk v s)])
      (cond
        [(and (Var? u) (Var? v) (var=? u v)) s]
        [(Var? u) (ext-s u v s)]
        [(Var? v) (ext-s v u s)]
        [(and (pair? u) (pair? v))
         (let ([s (unify (car u) (car v) s)])
           (and s (unify (cdr u) (cdr v) s)))]
        [else (and (eqv? u v) s)]))))

(define call/fresh : (-> (-> Var Goal) Goal)
  (lambda (f)
    (lambda (s/c)
      (let ([c (cdr s/c)])
        ((f (Var c)) `(,(car s/c) . ,(+ c 1)))))))

(define disj : (-> Goal Goal Goal)
  (lambda (g1 g2)
    (lambda (s/c)
      (mplus (g1 s/c) (g2 s/c)))))

(define conj : (-> Goal Goal Goal)
  (lambda (g1 g2)
    (lambda (s/c)
      (bind (g1 s/c) g2))))

(define mplus : (-> Stream Stream Stream)
  (lambda (s1 s2)
    (cond
      [(null? s1) s2]
      [(procedure? s1) (lambda () (mplus s2 (s1)))]
      [else (cons (car s1) (mplus (cdr s1) s2))])))

(define bind : (-> Stream Goal Stream)
  (lambda (s g)
    (cond
      [(null? s) mzero]
      [(procedure? s) (lambda () (bind (s) g))]
      [else (mplus (g (car s)) (bind (cdr s) g))])))

(define-syntax Zzz
  (syntax-rules ()
    [(_ g) (lambda (s/c) (lambda () (g s/c)))]))

(define-syntax conj+
  (syntax-rules ()
    [(_ g) (Zzz g)]
    [(_ g0 g ...) (conj (Zzz g0) (conj+ g ...))]))

(define-syntax disj+
  (syntax-rules ()
    [(_ g) (Zzz g)]
    [(_ g0 g ...) (disj (Zzz g0) (disj+ g ...))]))

(define-syntax conde
  (syntax-rules ()
    [(_ (g0 g ...) ...) (disj+ (conj+ g0 g ...) ...)]))

(define-syntax fresh
  (syntax-rules ()
    [(_ () g0 g ...) (conj+ g0 g ...)]
    [(_ (x0 x ...) g0 g ...)
     (call/fresh (lambda (x0) (fresh (x ...) g0 g ...)))]))

(define pull : (-> Stream (U Null (Pair State Stream)))
  (lambda (s)
    (if (procedure? s)
        (pull (s))
        s)))

(define take-all : (-> Stream (Listof State))
  (lambda (s)
    (let ([s (pull s)])
      (if (null? s)
          '()
          (cons (car s)
                (take-all (cdr s)))))))

(define take : (-> Index Stream (Listof State))
  (lambda (n s)
    (if (zero? n)
        '()
        (let ([s (pull s)])
          (cond
            [(null? s) '()]
            [else (cons (car s)
                        (take (- n 1) (cdr s)))])))))

(define mk-reify : (-> (Listof State) (Listof Term))
  (lambda (s/c*)
    (map reify-state/1st-var s/c*)))

(define reify-state/1st-var : (-> State Term)
  (lambda (s/c)
    (let ([v (walk* (Var 0) (car s/c))])
      (walk* v (reify-s v '())))))

(define reify-s : (-> Term Substitution Substitution)
  (lambda (v s)
    (let ([v (walk v s)])
      (cond
        [(Var? v) (let ([n (reify-name (length s))])
                    (cons `(,v . ,n) s))]
        [(pair? v) (reify-s (cdr v) (reify-s (car v) s))]
        [else s]))))

(define reify-name : (-> Index Symbol)
  (lambda (n)
    (string->symbol (string-append "_" (number->string n)))))

(define walk* : (-> Term Substitution Term)
  (lambda (v s)
    (let ([v (walk v s)])
      (cond
        [(Var? v) v]
        [(pair? v) (cons (walk* (car v) s)
                         (walk* (cdr v) s))]
        [else v]))))

(define empty-state '(() . 0))
(define call/empty-state : (-> Goal Stream)
  (lambda (g)
    (g empty-state)))

(define-syntax run
  (syntax-rules ()
    [(_ n (x ...) g0 g ...)
     (mk-reify (take n (call/empty-state (fresh (x ...) g0 g ...))))]))

(define-syntax run*
  (syntax-rules ()
    [(_ (x ...) g0 g ...)
     (mk-reify (take-all (call/empty-state (fresh (x ...) g0 g ...))))]))

(define-syntax defrel
  (syntax-rules ()
    [(defrel (name x ...) g ...)
     (define (name [x : Term] ...) : Goal
       (lambda (s/c)
         (lambda ()
           ((conj+ g ...) s/c))))]))

(module+ test
  (require typed/rackunit)

  (defrel (appendo l s out)
    (conde
     ((== '() l) (== s out))
     ((fresh (a d res)
             (== `(,a . ,d) l)
             (== `(,a . ,res) out)
             (appendo d s res)))))

  (check-equal? (run* (x a b)
                      (== x `(,a ,b))
                      (appendo a b '(1 2 3 4 5)))
                '((() (1 2 3 4 5))
                  ((1) (2 3 4 5))
                  ((1 2) (3 4 5))
                  ((1 2 3) (4 5))
                  ((1 2 3 4) (5))
                  ((1 2 3 4 5) ())))

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
                '((s (s (s z))))))
