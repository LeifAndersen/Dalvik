#lang racket

(require racket/match)

; Input language
; program ::= class-def ...
;
; class-def ::= class class-name extends class-name
;               { field-def ... method-def ... }
;
; field-def ::= var field-name ;
;
; method-def ::= def method-name($name, ..., $name) { body }
;
; body ::= stmt ...
;
; stmt ::= label label:
;       |  skip ;
;       |  goto label ;
;       |  if aexp goto label ;
;       |  $name := aexp | cexp ;
;       |  return aexp ;
;       |  aexp.field-name := aexp ;
;       |  push-handler class-name label ;
;       |  pop-handler ;
;       |  throw aexp ;
;       |  move-exception $name ;
;
; cexp ::= new class-name
;       |  invoke aexp.method-name(aexp,...,aexp)
;       |  invoke super.method-name(aexp,...,aexp) ;
; aexp ::= this
;       |  true | false
;       |  null
;       |  void
;       |  $name
;       |  int
;       |  atomic-op(aexp, ..., aexp)
;       |  instanceof(aexp, class-name)
;       |  aexp.field-name
;

; Using the code from:
; http://matt.might.net/articles/parsing-with-derivatives/

(require srfi/41) ; Stream library
(require test-engine/racket-tests)

; Generic tools:
(define-syntax while
  (syntax-rules ()
    [(_ cond body ...)
     ; =>
     (letrec ((lp (lambda () (when cond body ... (lp)))))
       (lp))]))

(define-syntax define/fix
  (syntax-rules ()
    [(_ (f x) #:bottom bottom body ...)
     ; =>
     (define f (let ((cache     (make-weak-hasheq))
                     (changed?  (make-parameter 'error-changed))
                     (running?  (make-parameter #f))
                     (visited   (make-parameter 'error-visited)))
                 (lambda (x)
                   (let ((cached? (hash-has-key? cache x))
                         (cached  (hash-ref cache x (lambda () bottom)))
                         (run?    (running?)))
                     (cond
                       [(and cached? (not run?))
                        ; =>
                        cached]
                       
                       [(and run? (hash-has-key? (unbox (visited)) x))
                        ; =>
                        (if cached? cached bottom)]
                       
                       [run? 
                        ; =>
                        (hash-set! (unbox (visited)) x #t)
                        (let ((new-val (begin body ...)))
                          (when (not (equal? new-val cached))
                            (set-box! (changed?) #t)
                            (hash-set! cache x new-val))
                          new-val)]
                       
                       [(and (not cached?) (not run?))
                        ; =>
                        (parameterize ([changed? (box #t)]
                                       [running? #t]
                                       [visited (box (make-weak-hasheq))])
                          (let ([v bottom])
                            (while (unbox (changed?))
                                   (set-box! (changed?) #f)
                                   (set-box! (visited) (make-weak-hasheq))
                                   (set! v (f x)))
                            v))])))))]))

(define-syntax make-weak-hash-trie
  (syntax-rules ()
    [(_ #:eq eq ...)      (make-weak-hasheq)]
    [(_ #:eqv eq ...)     (make-weak-hasheqv)]
    [(_ #:equal eq ...)   (make-weak-hash)]))

(define-syntax weak-hash-trie-get!
  (syntax-rules ()
    [(_ t [eq] [x] lazy-val)
     ; =>
     (let ([$t t]
           [$x x])
       (if (hash-has-key? $t $x)
           (hash-ref $t $x)
           (let ([val lazy-val])
             (hash-set! $t $x val)
             val)))]
    
    [(_ t [eq1 eq2 eq3 ...] [x1 x2 x3 ...] lazy-val)
     ; =>
     (let ([$t t])
       (if (hash-has-key? $t x1)
           (let ([t2 (hash-ref t x1)])
             (weak-hash-trie-get! t2 [eq2 eq3 ...] [x2 x3 ...] lazy-val))
           (let ([t2 (make-weak-hash-trie eq2 eq3 ...)])
             (hash-set! $t x1 t2)
             (weak-hash-trie-get! t2 [eq2 eq3 ...] [x2 x3 ...] lazy-val))))]))
 
(define-syntax define/memoize 
  (syntax-rules ()
    [(_ (f [v eq] ...) body ...)
     ; =>
     (define/memoize (f v ...) #:order ([v eq] ...) body ...)]
    
    [(_ (f v ...) #:order ([v* eq] ...) body ...)
     ; =>
     (define f (let ((cache (make-weak-hash-trie eq ...))
                     ($f    (lambda (v ...) (let ([v* v] ...) body ...))))
                 (lambda (v ...)
                   (let ([v* v] ...)
                     (weak-hash-trie-get! cache [eq ...] [v ...] ($f v ...))))))]
    
    [(_ (f v ...) body ...)
     ; =>
     (define/memoize (f [v #:equal] ...) body ...)]))
    
; Languages:
(define-struct language ())

; Atomic languages:
(define-struct (empty language) ())           ; empty set
(define-struct (eps   language) ())           ; empty string
(define-struct (token language) (pred class)) ; terminal

; Compound languages:
(define-struct (compound-language language)      ())
(define-struct (union         compound-language) (this that))
(define-struct (concatenation compound-language) (left right))
(define-struct (reduction     compound-language) (lang reduce))

; Special symbols that can only appear during parsing:
(define-struct (eps*  eps)  (tree-set)) ; empty string that produces a tree

; Constructors:
(define-syntax cat
  (syntax-rules ()
    [(_)            (eps)]
    [(_ l1)         l1]
    [(_ l1 l2 ...)  (concatenation (delay l1) (delay (cat l2 ...)))]))

(define-syntax alt
  (syntax-rules ()
    [(_)            (empty)]
    [(_ l1)         l1]
    [(_ l1 l2 ...)  (union (delay l1) (delay (alt l2 ...)))]))

(define-syntax red
  (syntax-rules ()
    [(_ l f)        (reduction (delay l) f)]))

(define-syntax lang
  (syntax-rules (or quote seq --> empty reduction eps ?)
    [(_)                  (empty)]
    [(_ (eps))            (eps)]
    [(_ (empty))          (empty)]
    [(_ (? pred class))   (token pred class)]
    [(_ (quote lit))      (token (lambda (t) (equal? t 'lit)) 'lit)]
    
    [(_ (or))             (empty)]
    [(_ (or l1))          (lang l1)]
    [(_ (or l1 l2 ...))   (alt (lang l1) (lang (or l2 ...)))]
    
    [(_ (seq))            (eps)]
    [(_ (seq l1))         (lang l1)]
    [(_ (seq l1 l2 ...))  (cat (lang l1) (lang (seq l2 ...)))]
    
    [(_ (--> l f))        (red (lang l) f)]
                
    [(_ var)              var]))
    
; Pattern-matchers on languages:
(define-match-expander orp
  (syntax-rules ()
    [(_ l1 l2) (union (app force l1) (app force l2))]))

(define-match-expander seqp
  (syntax-rules ()
    [(_ l1 l2) (concatenation (app force l1) (app force l2))]))

(define-match-expander redp
  (syntax-rules ()
    [(_ l f) (reduction (app force l) f)]))

(define-match-expander nullablep?
  (syntax-rules ()
    [(_) (app nullable? #t)]))

; Parse a stream into a tree:    
(define (parse l s #:compact [compact (lambda (x) x)] #:steps [n #f] #:debug [debug? #f])
  (cond
    [(and n (= n 0)) l]
    [(stream-null? s) (parse-null l)]
    [else             
     ; =>
     (let* ([c      (stream-car s)]
            [rest   (stream-cdr s)]
            [dl/dc  (parse-derive c l)]
            [l*     (compact dl/dc)])
       (when debug?
         (display (format "size: ~s; mem: ~s~n" (language-size l*) (current-memory-use))))
       (parse l* rest
              #:compact compact
              #:steps   (and n (- n 1))
              #:debug   debug?))]))

(define (parse-null/input l input)
  (list->stream (set-map (parse-null l) (lambda (el) (cons el input)))))

; Nullability:
(define/fix (nullable? l)
  #:bottom #f
  (match l
    [(empty)           #f]
    [(eps)             #t]    
    [(token _ _)       #f]
    [(orp l1 l2)       (or (nullable? l1) (nullable? l2))]
    [(seqp l1 l2)      (and (nullable? l1) (nullable? l2))]
    [(redp l1 _)       (nullable? l1)]))

; Parse trees for nullability:
(define empty-tree-set (set))

(define/fix (parse-null l)
  #:bottom empty-tree-set
  (match l
    [(empty)        empty-tree-set]
    [(eps* S)       S]
    [(eps)          (set l)]
    [(token _ _)    empty-tree-set]
    [(orp l1 l2)    (set-union (parse-null l1) (parse-null l2))]
    [(seqp l1 l2)   (for*/set ([t1 (parse-null l1)]
                               [t2 (parse-null l2)])
                              (cons t1 t2))]
    [(redp l1 f)    (for/set ([t (parse-null l1)])
                             (f t))]))

; Derivative of a parser combinator:
(define/memoize (parse-derive c l)
  #:order ([l #:eq] [c #:equal])
  (match l
    [(empty)     (empty)]
    [(eps)       (empty)]
    [(token pred class)
     ; =>
     (if (pred c) (eps* (set c)) (empty))]
    
    [(orp l1 l2)
     ; =>
     (alt (parse-derive c l1) 
          (parse-derive c l2))]
    
    [(seqp (and (nullablep?) l1) l2)
     ; =>
     (alt (cat (eps* (parse-null l1)) (parse-derive c l2))
          (cat (parse-derive c l1) l2))]
    
    [(seqp l1 l2)
     ; =>
     (cat (parse-derive c l1) l2)]
    
    [(redp l f)
     ; =>
     (red (parse-derive c l) f)]))

; Derivative of a context-free language:
(define/memoize (derive c l)
  #:order ([l #:eq] [c #:equal])
  (match l
    [(empty)
     ; =>
     (empty)]
    
    [(eps)
     ; =>
     (empty)]
    
    [(token pred class)
     ; =>
     (if (pred c) (eps) (empty))]
    
    [(orp l1 l2)
     ; =>
     (alt (derive c l1) 
          (derive c l2))]
    
    [(seqp (and (nullablep?) l1) l2)
     ; =>
     (alt (derive c l2)
          (cat (derive c l1) l2))]
    
    [(seqp l1 l2)
     ; =>
     (cat (derive c l1) l2)]
    
    [(redp l f)
     ; =>
     (derive c l)]))

; Recognizes if a string is in a language:
(define (recognizes? l s)
  (cond
    [(stream-null? s) (nullable? l)]
    [else             (recognizes?
                       (derive (stream-car s) l)
                       (stream-cdr s))]))

; Partially parse a stream; return sub-parses:
(define (parse-partial l s) 
  (if (stream-null? s)
      (parse-null/input l stream-null)
      (match l 
        [(empty)      stream-null]
        [(eps)        (stream (cons (eps) s))]
        [(eps* S)     (parse-null/input l s)]
        [(token p c)
         ; =>
         (cond
           [(p (stream-car s)) (stream-cons (cons (stream-car s) (stream-cdr s))
                                            stream-null)]
           [else               stream-null])]
        [else
         ; =>
         (define c (stream-car s))
         (define rest (stream-cdr s))
         (stream-stitch (parse-partial (parse-derive c l) rest)
                        (parse-null/input l s))])))
                      
; Stream stitching:
(define (stream-stitch s1 s2 #:even [even? #t])
  (define (pull-s1) (stream-cons (stream-car s1) (stream-stitch (stream-cdr s1) s2 #:even (not even?))))
  (define (pull-s2) (stream-cons (stream-car s2) (stream-stitch s1 (stream-cdr s2) #:even (not even?))))
  (cond
    [(and even? (not (stream-null? s1))) (pull-s1)]
    [(and even? (not (stream-null? s2))) (pull-s2)]
    [even?                               stream-null]
    [(not (stream-null? s2))             (pull-s2)]
    [(not (stream-null? s1))             (pull-s1)]
    [else                                stream-null]))

; Checks whether a language is the empty string:
(define/fix (is-null? l)
  #:bottom #t
  (match l
    [(empty)           #f]
    [(eps)             #t]    
    [(token _ _)       #f]
    [(orp l1 l2)       (and (is-null? l1)  (is-null? l2))]
    [(seqp l1 l2)      (and (is-null? l1)  (is-null? l2))]
    [(redp l1 _)       (is-null? l1)]))

(define-match-expander nullp
  (syntax-rules ()
    [(_)    (app is-null? #t)]
    [(_ el) (and (app is-null? #t) (app parse-null (and (? singleton?) (app set-choose el))))]))

; Checks whether a language is the empty set:
(define/fix (is-empty? l)
  #:bottom #t
  (match l
    [(empty)           #t]
    [(eps)             #f]    
    [(token _ _)       #f]
    [(orp l1 l2)       (and (is-empty? l1)  (is-empty? l2))]
    [(seqp l1 l2)      (or  (is-empty? l1)  (is-empty? l2))]
    [(redp l1 _)       (is-empty? l1)]))

(define-match-expander emptyp
  (syntax-rules ()
    [(_) (app is-empty? #t)]))


(define (set-size s)
  (define size 0)
  (for ([_ s])
    (set! size (+ size 1)))
  size)

(define (singleton? s)
  (eqv? (set-size s) 1))

(define (set-choose s)
  (define el #f)
  (for ([el* s])
    (set! el el*))
  el)
  
; Performs algebraic reductions on a grammar:
(define/memoize (compact [l #:eq])
  (match l
    [(empty)       l]
    [(eps)         l]
    [(emptyp)      (empty)]
    [(nullp)       (eps* (parse-null l))]
    [(token p c)   l]

    [(orp (emptyp) l2)  (compact l2)]
    [(orp l1 (emptyp))  (compact l1)]
    
    [(seqp (nullp t) l2)  (red (compact l2) (lambda (w2) (cons t w2)))]
    [(seqp l1 (nullp t))  (red (compact l1) (lambda (w1) (cons w1 t)))]
    
    [(orp l1 l2)   (alt (compact l1) (compact l2))]
    [(seqp l1 l2)  (cat (compact l1) (compact l2))]
    
    [(redp (emptyp) _)  (empty)]
    
    [(redp (and e (nullp)) f) 
     ; =>
     (eps* (for/set ([t (parse-null e)]) (f t)))]
    
    [(redp (seqp (nullp t) l2) f)
     ; =>
     (red (compact l2) (lambda (w2) (f (cons t w2))))]
    
    [(redp (redp l f) g) 
     ; =>
     (red (compact l) (compose g f))]
        
    [(redp l f)    (red (compact l) f)]))
    

  



;;;; Debugging.

; Gives every object a unique value:
(define mark-of-beast 
  (let* ([index (make-hasheq)]
         [max   0]
         [next  (lambda ()
                  (set! max (+ max 1))
                  max)])
    (lambda (object)
      (if (hash-has-key? index object)
          (hash-ref index object)
          (begin
            (hash-set! index object (next))
            (mark-of-beast object))))))

; Allows recursive functions on graphs by
; turning them into graph searches:
(define-syntax define/search 
  (syntax-rules ()
    [(_ (f x rest ...) #:reentry default body ...)
     ; =>
     (define f (let ([visited (make-parameter #f)]
                     [$def    default])
                 (lambda (x rest ...)
                   (cond
                     [(not (visited))
                      ; =>
                      (parameterize ([visited (make-hasheq)])
                        (f x rest ...))]
                     
                     [(hash-has-key? (visited) x)
                      ; =>
                      (if (procedure? $def) ($def x) $def)]
                     
                     [else 
                      ; =>
                      (hash-set! (visited) x #t)
                      (let () body ...)]))))]
    
    [(_ (f x rest ...) body ...)
     ; =>
     (define/search (f x rest ...) #:reentry (lambda (x) (void)) body ...)]))

; Computes the size of a grammar.
(define/search (language-size l) 
  #:reentry 0
  (match l
    [(or (eps) (token _ _) (empty))   1]
    [(or (seqp l1 l2) (orp l1 l2))    (+ 1 (language-size l1)
                                           (language-size l2))]
    [(redp l f)                       (+ 1 (language-size l))]))
     
; Outputs a grammar as a dot file.
(define (dotify l #:port [port (current-output-port)])
  
  (define/search (dotify-nodes l port)
    (define m (mark-of-beast l))
    (match l
      [(empty) 
       ; =>
       (display (format "\"~s\" [label = \"empty\"~n];~n~n" m) port)]
      
      [(eps* S)
       ; =>
       (display (format "\"~s\" [shape = \"record\", label = \"eps* | ~v\"~n];~n~n" m S) port)]
      
      [(eps)
       ; =>
       (display (format "\"~s\" [label = \"eps\"~n];~n~n" m) port)]
      
      [(token _ c)
       ; =>
       (display (format "\"~s\" [shape = \"record\", label = \"token | ~s\"~n];~n~n" m c) port)]
      
      [(orp l1 l2)
       ; =>
       (define m1 (mark-of-beast l1))
       (define m2 (mark-of-beast l2))
       (display (format "\"~s\" [label = \"or\"~n];~n~n" m) port)
       (dotify-nodes l1 port)
       (dotify-nodes l2 port)
       (display (format "\"~s\" -> \"~s\" [~n];~n~n" m m1) port)
       (display (format "\"~s\" -> \"~s\" [~n];~n~n" m m2) port)]
      
      [(seqp l r)
       ; =>
       (define ml (mark-of-beast l))
       (define mr (mark-of-beast r))
       (display (format "\"~s\" [shape=\"none\", margin=0, label = <~n<table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\"><tr><td colspan=\"2\">seq</td></tr><tr><td port=\"L\">L</td><td port=\"R\">R</td></tr></table>>~n];~n~n" m) port)
       (dotify-nodes l port)
       (dotify-nodes r port)
       (display (format "\"~s\":L -> \"~s\" [~n];~n~n" m ml) port)
       (display (format "\"~s\":R -> \"~s\" [~n];~n~n" m mr) port)]
      
      [(redp l f)
       ; =>
       (define ml (mark-of-beast l))
       (display (format "\"~s\" [label = \"red\"~n];~n~n" m) port)
       (dotify-nodes l port)
       (display (format "\"~s\" -> \"~s\" [~n];~n~n" m ml) port)]))
  
  (define close-port? #f)
  
  (when (string? port)
    (set! close-port? #t)
    (set! port (open-output-file port #:mode 'text #:exists 'replace)))
  
  (display (format "digraph {~n~n") port)
  (display (format "node [];~n") port)
  (dotify-nodes l port)
  (display (format "\"~s\" [shape = \"doublecircle\"~n];~n" (mark-of-beast l)) port)
  (display (format "~n}") port)
  
  (when close-port?
    (close-output-port port)))
           

  

; Converts a grammar into a tree:
(define (language-to-tree l [seen (make-hasheq)])
  
  (define (seen?) (hash-has-key? seen l))
  
  (define (mark) (hash-set! seen l #t))
  
  (if (seen?)
      '-
      (begin 
        (mark)
        (match l
          [(empty)          '(empty)]
          [(eps* S)         `(eps* ,@(for/list ((s S)) s))]
          [(eps)            '(eps)]
          [(token _ class)   (list 'token class)]
          [(seqp l1 l2)     `(seq ,(language-to-tree l1 seen)
                                  ,(language-to-tree l2 seen))]
          [(orp l1 l2)      `(or  ,(language-to-tree l1 seen)
                                  ,(language-to-tree l2 seen))]
          [(redp l1 f)      `(red ,(language-to-tree l1 seen))]))))


(define (parse-program program)
  (parse program 'put-language-here)

; Parsed language
; program ::= class-def
;
; class-def ::= (class class-name class-name field-def method-def class-def)
;
; field-def ::= (var field-name field-def)
;
; method-def ::= (def method-name ($name, ..., $name) body method-def)
;
; body ::= (stmt body)
;
; stmt ::= (label label)
;       |  (skip)
;       |  (goto label)
;       |  (if aexp goto label)
;       |  (:= $name aexp | cexp)
;       |  (return aexp)
;       |  aexp.field-name := aexp ;
;       |  push-handler class-name label ;
;       |  pop-handler ;
;       |  throw aexp ;
;       |  move-exception $name ;
;
; cexp ::= new class-name
;       |  invoke aexp.method-name(aexp,...,aexp)
;       |  invoke super.method-name(aexp,...,aexp) ;
; aexp ::= this
;       |  true | false
;       |  null
;       |  void
;       |  $name
;       |  int
;       |  (atomic-op aexp ... aexp)
;       |  (instanceof aexp class-name)
;       |  aexp.field-name


(struct statement {stmt
                   next
                   class})

(struct state {statement
               frame-pointer
               store
               continuation
               statement-map})

(struct class {name
               extends
               field-def
               method-def
               next})

(struct method {name
                args
                body
                next})

(struct handle {class-name
                label
                kont})

; atom? exp -> boolean?
(define (atom? exp)
  (match exp
    [(? symbol?)        #t]
    [(? boolean?)       #t]
    [(? integer?)       #t]
    [(cons (? prim?) _) #t]
    [else               #f]))

; prim? symbol? -> boolean?
(define (prim? exp)
  (case exp
    [(+ - * void) #t]
    [else         #f]))

; prim->proc : symbol? -> procedure?
(define (prim->proc prim)
  (match prim
    ['+       +]
    ['-       -]
    ['*       *]
    ['void void]))

; eval-atom : aexp fp store -> value
(define (eval-atom atom fp σ)
  (match atom
    [(? symbol?)  (σ fp atom)]
    [(? boolean?) atom]
    [(? integer?) atom]
    [else atom]))

(define (generate-statement-map-helper program sm)
  (match program
    [`(class ,c)
     (generate-statement-map-helper (class-next c) (generate-statement-map-helper (class-method-def c) sm))]
    [`(def ,m)
     (generate-statement-map-helper (method-next m) (generate-statement-map-helper (method-body m) sm) sm)]
    [(cons `(label ,label) rest)
     (generate-statement-map-helper rest ((λ label*)
                                          (if (equal? label label*)
                                              program
                                              (sm label*))))]
    [(cons _ rest)
     (generate-statement-map-helper rest sm)]
    ['()
     sm]
    [else sm]))

(define (generate-statement-map program)
  (generate-statement-map-helper ((λ label) (error (format "unbound statement: ~a" label)))))

(define (find-method-helper m* m)
  (let ([name (method-name m*)])
    (if (equal? name m)
        m*
        (let ([next (method-next m*)])
          (if (equal? next null)
              null
              (find-method-helper next m))))))

(define (find-method c m)
  (let ([m* (find-method-helper (class-method-def c) m)])
    (if (equal? m* null)
        (let ([e (class-extends c)])
          (if (equal? e null)
              (error (format "unbound method: ~a" m))))
        m*)))

(define (apply-method-helper m name val v e fp σ κ sm)
  (if (equal? e '())
      (state (method-body m) fp σ κ)
      (let ([s (apply-method-helper m name val (cdr v) (cdr e) fp κ)])
        (state (state-statement s)
               (state-frame-pointer s)
               (λ (fp* arg)
                  (if (equal? `(,fp ,(car v) `(,fp* ,arg)))
                      (eval-atom (car e) fp σ)
                      (σ fp* arg)))
               (state-continuation s)
               (state-statement-map s)))))

(define (apply-method m name val e s fp σ κ sm)
  (if (equal? e '())
      (state (method-body m)
             (gensym 'fp)
             (λ (fp* arg)
                (if (equal? `(,fp $this) `(,fp* ,arg))
                    val
                    (σ fp* arg)))
             (`(assign ,name ,s ,fp ,κ))
             sm)
      (let ([st (apply-method-helper m name val (method-args m) e (gensym 'fp) κ)])
        (state (state-statement st)
               (state-frame-pointer st)
               (λ (fp* arg)
                  (if (equal? `(,fp $this) `(,fp* ,arg))
                      val
                      (σ fp* arg)))
               (`(assign ,name ,s ,fp ,(state-continuation st)))
               (state-statement-map st)))))

(define (apply-kont κ val σ sm)
  (match κ
    [`(assign ,name ,s ,fp ,κ)
     ; =>
     (state s fp (λ (fp* name*)
                    (if (equal? `(,fp ,name) `(,fp* ,name*))
                        val
                        (σ fp* name*)))
                    κ)]
    [`(handle ,class-name ,label ,κ sm)
     ; =>
     (apply-kont κ val σ)]
    ['halt
     ; =>
     (state '() fp σ 'halt sm)]))

(define (subclass? c c*)
  (if (equal? c c*)
      #t
      (let ([c** (class-extends c)])
        (if (equal? c** null)
          #f
          (subclass c** c*)))))

(define (handle-func val fp σ κ sm)
  (match κ
    [`(handle ,class-name* ,label ,κ)
     (let ([`(,op ,class-name) val])
       (if (subclass? class-name class-name*)
           (state (sm label) fp (λ (fp* val*)
                                   (if (equal? `(,fp $ex) `(,fp* ,val*))
                                       val
                                       (σ fp* val)))
                  κ sm)
           (handle-func val fp σ κ sm)))]
    [`(assign ,name ,s ,fp* ,κ)
     (handle-func val fp* σ κ sm)]
    [else #f]))

(define (step ς)
  (let ([stmt (state-statement ς)]
        [fp (state-frame-pointer ς)]
        [σ (state-store ς)]
        [κ (state-continuation ς)]
        [sm (state-statement-map ς)])
    (match (statement-stmt stmt)
      [`(skip)
       ; =>
       (state (statement-next stmt) fp σ κ sm)]
      [`(label ,label)
       ; =>
       (state (statement-next stmt) fp σ κ sm)]
      [`(goto ,label)
       ; =>
       (state (sm label) fp σ κ sm)]
      [`(if ,cond ,label)
       ; =>
       (if (eval-atom cond fp σ)
           (state (sm label) fp σ κ sm)
           (state (statement-next stmt) fp σ κ sm))]
      [`(:= ,name ,e)
       ; =>
       (state (statement-next stmt) fp (λ (fp* var)
                                          (if (equal? `(,fp ,name) `(,fp* var))
                                              (eval-atom e fp σ)
                                              (σ fp var)))
              κ sm)]
      [`(:=-new ,name ,class-name)
       ; =>
       (state (statement-next stmt) fp ((λ addr)
                                        (if (equal? addr name)
                                            `(,class-name ,(gensym 'op))
                                            (σ addr)))
              κ sm)]
      [`(invoke ,name ,args ...)
       ; =>
       (let ([m (find-method (statement-class stmt))])
         (apply-method m name (σ fp '$this) (method-args m) (statement-next stmt) fp σ κ sm))]
      [`(invoke-super ,name ,args ...)
       (let ([m (find-method (class-extends (statement-class stmt)))])
         (apply-method m name (σ fp '$this) (method-args m) (statement-next stmt) fp σ κ sm))]
       ; =>
      [`(return ,e)
       ; =>
       (apply-kont κ (eval-atom e fp σ) σ sm)]
      [`(push-handler ,class-name ,label)
       ; =>
       (state (statement-next stmt) fp σ (handle class-name label κ))]
      [`(pop-handler)
       ; =>
       (state (statement-next stmt) fp σ (handle-kont κ))]
      [`(throw ,e)
       ; =>
       (handle-func (eval-atom e fp σ) fp σ κ) sm]
      [`(move-exception ,name)
       ; =>
       (state (statement `(:= name $ex) (statement-next stmt)) fp σ κ sm)]
      [else #f]))))

(define (step* ς)
  (if (state? ς)
      (step* (step ς))
      (step* ς)))

(define (execute program)
  (let ([fp0 'not-done]
        [σ0 ((λ addr) (error (format "unbound address: ~a" addr)))]
        [sm (generate-statement-map program)])
    (step* (state program fp0 σ0 'halt sm))))

(define (run program)
  (execute (parse-program program)))

