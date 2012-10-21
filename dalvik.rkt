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

(define (parse program)
  program)

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
                   next})

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
    [(? symbol?)  (σ (fp atom))]
    [(? boolean?) atom]
    [(? integer?) atom]
    [else #f]))

(define (eval-object object fp σ)
  ; TODO
  )

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

(define apply-method m name val ς
  ; TODO
  )

(define apply-kont κ val store
  ; TODO
  )

(define (step ς)
  (let ([stmt (state-statement)]
        [fp (state-frme-pointer ς)]
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
       (state (statement-next stmt) fp ((λ addr)
                                        (if (equal? addr name)
                                            (eval-atom e fp σ)
                                            (σ addr)))
              κ sm)]
      [`(:=-new ,name ,obj-name)
       ; =>
       (state (statement-next stmt) fp ((λ addr)
                                        (if (equal? addr name)
                                            (eval-object obj-name fp σ)
                                            (σ addr)))
              κ sm)]
      [`(invoke ,name ,args ...)
       ; =>
       (apply-method (find-method 'not-done name)
                     ; TODO
                     )]
      [`(invoke-super ,name ,args ...)
       ; =>
       ; TODO
       ]
      [`(return ,value)
       ; =>
       ; TODO
       ]
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
  (execute (parse program)))
