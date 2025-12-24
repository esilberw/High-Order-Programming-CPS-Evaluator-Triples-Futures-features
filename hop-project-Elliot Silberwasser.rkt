#lang r5rs

(define (error . msg)
  (display "ERROR: ")
  (display msg)
  (newline))

(define apply-in-underlying-scheme apply)

;;; ============================================================================
(define (cpseval exp env cnt)
  (cond ((self-evaluating? exp)
         (eval-self-evaluating exp env cnt))
        ((variable? exp)
         (eval-variable exp env cnt))
        ((quoted? exp)
         (eval-quoted exp env cnt))
        ((assignment? exp)
         (eval-assignment exp env cnt))
        ((definition? exp)
         (eval-definition exp env cnt))
        ((if? exp)
         (eval-if exp env cnt))
        ((lambda? exp)
         (eval-lambda exp env cnt))
        ((begin? exp)
         (eval-begin exp env cnt))
        ((cond? exp)
         (cpseval (cond->if exp) env cnt))
        ((let? exp)
         (cpseval (let->lambda exp) env cnt))
        ((application? exp)
         (eval-application exp env cnt))
        (else
         (error "Unknown expression type -- EVAL" exp))))

(define (meta-apply procedure arguments cnt)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure arguments cnt))
        ((compound-procedure? procedure)
         (eval-sequence
          (procedure-body procedure)
          (extend-environment
           (procedure-parameters procedure)
           arguments
           (procedure-environment procedure))
          cnt))
        ((continuation? procedure)
         ((continuation-cnt procedure) (car arguments)))        
        (else
         (error
          "Unknown procedure type -- APPLY" procedure))))

(define (eval-self-evaluating exp env cnt)
  (cnt exp))

(define (eval-quoted exp env cnt)
  (cnt (text-of-quotation exp)))

(define (eval-lambda exp env cnt)
  (cnt (make-procedure (lambda-parameters exp)
                         (lambda-body exp)
                         env)))

(define (eval-variable exp env cnt)
  (cnt (lookup-variable-value exp env)))

(define (eval-if exp env cnt)
  (cpseval (if-predicate exp) env
        (lambda (value)
          (if (true? value)
              (cpseval (if-consequent exp) env cnt)
              (cpseval (if-alternative exp) env cnt)))))

(define (eval-begin exp env cnt)
  (eval-sequence (begin-actions exp) env cnt))

(define (eval-sequence exps env cnt)
  (if (last-exp? exps)
      (cpseval (first-exp exps) env cnt)
      (cpseval (first-exp exps) env
            (lambda (value)
              (eval-sequence (rest-exps exps) env cnt)))))

(define (eval-assignment exp env cnt)
  (cpseval (assignment-value exp) env
        (lambda (value)
          (set-variable-value! (assignment-variable exp) value env)
          (cnt 'ok))))
 
(define (eval-definition exp env cnt)
  (cpseval (definition-value exp) env
        (lambda (value)
          (define-variable! (definition-variable exp) value env)
          (cnt 'ok))))

(define (eval-application exp env cnt)
  (cpseval (operator exp) env
        (lambda (proc)
          (list-of-values (operands exp) env
                    (lambda (args)
                      (meta-apply proc args cnt))))))

(define (list-of-values exps env cnt)
  (if (no-operands? exps)
      (cnt '())
      (cpseval (first-operand exps) env
            (lambda (arg)
              (list-of-values (rest-operands exps) env
                              (lambda (args)
                                (cnt (cons arg args))))))))
  

;;; ============================================================================ 
(define (self-evaluating? exp)
  (cond ((number? exp) #t)
        ((string? exp) #t)
        (else #f)))
 
(define (variable? exp) (symbol? exp))
 
(define (quoted? exp)
  (tagged-list? exp 'quote))
 
(define (text-of-quotation exp) (cadr exp))
 
(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      #f))
 
(define (assignment? exp)
  (tagged-list? exp 'set!))
(define (assignment-variable exp) (cadr exp))
(define (assignment-value exp) (caddr exp))
 
(define (definition? exp)
  (tagged-list? exp 'define))
(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))
(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)   ; formal parameters
                   (cddr exp)))) ; body
 
(define (lambda? exp) (tagged-list? exp 'lambda))
(define (lambda-parameters exp) (cadr exp))
(define (lambda-body exp) (cddr exp))
 
(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))
 
(define (if? exp) (tagged-list? exp 'if))
(define (if-predicate exp) (cadr exp))
(define (if-consequent exp) (caddr exp))
(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      'false))
 
(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))
 
(define (begin? exp) (tagged-list? exp 'begin))
(define (begin-actions exp) (cdr exp))
(define (last-exp? seq) (null? (cdr seq)))
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))
 
(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))
(define (make-begin seq) (cons 'begin seq))
 
(define (application? exp) (pair? exp))
(define (operator exp) (car exp))
(define (operands exp) (cdr exp))
(define (no-operands? ops) (null? ops))
(define (first-operand ops) (car ops))
(define (rest-operands ops) (cdr ops))

(define (cond? exp) (tagged-list? exp 'cond))
(define (cond-clauses exp) (cdr exp))
(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))
(define (cond-predicate clause) (car clause))
(define (cond-actions clause) (cdr clause))
(define (cond->if exp)
  (expand-clauses (cond-clauses exp))) 
(define (expand-clauses clauses)
  (if (null? clauses)
      'false                          ; no else clause
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence->exp (cond-actions first))
                (error "ELSE clause isn't last -- COND->IF"
                       clauses))
            (make-if (cond-predicate first)
                     (sequence->exp (cond-actions first))
                     (expand-clauses rest))))))

(define (let? exp) (tagged-list? exp 'let)) 
(define (let-clauses exp) (cadr exp))
(define (let-body exp) (cddr exp))
(define (let-variables exp) 
  (map car (let-clauses exp)))
(define (let-expressions exp)
  (map cadr (let-clauses exp)))

  
(define (let->lambda exp) 
  (cons
   (make-lambda (let-variables exp) (let-body exp)) 
   (let-expressions exp))) 


;=== IMPLEMENTATION OF TRIPLE TYPE 1.1 ===

;CHECK of type:
(define (triple? obj)
  (and (pair? obj)
       (tagged-list? obj 'triple) ; check the TAG equiv to (eq? (car obj) 'triple)
       (pair? (cdr obj))
       (pair? (cddr obj))
       (pair? (cdddr obj))
       (null? (cddddr obj)))) ; Check if the 5 th elem of the list is '() (=empty list), we want only 3 elems.

;CREATION:
(define (make-triple-primitive args cnt)
  ; Check if there are only 3 arguments; else: error
  (if (and (pair? args)
           (pair? (cdr args))
           (pair? (cddr args))
           (null? (cdddr args)))   
      (let ((first  (car args))
            (second (cadr args))
            (third  (caddr args)))
        (list 'triple first second third)) ; create a tagged-list using 'triple as a tag
      (error "make-triple expects exactly 3 arguments" args)))


;ACCESSORS:
(define (first-primitive args cnt)
  (let ((triple (car args)))
    (if (triple? triple)
        (cadr triple) ; return the first elem
        (error "first: not a triple" triple))))

(define (second-primitive args cnt)
  (let ((triple (car args)))
    (if (triple? triple)
        (caddr triple)
        (error "second: not a triple" triple))))

(define (third-primitive args cnt)
  (let ((triple (car args)))
    (if (triple? triple)
        (cadddr triple)
        (error "third: not a triple" triple))))

;MUTATORS:
(define (set-first!-primitive args cnt)
  (let ((triple (car args))
        (new-first (cadr args)))
    (if (triple? triple)
        (begin
          (set-car! (cdr triple) new-first)
          'mutation_pass)
        (error "set-first!: not a triple" triple))))

(define (set-second!-primitive args cnt)
  (let ((triple (car args))
        (new-second (cadr args)))
    (if (triple? triple)
        (begin
          (set-car! (cddr triple) new-second)
          'mutation_pass)
        (error "set-second!: not a triple" triple))))


(define (set-third!-primitive args cnt)
  (let ((triple (car args))
        (new-third (cadr args)))
    (if (triple? triple)
        (begin
          (set-car! (cdddr triple) new-third)
          'mutation_pass)
        (error "set-third!: not a triple" triple))))
 
;;; ============================================================================
(define (true? x)
  (not (eq? x #f)))
(define (false? x)
  (eq? x #f))
 
(define (make-procedure parameters body env)
  (list 'procedure parameters body env))
(define (compound-procedure? p)
  (tagged-list? p 'procedure))
(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))
 
 
(define (enclosing-environment env) (cdr env))
(define (first-frame env) (car env))
(define the-empty-environment '())
 
(define (make-frame variables values)
  (cons variables values))
(define (frame-variables frame) (car frame))
(define (frame-values frame) (cdr frame))
(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (car frame)))
  (set-cdr! frame (cons val (cdr frame))))
 
(define (extend-environment vars vals base-env)
  (if (= (length vars) (length vals))
      (cons (make-frame vars vals) base-env)
      (if (< (length vars) (length vals))
          (error "Too many arguments supplied" vars vals)
          (error "Too few arguments supplied" vars vals))))
 
(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (car vals))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))
 
(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable -- SET!" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))
 
(define (define-variable! var val env)
  (let ((frame (first-frame env)))
    (define (scan vars vals)
      (cond ((null? vars)
             (add-binding-to-frame! var val frame))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (scan (frame-variables frame)
          (frame-values frame))))

(define (make-primitive underlying-scheme-proc)
  (list 'primitive underlying-scheme-proc))

(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))
 
(define (primitive-implementation proc) (cadr proc))

(define (make-continuation cnt)
  (list 'continuation cnt))
 
(define (continuation? c)
  (tagged-list? c 'continuation))
 
(define (continuation-cnt c) (cadr c))

(define (wrap-underlying-primitive p)
  (lambda (args cnt)
    (apply-in-underlying-scheme p args)))

(define (call-cc-primitive args cnt)
 (let ((proc (car args)))
   (meta-apply proc (list (make-continuation cnt)) cnt)))
                             
(define primitive-procedures
  (list (list '+ (wrap-underlying-primitive +))
        (list '- (wrap-underlying-primitive -))
        (list '* (wrap-underlying-primitive *))
        (list '< (wrap-underlying-primitive <))
        (list 'eq? (wrap-underlying-primitive eq?))
        (list 'car (wrap-underlying-primitive car))
        (list 'cdr (wrap-underlying-primitive cdr))
        (list 'cons (wrap-underlying-primitive cons))
        (list 'make-triple make-triple-primitive) ;ADDED
        (list 'first first-primitive) ;ADDED
        (list 'second second-primitive) ; ADDED
        (list 'third third-primitive) ;ADDED
        (list 'set-first! set-first!-primitive);ADDED
        (list 'set-second! set-second!-primitive) ;ADDED
        (list 'set-third! set-third!-primitive) ;ADDED
        (list 'null? (wrap-underlying-primitive null?))
        (list 'display (wrap-underlying-primitive display))
        (list 'newline (wrap-underlying-primitive newline))
        (list 'call/cc call-cc-primitive)
        ))

(define (primitive-procedure-names)
  (map car primitive-procedures))
 
(define (primitive-procedure-objects)
  (map make-primitive (map cadr primitive-procedures))) 
 
(define (apply-primitive-procedure proc args cnt)
  (cnt ((primitive-implementation proc) args cnt))) ; !! DO Already apply CNT on the primitive that we give to apply, don't need to add one the return value of our primitives
 
(define (setup-environment)
  (let ((initial-env
         (extend-environment (primitive-procedure-names)
                             (primitive-procedure-objects)
                             the-empty-environment)))
    (define-variable! 'false #f initial-env)
    (define-variable! 'true #t initial-env)
    initial-env))
 
(define the-global-environment (setup-environment))

(define input-prompt ";;; CPS-Eval:")
(define output-prompt ";;; CPS-Eval value:")
(define (driver-loop)
  (prompt-for-input input-prompt)
  (let ((input (read)))
    (cpseval input
          the-global-environment
          (lambda (value)
            (announce-output output-prompt)
            (user-print value)
            (driver-loop)))))

(define (prompt-for-input string)
  (newline) (newline) (display string) (newline))
 
(define (announce-output string)
  (newline) (display string)
  (newline))

(define (print-object obj)
  (cond
    ((compound-procedure? obj)
     (display (list 'compound-procedure
                    (procedure-parameters obj)
                    (procedure-body obj)
                    'procedure-environment)))

    ; Add specific user-print := t(first second third), in a recursif way to handle recursive triples.
    ((triple? obj)
     (display "t(")
     (print-object (cadr obj))
     (display " ")
     (print-object (caddr obj))
     (display " ")
     (print-object (cadddr obj))
     (display ")"))

    (else
     (display obj))))

(define (user-print object)
  (print-object object))
 
(driver-loop)