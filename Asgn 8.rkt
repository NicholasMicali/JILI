#lang typed/racket

(require typed/rackunit)
(define-syntax tstruct
  (syntax-rules ()
    [(_ name fields)
     (struct name fields #:transparent)]))


; Progress Statement:
;;;;;;;;;;;;;;;;;;;
;
; Full program implemented
; 
;;;;;;;;;;;;;;;;;;;

#|
EBNF Notation for JILI8:

Expr = Num
     | id
     | String
     | {if Expr Expr Expr}
     | {var {[id : ty = Expr] ...} in Expr}
     | {[id : ty] ... => Expr}
     | {rec {id = {[id : ty] ... : ty => Expr}} in Expr}
     | {Expr Expr ...}


ty = num
    | bool
    | str
    | {ty ... -> ty}

operator = +
 	 | -
         | *
	 | /
 	 | num-eq?
  	 | str-eq?
 	 | <=
 	 | substring


... where an id is not if, :, =, var, in, rec, =>, or ->.

|#


;;;;;; Data Definitions 

; Components of JILI8 language
(define-type ExprC (U numC stringC idC ifC lamC appC recC))
(tstruct numC ([n : Real]))
(tstruct stringC ([s : String]))
(tstruct idC ([sym : Symbol]))
(tstruct ifC ([cond : ExprC] [then : ExprC] [else : ExprC]))
(tstruct lamC ([params : (Listof Symbol)] [types : (Listof Type)] [body : ExprC]))
(tstruct appC ([body : ExprC] [args : (Listof ExprC)]))
(tstruct recC ([name : Symbol] [params : (Listof Symbol)] [types : (Listof Type)] [return : Type]
                               [body : ExprC] [recBody : ExprC]))

; Values of JILI8 language
(define-type Value (U numV boolV primopV stringV cloV))
(tstruct cloV ([params : (Listof Symbol)] [body : ExprC] [env : Environment]))
(tstruct numV ([n : Real]))
(tstruct boolV ([b : Boolean]))
(tstruct stringV ([s : String]))
(tstruct primopV ([op : Symbol]))

; Types of the JILI8 language
(define-type Type (U numT boolT strT lamT))
(tstruct numT ())
(tstruct boolT ())
(tstruct strT ())
(tstruct lamT ([params : (Listof Type)] [return : Type]))

; Environments of the JILI8 langauge
(tstruct Binding ([name : Symbol] [val : (Boxof Value)]))
(define-type Environment (Listof Binding))
(define top-env (list (Binding 'true (box (boolV #t)))
                      (Binding 'false (box (boolV #f)))
                      (Binding '+ (box (primopV '+)))
                      (Binding '- (box (primopV '-)))
                      (Binding '* (box (primopV '*)))
                      (Binding '/ (box (primopV '/)))
                      (Binding '<= (box (primopV '<=)))
                      (Binding 'num-eq? (box (primopV 'num-eq?)))
                      (Binding 'str-eq? (box (primopV 'str-eq?)))
                      (Binding 'substring (box (primopV 'substring)))))


(tstruct tBinding ([sym : Symbol] [ty : Type]))
(define-type Type-Environment (Listof tBinding))
(define base-tenv (list (tBinding 'true (boolT))
                        (tBinding 'false (boolT))
                        (tBinding 'num (numT))
                        (tBinding 'bool (boolT))
                        (tBinding 'str (strT))
                        (tBinding '+ (lamT (list (numT) (numT)) (numT)))
                        (tBinding '- (lamT (list (numT) (numT)) (numT)))
                        (tBinding '* (lamT (list (numT) (numT)) (numT)))
                        (tBinding '/ (lamT (list (numT) (numT)) (numT)))
                        (tBinding '<= (lamT (list (numT) (numT)) (boolT)))
                        (tBinding 'num-eq? (lamT (list (numT) (numT)) (boolT)))
                        (tBinding 'str-eq? (lamT (list (strT) (strT)) (boolT)))
                        (tBinding 'substring (lamT (list (strT) (numT) (numT)) (strT)))))
                        

; Keywords that can not be id's
(define keywords '(if : = var in rec => ->))

; Purpose: takes any and returns true if it is a symbol not defined in keywords and false otherwise
(: legal-id? (Any -> Boolean : #:+ Symbol))
(define (legal-id? s)
  (and (symbol? s)
       (not (member s keywords))))




;;;;;; Important Functions

; Purpose: Parse and interpret a full JILI8 program from concrete syntax to String representation
;of the result

(define (top-interp [s : Sexp]) : String
  (define ast (parse s)) (type-check ast base-tenv) (serialize (interp ast top-env)))


; Purpose: Parses an S expression of concrete JILI8 syntax and returns the respective JILI8 structs
(define (parse [sexp : Sexp]) : ExprC
 (match sexp
    [(? real? n) (numC n)]
    [(? string? s) (stringC s)]
    [(list 'if cond then else) (ifC (parse cond) (parse then) (parse else))]
    [(? legal-id? sym) (idC sym)]
    [(list 'var (list (list (? legal-id? params) ': ty '= args) ...) 'in body)
     (if (duplicate? (cast params (Listof Symbol)))
         (appC (lamC (cast params (Listof Symbol))
                     (map parse-types (cast ty (Listof Sexp)))
                     (parse body)) (map parse (cast args (Listof Sexp))))
         (error 'parse "JILI found duplicate parameters ~e" exp))]
    [(list 'rec (list (? legal-id? name) '= (list (list (? legal-id? id) ': ty) ... ': recty '=> body)) 'in recbody)
     (recC name (cast id (Listof Symbol))
           (map parse-types (cast ty (Listof Sexp))) (parse-types recty) (parse body) (parse recbody))]
    [(list (list (? symbol? params) ': ty) ... '=> rest)
     (if (duplicate? (cast params (Listof Symbol)))
         (lamC (cast params (Listof Symbol)) (map parse-types (cast ty (Listof Sexp))) (parse rest))
         (error 'parse "JILI found duplicate parameters ~e" exp))]
    [(list f args ...) (appC (parse f) (map parse args))]
    [other (error 'parse "JILI failed to parse sexp ~e" sexp)]))



; Purpose: Parses the concrete syntax into a JILI8 Type
(define (parse-types [sexp : Sexp]) : Type
  (match sexp
    ['num (numT)]
    ['bool (boolT)]
    ['str (strT)]
    [(list params ... -> return) (lamT (map parse-types (cast params (Listof Sexp)))
                                                   (parse-types return))]
    [_ (error 'parse-types "JILI found illegal input type")]))


; Purpose: type-checks the JILI8 AST ExprC to check for a valid program
(define (type-check [exp : ExprC] [tenv : Type-Environment]) : Type
  (match exp
    [(numC n) (numT)]
    [(stringC s) (strT)]
    [(idC sym) (lookupt sym tenv)]
    [(ifC cond then else) (match (type-check cond tenv)
                            [(boolT) (match (type-check then tenv)
                                       [type (if (equal? type (type-check else tenv))
                                                 type
                                                 (error 'type-check "JILI found unmatched types in if ~e" type))])]
                            [_ (error 'type-check "JILI found wrong type in if condition ~e" cond)])]
    [(lamC params types body) (lamT types (type-check body (mult-textend tenv params types)))]
    [(recC name params types return body recbody)
     (define new-tenv (extend-tenv tenv name (lamT types return)))
     (match (type-check body (mult-textend new-tenv params types))
       [ty (match (type-check recbody new-tenv)
             [recty (if (equal? ty recty)
                        return
                        (error 'type-check "JILI found bad recursive call ~e" name))])])]
    [(appC body args) (match (type-check body tenv)
                     [(lamT types return) (if (equal? (map (lambda ([arg : ExprC]) (type-check arg tenv)) args) types)
                                              return
                                              (error 'type-check "JILI found incorrect type args ~e" types))]
                     [_ (error 'interp "JILI5 found unbound function ~e" exp)])]))
                        



; Purpose: Interprets a JILI8 program and returns the Value result.
(define (interp [e : ExprC] [env : Environment]) : Value
  (match e
    [(numC n) (numV n)]
    [(stringC s) (stringV s)]
    [(idC sym) (lookupS sym env)]
    [(ifC cond then else) (match (interp cond env)
                            [(boolV #t) (interp then env)]
                            [(boolV #f) (interp else env)])]
    [(lamC params types body) (cloV params body env)]
    [(recC name params types return body recbody)
     (define new-env (extend-env env name (stringV "dummy")))
     (set-box! (Binding-val (last new-env)) (interp (lamC params types body) new-env))
     (interp recbody new-env)]
    [(appC f args) (match (interp f env)
                     [(cloV params body cloV-env)
                       (define argVs (map (evalarg-help env) args))
                       (define new-env (mult-extend cloV-env params argVs))
                       (interp body new-env)]
                     [(primopV op) (define argVs (map (evalarg-help env) args))
                                    (primop-help op argVs)])]))


; Purpose: Serialize a Value to a string representation
(define (serialize [val : Value]) : String
  (match val
    [(numV n) (~v n)]
    [(boolV b) (if b "true" "false")]
    [(stringV s) (~v s)]
    [(cloV params body env) "#<procedure>"]
    [(primopV op) "#<primop>"]
    ))






;;;;;; Helper functions


; Purpose: extend the Environment with a name value pair
(define (extend-env [env : Environment] [name : Symbol] [value : Value]) : Environment
  (match env
    ['() (list (Binding name (box value)))]
    [(cons (Binding n v) r) (if (equal? n name) (cons (Binding name (box value)) (extend-env r name value))
                                                (cons (Binding n v) (extend-env r name value)))]))

; Purpose: extend the environment with a list of names to values
(define (mult-extend [env : Environment] [names : (Listof Symbol)] [values : (Listof Value)]) : Environment
  (match names
    ['() (match values
           ['() env])]
    [(cons firstN restN) (match values
                         [(cons firstV restV) (mult-extend (extend-env env firstN firstV) restN restV)])]))


; Purpose: extend the type Environment
(define (extend-tenv [tenv : Type-Environment] [name : Symbol] [type : Type]) : Type-Environment
  (match tenv
    ['() (list (tBinding name type))]
    [(cons (tBinding n ty) r) (if (equal? n name) (cons (tBinding name type) (extend-tenv r name type))
                                                (cons (tBinding n ty) (extend-tenv r name type)))]))

; Purpose: extend the type environment with a list of names to values
(define (mult-textend [tenv : Type-Environment] [names : (Listof Symbol)] [types : (Listof Type)]) : Type-Environment
  (match names
    ['() (match types
           ['() tenv])]
    [(cons firstN restN) (match types
                         [(cons firstT restT) (mult-textend (extend-tenv tenv firstN firstT) restN restT)])]))


; Purpose: check for duplicate symbols in a list of symbols
(define (duplicate? [l : (Listof Symbol)]) : Boolean
  (equal? (length (remove-duplicates l)) (length l)))

; Purpose: Divive primop and account for division by zero error
(define (mydiv [l : Real] [r : Real]) : Real
  (if (= r 0) (error 'mydiv "JILI divide by 0 ~e" exp) (/ l r)))

; Purpose: lookup binding of a symbol in its environment
(define (lookupS [id : Symbol] [env : Environment]) : Value
  (match env
    [(cons (Binding n v) r) (if (equal? n id) (unbox v) (lookupS id r))]))

; Purpose: lookup binding of a symbol in its type environment
(define (lookupt [id : Symbol] [tenv : Type-Environment]) : Type
  (match tenv
    ['() (error 'lookup "JILI found unbound type id ~e" id)]
    [(cons (tBinding n ty) r) (if (equal? n id) ty (lookupt id r))]))

; Purpose: given an environment, returns an interp helper function that converts an ExprC to a value
(define (evalarg-help [env : Environment]) : (ExprC -> Value)
  (lambda (arg) (interp arg env)))

; Purpose: helper function to lookup a primops associated racket procedure
(define (lookupOP [op : Symbol]) : (Real Real -> Real)
  (match op
    ['+ +]
    ['- -]
    ['* *]
    ['/ mydiv]))

; Purpose: helper function to match primops and preform the respective operation on its arguments
(define (primop-help [op : Symbol] [args : (Listof Value)]) : Value
  (match op
    ['<= (match args
           [(list (numV n1) (numV n2)) (boolV (<= n1 n2))])]
    ['num-eq? (match args
               [(list v1 v2) (boolV (equal? v1 v2))])]
    ['str-eq? (match args
               [(list v1 v2) (boolV (equal? v1 v2))])]
    ['substring (match args
                  [(list (stringV s) (numV (? integer? start)) (numV (? integer? end)))
                   (stringV (substring s (cast start Integer) (cast end Integer)))])]
    [(? symbol? numOP) (match args
                          [(list (numV n1) (numV n2)) (numV ((lookupOP numOP) n1 n2))])]))





;;;;;;; Test Cases


; simple tests
(check-equal? (top-interp '7) "7")
(check-equal? (top-interp 'true) "true")
(check-equal? (top-interp 'false) "false")
(check-equal? (top-interp '+) "#<primop>")
(check-equal? (top-interp '{[a : num] => a}) "#<procedure>")
(check-equal? (top-interp '{[a : num] [b : num] => {+ a b}}) "#<procedure>")
(check-equal? (top-interp '{{[a : num] => a} 5}) "5")
(check-equal? (top-interp '{+ 5 2}) "7")
(check-equal? (top-interp '{num-eq? 5 5}) "true")
(check-equal? (top-interp '{num-eq? 5 4}) "false")
(check-equal? (top-interp '{str-eq? "s" "s"}) "true")
(check-equal? (top-interp '{[a : bool] => a}) "#<procedure>")

(check-equal? (top-interp '{{[a : num] [b : num] => {- a b}} 5 2}) "3")
(check-equal? (top-interp '{{[a : num] [b : num] => {* a b}} 5 2}) "10")
(check-equal? (top-interp '{{[a : num] [b : num] => {/ a b}} 6 2}) "3")
(check-equal? (top-interp '{{[a : num] [b : num] => {<= a b}} 5 2}) "false")
(check-equal? (top-interp '{{[a : num] => {{[x : num] => {+ x a}} 5}} 2}) "7")

(check-equal? (top-interp '{if {num-eq? 1 1} "yup" "nope"})  "\"yup\"")
(check-equal? (top-interp '{if {str-eq? "h" "j"} "yup" "nope"}) "\"nope\"")

; more complicated
(check-equal? (top-interp '{{[b : num] => {* {{[b : num] => {+ b 5}} 7} b}} 3}) "36")
(check-equal? (top-interp '{{[x : num] => {{[x : num] => {+ x x}} 5}} 2}) "10")

(check-equal? (top-interp '{var {[z : num = 5] [y : num = 6]} in {+ z y}}) "11")
(check-equal? (top-interp '{substring "hello" 0 3}) "\"hel\"")

(check-equal? (top-interp '{rec {fact = {[n : num] : num =>
                       {if {<= n 0} 1 {* n {fact {- n 1}}}}}}
     in
     {fact 4}}) "24")
(check-equal? (top-interp '{rec {square-helper = {[n : num] : num =>
                       {if {<= n 0} 0 {+ n {square-helper {- n 2}}}}}}
     in
  {var {[square : {num -> num}  =
        {[n : num] => {square-helper {- {* 2 n} 1}}}]}
    in
    {square 13}}}) "169")


; JILI exceptions (syntax, type, and math errors)
(check-exn #px"JILI"
           (λ () (top-interp '{})))
(check-exn #px"JILI"
           (λ () (top-interp '{/ 4 0})))
(check-exn #px"JILI"
           (λ () (top-interp '{/ z 2})))
(check-exn #px"JILI"
           (λ () (top-interp '{z 6})))
(check-exn #px"JILI"
           (λ () (top-interp '{/ 4})))
(check-exn #px"JILI"
           (λ () (top-interp '{<= 4 false})))
(check-exn #px"JILI"
           (λ () (top-interp '{{[x : num] => {* x 2}} 5 4})))
(check-exn #px"JILI"
           (λ () (top-interp '{{[x : num] [y : num] => {+ x y}} 2})))
(check-exn #px"JILI"
           (λ () (top-interp '{{[a : num] => {<= a "l"}} 5})))
(check-exn #px"JILI"
           (λ () (top-interp '{{[x : str] => {* x 2}} 5})))
(check-exn #px"JILI"
           (λ () (top-interp '{+ "hi" 5})))
(check-exn #px"JILI"
           (λ () (top-interp '{{[x : num] => {str-eq? x "5"}} 5})))
(check-exn #px"JILI"
           (λ () (top-interp '{{[x : bool] [x : bool] => x} true false})))
(check-exn #px"JILI"
           (λ () (top-interp '{var {[x : bool = true] [x : bool = false]} in x})))
(check-exn #px"JILI"
           (λ () (top-interp '{{[x : idk] => x} true})))
(check-exn #px"JILI"
           (λ () (top-interp '{if "hi" 5 4})))
(check-exn #px"JILI"
           (λ () (top-interp '{if true 5 "hi"})))
(check-exn #px"JILI"
           (λ () (top-interp '{yo 5 4})))
(check-exn #px"JILI"
           (λ () (top-interp '{rec {fact = {[n : num] : bool => {if {<= n 0} 1 {* n {fact {- n 1}}}}}}
                                in {fact 4}})))
(check-exn #px"JILI"
           (λ () (top-interp '{rec {fact = {[n : num] : num => {if {<= n 0} 1 {* n {fact {- n 1}}}}}}
                                in {substring "hello" 0 {fact 1}}})))
(check-exn #px"JILI"
           (λ () (type-check (parse '("abc" 9)) base-tenv)))
(check-exn #px"JILI"
           (λ () (top-interp '{{[b : num] => {* {{[b : num] => {+ b 5}} "astring"} b}} 3})))
(check-exn #px"JILI"
           (λ () (top-interp '{+ 3 {[a : num] => a}})))








