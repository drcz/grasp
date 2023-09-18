(import (assert))
(import (infix))
(import (define-object))
(import (define-type))
(import (define-interface))
(import (define-property))
(import (define-cache))
(import (keyword-arguments))
(import (extent))
(import (match))
(import (for))
(import (functions))
(import (examples))
(import (fundamental))
(import (indexable))
(import (primitive))
(import (painter))
(import (space))
(import (text))
(import (comments))
(import (interactive))
(import (extension))
(import (parse))
(import (mapping))
(import (combinators))
(import (print))
(import (button))

(define (render-foreground! expression::Element
			    counterparts::(maps (Element)
						to: (list-of
						     Element))
			    source-position::(maps (Element)
						   to: Position)
			    target-position::(maps (Element)
						   to: Position)
			    intensity::float)
  ::void
  (let ((links (counterparts expression))
	(painter ::Painter (the-painter)))
    (cond
     ((empty? links)
      (draw-emerging! expression
		      (source-position expression)
		      intensity)
      (when (gnu.lists.LList? expression)
	(traverse
	 expression
	 doing:
	 (lambda (sub::Element t::Traversal)
	   (render-foreground! sub counterparts
			       source-position
			       target-position
			       intensity)))))

     (else
      (for x in links
	(draw-morph! expression x counterparts
		     source-position
		     target-position
		     intensity))))))


(define (draw-morph! foreground::Element
		     background::Element
		     counterparts::(maps (Element)
					 to: (list-of
					      Element))
		     source-position::(maps (Element)
					    to: Position)
		     target-position::(maps (Element)
					    to: Position)
		     progress::float)
  ::void
  (let* ((p0 ::Position (source-position foreground))
	 (p1 ::Position (target-position background))
	 (painter ::Painter (the-painter))
	 (left ::real (linear-interpolation
		       from: p0:left to: p1:left
		       at: progress))
	 (top ::real (linear-interpolation
		      from: p0:top to: p1:top
		      at: progress)))
    (cond
     ((equal? foreground background)
      ;; here we just draw the foreground
      ;; with full intensity
      (with-translation (left top)
	(draw! foreground)))

     ((or (isnt foreground Tile?)
	  (isnt background Tile?))
      ;; at least one of the elements is (presumably)
      ;; a space, so the only way we can morph them
      ;; is by fading
      (with-translation (left top)
	(painter:with-intensity (- 1.0 progress)
	  (lambda ()
	    (draw! background)))
	(painter:with-intensity progress
	  (lambda ()
	    (draw! foreground)))))

     ((and (gnu.lists.LList? foreground)
	   (gnu.lists.LList? background))
      (let* ((e0 ::Extent (extent foreground))
	     (e1 ::Extent (extent background))
	     (width ::real (linear-interpolation
			    from: e0:width to: e1:width
			    at: progress))
	     (height ::real (linear-interpolation
			     from: e0:height to: e1:height
			     at: progress)))
	(with-translation (left top)
	  (painter:draw-box! width height '()))
	(traverse
	 foreground
	 doing:
	 (lambda (item::Element t::Traversal)
	   (render-foreground! item
			       counterparts
			       source-position
			       target-position
			       progress)))))
     ((and (Tile? foreground)
	   (Tile? background))
      (let* ((e0 ::Extent (extent foreground))
	     (e1 ::Extent (extent background))
	     (width ::real (linear-interpolation
			    from: e0:width to: e1:width
			    at: progress))
	     (height ::real (linear-interpolation
			     from: e0:height to: e1:height
			     at: progress)))
	(with-translation (left top)
	  (painter:with-intensity (- 1.0 progress)
	    (lambda ()
	      (painter:with-stretch
		  (/ width e1:width)
		  (/ height e1:height)
		(lambda ()
		  (draw! background)))))
	  (painter:with-intensity progress
	    (lambda ()
	      (painter:with-stretch
	       (/ width e0:width)
	       (/ height e0:height)
	       (lambda ()
		 (draw! foreground))))))))
     )))

(define (draw-emerging! expression::Element p::Position
			intensity::float)
  ::void
  (let ((painter ::Painter (the-painter)))
    (painter:with-intensity intensity
      (lambda ()
	(with-translation (p:left p:top)
	  (if (gnu.lists.LList? expression)
	      (let ((outer ::Extent (extent expression)))
		(painter:draw-box! outer:width outer:height '()))
	      (draw! expression)))))))

(define (render-background! expression::Element
			    counterparts::(maps (Element)
						to: (list-of
						     Element))
			    position::(maps (Element)
					    to: Position)
			    intensity::float)
  ::void
  (when (empty? (counterparts expression))
    (draw-emerging! expression (position expression) intensity))
  (when (gnu.lists.LList? expression)
    (traverse
     expression
     doing:
     (lambda (sub::Element t::Traversal)
       (render-background! sub counterparts position
			   intensity)))))

(define/kw (measure-positions!
	    expression
	    left::real := 0
	    top::real := 0
	    into:
	    measurements::(!maps (Element) to: Position)
	    := (property+ (element::Element)::Position
			  (Position left: 0 top: 0)))
  ::(maps (Element) to: Position)
  (if (list? expression)
      (traverse
       expression
       doing:
       (lambda (item::Element t::Traversal)
	 (let ((p ::Position (measurements item)))
	   (set! p:left (+ t:left left))
	   (set! p:top (+ t:top top))
	   (when (list? item)
	     (measure-positions! item p:left p:top
				 into: measurements))))
       returning:
       (lambda (t::Traversal)
	 measurements))
      measurements))

(define-object (Morph initial::Tile
		      final::Tile
		      origin::(maps (Element) to: (list-of
						   Element))
		      progeny::(maps (Element) to: (list-of
						    Element)))
  ::Enchanted
  (define progress ::float 0.0)

  (define initial-position ::(maps (Element) to: Position)
    (measure-positions! initial))

  (define initial-extent ::Extent
    (initial:extent))

  (define final-position ::(maps (Element) to: Position)
    (measure-positions! final))

  (define final-extent ::Extent
    (final:extent))

  (define maximum-extent ::Extent
    (Extent width: (max initial-extent:width
			final-extent:width)
	    height: (max initial-extent:height
			 final-extent:height)))

  (define (extent) ::Extent maximum-extent)

  (define shift ::(maps (Element) to: Position)
    (property+ (element::Element)::Position
	       (Position left: 0 top: 0)))

  (define (draw! context::Cursor)::void
    (cond ((is progress <= 0.5) ;>
	   (render-background! final origin final-position
			       progress)
	   (render-foreground! initial
			       progeny
			       initial-position
			       final-position
			       (- 1.0 progress)))
	  (else
	   (render-background! initial progeny
			       initial-position
			       (- 1.0 progress))
	   (render-foreground! final
			       origin
			       final-position
			       initial-position
			       progress))))
  (Magic))

(define (self-evaluating? x)
  (and (isnt x list?)
       (isnt x pair?)
       (if (Atom? x)
	   (isnt (x:value) symbol?)
	   #t)))

(define-object (EvaluationContext)
  ;;(define macro-definitions ::)

  (define definitions ::java.util.Map
    (let ((table ::java.util.Map (java.util.HashMap)))
      (table:put (Atom "+") +)
      (table:put (Atom "-") -)
      (table:put (Atom "*") *)
      (table:put (Atom "/") /)
      (table:put (Atom "<") <)
      (table:put (Atom "<=") <=)
      (table:put (Atom ">") >)
      (table:put (Atom ">=") >=)
      (table:put (Atom "=") =)
      (table:put (Atom "eq?") eq?)		
      (table:put (Atom "eqv?") eqv?)
      (table:put (Atom "cons")
		 (lambda args
		   (match args
		     (`(',a ',b)
		      (cons (Atom "quote") (cons a b)))
		     (`(,a ',b)
		      (cons (Atom "quote") (cons a b)))
		     (`(',a ,b)
		      (cons (Atom "quote") (cons a b)))
		     (`(,a ,b)
		      (cons (Atom "quote") (cons a b))))))
      (table:put (Atom "car")
		 (lambda (x)
		   (match x
		     (`'(,a . ,b)
		      (if (self-evaluating? a)
			  a
			  (cons (Atom "quote") a))))))
      (table:put (Atom "cdr")
		 (lambda (x)
		   (match x
		     (`'(,a . ,b)
		      (if (self-evaluating? b)
			  b
			  (cons (Atom "quote") b))))))
      (table:put (Atom "pair?")
		 (lambda (x)
		   (and-let* ((`'(,_ . ,_) x)))))
      (table:put (Atom "null?")
		 (lambda (x)
		   (and-let* ((`'() x)))))
      table))

  (define (value symbol)
    (cond ((definitions:contains-key symbol)
	   (definitions:get symbol))
	  (else
	   (error "undefined symbol: "symbol))))

  (define (defines-macro? symbol)
    #f)

  (define (defines? symbol)
    (definitions:contains-key symbol))

  (define (define! name value)
    (definitions:put name value))

  (define (primitive? symbol)
    (and (definitions:contains-key symbol)
	 (let ((value (definitions:get symbol)))
	   (procedure? value))))
  )

(define default-context ::EvaluationContext
  (EvaluationContext))

(default-context:define! (Atom "!")
  (car (parse-string "\
(lambda (n)
  (if (<= n 1)
     1 #| base case |#
     (* n (! (- n 1)))))")))

(default-context:define! (Atom "append")
  (car (parse-string "\
(lambda (a b)
  (if (null? a)
     b
     (cons (car a) (append (cdr a) b))))")))

(define (grasp expression)
  (cond ((pair? expression)
	 (cons (grasp (car expression))
	       (grasp (cdr expression))))
	((null? expression)
	 (empty))
	((string? expression)
	 (text expression))
	((symbol? expression)
	 (Atom (symbol->string expression)))
	((number? expression)
	 (Atom (number->string expression)))
	(else
	 (Atom (show->string expression)))))

(define (reduce expression
		#!optional
		(origin::(!maps (Element) to: (list-of Element))
			 (property (e::Element)::(list-of Element)
				   (recons e '())))
		(progeny::(!maps (Element) to: (list-of Element))
			  (property (e::Element)::(list-of Element)
				    (recons e '())))
		#!key
		(context::EvaluationContext default-context))
  
  (define (mark-origin! newborn parent)
    (set! (origin newborn) (recons parent '()))
    (set! (progeny parent) (recons newborn '())))

  (define (add-origin! newborn parent)
    (and-let* ((`(,default) (origin newborn))
	       ((eq? newborn default)))
      (set! (origin newborn) '()))
    (and-let* ((`(,default) (progeny parent))
	       ((eq? parent default)))
      (set! (progeny parent) '()))
    (set! (origin newborn) (recons parent (origin newborn)))
    (set! (progeny parent) (cons newborn (progeny parent))))
  
  (define (dissolve! item)
    (set! (origin item) '())
    (when (gnu.lists.LList? item)
      (traverse
       item
       doing:
       (lambda (e::Element t::Traversal)
	 (dissolve! e)))))

  (define (substitute variables #;with values #;in expression)
    (match expression
      (`(quote ,_)
       expression)
      (`(lambda ,args ,body)
       (let*-values (((variables* values*) (only. (isnt _ in. args)
						  variables values))
		     ((lambda*) (car expression))
		     ((result) (cons* lambda* args
				      (substitute variables* #;with values*
						  #;in body))))
	 (copy-properties cell-display-properties
			  (cdr expression) (cdr result))
	 (copy-properties cell-display-properties
			  expression result)
	 result))
      (`(,operator . ,operands)
       (let ((result (cons (substitute variables #;with values
				       #;in operator)
			   (substitute variables #;with values
				       #;in operands))))
	 (copy-properties cell-display-properties expression
			  result)))
      (_
       (if (Atom? expression)
	   (let* ((result (counterpart #;of expression #;from variables
					    #;in values)))
	     (if (eq? result expression)
		 result
		 (let ((result (copy result)))
		   (add-origin! result expression)
		   result)))
	   expression))))

  (define (counterpart #;of variable #;from variables
			    #;in values)
    (match variables
      (`(,,variable . ,_)
       (let ((result (car values)))
	 (if (self-evaluating? result)
	     result
	     (cons (Atom "quote") result))))
      (,variable
       (cons (Atom "quote") values))
      (`(,_ . ,rest)
       (counterpart #;of variable #;from rest
			 #;in (cdr values)))
      (_
       variable)))
  
  (define (reduce-operands operands)
    (match operands
      (`(,first . ,rest)
       (let ((first* (reduce first)))
	 (if (equal? first first*)
	     (let* ((result (cons first (reduce-operands rest))))
	       (mark-origin! result operands)
	       (copy-properties cell-display-properties operands result))
	     (let ((result (cons first* rest)))
	       (mark-origin! result operands)
	       (mark-origin! first* first)
	       (copy-properties cell-display-properties operands result)))))
      (`()
       operands)
      (_
       (reduce operands))))

  (define (reduce expression)
    (WARN "reducing "expression)
    (match expression
      (`(if #f ,then ,else)
       (dissolve! expression)
       (mark-origin! else expression)
       else)
      (`(if ,test ,then ,else)
       (WARN "conditional: "expression)
       (let ((test* (reduce test))
	     (if* (car expression)))
	 (cond ((equal? test test*)
		(dissolve! expression)
		(mark-origin! then expression)
		then)
	       (else
		(let ((result (cons* if* test* then else '())))
		  (mark-origin! result expression)
		  (mark-origin! test* test)
		  (copy-properties cell-display-properties
				   (cdr expression) (cdr result))
		  (copy-properties cell-display-properties
				   expression result))))))
      (`(lambda ,args ,body)
       expression)
      (`(quote ,_)
       expression)
      (`(,operator . ,operands)
       (if (and (Atom? operator)
		(context:defines-macro? operator))
	   (error "Macros not supported (yet)")
	   (let ((operands* (reduce-operands operands)))
	     (if (isnt operands equal? operands*)
		 (let ((result (cons operator operands*)))
		   (mark-origin! operands* operands)
		   (mark-origin! result expression)
		   (copy-properties cell-display-properties expression
				    result))
		 (match operator
		   (,@Atom?		    
		    (cond ((context:primitive? operator)
			   (let* ((result
				   (grasp
				    (parameterize ((cell-access-mode
						    CellAccessMode:Evaluating))
				      (WARN "applying "(context:value operator)
					    " to "operands)
				      (apply (context:value operator)
					     (map (lambda (x) x) operands))))))
			     (dissolve! expression)
			     (mark-origin! result expression)
			     result))
			  ((context:defines? operator)
			   (reduce (cons (context:value operator)
					 operands)))
			  (else
			   expression)))
		   (`(lambda ,args ,body)
		    (substitute args #;with operands
				#;in body))
		   (`(,_ . ,_)
		    (let* ((operator* (reduce operator))
			   (result (cons operator* operands)))
		      (mark-origin! result expression)
		      (mark-origin! operator* operator)
		      (copy-properties cell-display-properties expression
				       result)))
		   (_
		    expression))))))
      (_
       (if (and (Atom? expression)
		(context:defines? expression))
	   (let ((result (context:value expression)))
	     (dissolve! expression)
	     (mark-origin! result expression)
	     result)
	   expression))))

  (values (reduce expression)
	  origin
	  progeny))

(define (in. element collection)
  (any. (is _ equal? element) collection))

(define-mapping (morph-to expression::Tile)::Morph
  (Morph expression expression
	 (property (e::Element)::(list-of Element)
		   (recons e '()))
	 (property (e::Element)::(list-of Element)
				    (recons e '()))))

(define/memoized (morph-from expression::Tile)::Morph
  (WARN "reducing "expression)
  (let*-values (((reduced origins progenies) (reduce expression))
		((result) (Morph expression reduced origins progenies)))
    (WARN " to "reduced)
    (set! (morph-to reduced) result)
    result))

(define-interface Playable ()
  (rewind!)::void
  (back!)::void
  (play!)::void
  (pause!)::void
  (next!)::void
  (fast-forward!)::void
  (playing?)::boolean)

(define-interface Player (Enchanted Playable Animation))

(define-object (Stepper initial-expression::Tile)::Player

  (define (typename)::String "Stepper")

  (define duration/ms ::float 700.0)
  
  (define current-morph ::Morph
    (morph-from initial-expression))

  (define playing-backwards? ::boolean #f)
  
  (define (advance! timestep/ms::int)::boolean
    (let ((change (/ timestep/ms duration/ms)))
      (WARN "advance by "change)
      (if playing-backwards?
	  (let ((new-progress (- current-morph:progress change)))
	    (WARN "new progress "new-progress)
	    (cond
	     ((is new-progress <= 0.0)
	      (let ((initial current-morph:initial))
		(set! current-morph (morph-to initial))
		(set! current-morph:progress 1.0)
		(when (equal? initial current-morph:initial)
		  (set! now-playing? #f)))
	      now-playing?)
	     (else
	      (set! current-morph:progress new-progress)
	      #t)))
	  (let ((new-progress (+ current-morph:progress change)))
	    (WARN "new progress "new-progress)
	    (cond
	     ((is new-progress >= 1.0)
	      (let ((final current-morph:final))
		(set! current-morph (morph-from final))
		(set! current-morph:progress 0.0)
		(when (equal? final current-morph:final)
		  (set! now-playing? #f)))
	      now-playing?)
	     (else
	      (set! current-morph:progress new-progress)
	      #t))))))
  
  (define (rewind!)::void
    (WARN "rewind!")
    #;(set! current-morph (morph-from initial-expression)))
  
  (define (back!)::void
    (WARN "back!")
    (set! playing-backwards? #t)
    (set! now-playing? #f)
    (let ((painter ::Painter (the-painter)))
      (painter:play! (this))))

  (define (play!)::void
    (WARN "play!")
    (set! now-playing? #t)
    (set! playing-backwards? #f)
    (let ((painter ::Painter (the-painter)))
      (painter:play! (this))))
  
  (define (pause!)::void
    (set! now-playing? #f))
  
  (define (next!)::void
    (WARN "next!")
    (set! playing-backwards? #f)
    (set! now-playing? #f)
    (let ((painter ::Painter (the-painter)))
      (painter:play! (this))))
      
  (define (fast-forward!)::void
    (WARN "fast-forward!")
    ;; to zasadniczo nie wiemy, jak zaimplementowac
    (values))

  (define now-playing? ::boolean #f)
  
  (define (playing?)::boolean now-playing?)

  (define (draw! context::Cursor)::void
    (current-morph:draw! context))

  (define (as-expression)::cons
    (cons (Atom "Stepper") (cons initial-expression '())))

  (define max-extent ::Extent
    (current-morph:extent))
  
  (define (extent)::Extent
    (let ((current ::Extent (current-morph:extent)))
      (set! max-extent:width (max max-extent:width current:width))
      (set! max-extent:height (max max-extent:height current:height))
      max-extent))
      

  (define (cursor-under* x::real y::real path::Cursor)::Cursor*
    #!null)
  
  (Magic))

(define (PlayerWithControls player::Player)::Enchanted
  (Below
   top: player
   bottom:
   (Beside
    left:
    (Beside left: (Button label: "▮◀◀"
			  action: (lambda () (player:rewind!)))
	    right: (Button label: "▮◀ "
			   action: (lambda () (player:back!))))
    right:
    (Beside
     left: (Button label: " ▶ "
		   action: (lambda () (player:play!)))
     right:
     (Beside left: (Button label: " ▶▮"
			   action: (lambda () (player:next!)))
	     right: (Button label: "▶▶▮"
			    action: (lambda ()
				      (player:fast-forward!))))))))

(set! (extension 'Stepper)
      (object (Extension)
	((enchant source::cons)::Enchanted
	 (WARN "invoking stepper")
	 (otherwise (begin
		      (WARN "Unable to create Stepper from "source)
		      #!null)
	   (parameterize ((cell-access-mode CellAccessMode:Editing))
	     (and-let* ((`(Stepper ,expression) source))
	       (PlayerWithControls (Stepper expression))))))))