(import (define-parameter))
(import (keyword-arguments))
(import (functions))
(import (fundamental))
(import (indexable))
(import (space))
(import (cursor))
(import (primitive))
(import (document-operations))
(import (infix))
(import (match))
(import (print))
(import (extent))
(import (painter))
(import (history))
(import (text))

(define-parameter (cursor-column)::real 0)

(define (move-cursor-right!)
  (set! (the-cursor) (cursor-advance))
  (let* ((painter (the-painter))
	 (cursor-position ::Position (painter:cursor-position)))
    (set! (cursor-column) cursor-position:left))
  (set! (the-selection-anchor) (the-cursor)))

(define (move-cursor-left!)
  (set! (the-cursor) (cursor-retreat))
  (let* ((painter (the-painter))
	 (cursor-position ::Position (painter:cursor-position)))
    (set! (cursor-column) cursor-position:left))
  (set! (the-selection-anchor) (the-cursor)))

(define (unnest-cursor-right!)
  (and-let* ((`(,tip ,top . ,root) (the-cursor))
	     (parent ::Indexable (the-expression at: root))
	     (target ::Indexable (parent:part-at top))
	     (item ::Indexable (target:part-at tip)))
    ;;(assert (eq? target item))
    (set! (the-cursor)
	  (cond
	   ((Textual? item)
	    (recons (parent:last-index) root))
	   ((eqv? tip (parent:last-index))
	    (recons (parent:last-index) root))
	   (else
	    (recons* (parent:last-index) top root))))
    (set! (the-selection-anchor) (the-cursor))))

(define (expand-selection-right!)
  (set! (the-cursor) (cursor-advance))
  (let* ((painter (the-painter))
	 (cursor-position ::Position (painter:cursor-position)))
    (set! (cursor-column) cursor-position:left)))

(define (expand-selection-left!)
  (set! (the-cursor) (cursor-retreat))
  (let* ((painter (the-painter))
	 (cursor-position ::Position (painter:cursor-position)))
    (set! (cursor-column) cursor-position:left)))

(define (move-cursor-up!)
  (let* ((painter (the-painter))
	 (target (the-expression))
	 (initial-position ::Position (painter:cursor-position))
	 (cursor-height (painter:cursor-height))
	 (initial-cursor (the-cursor)))
    (let probe ((attempt 1))
      (let* ((shift (* attempt cursor-height))
	     (cursor (cursor-under (cursor-column)
				  (- initial-position:top
				     shift))))
	(cond ((isnt cursor equal? initial-cursor)
	       (set! (the-cursor) cursor)
	       (set! (the-selection-anchor) cursor))
	      ((is 0 < shift < initial-position:top)
	       (probe (+ attempt 1))))))))

(define (move-cursor-down!)
  (let* ((painter (the-painter))
	 (target (the-expression))
	 (initial-position ::Position (painter:cursor-position))
	 (cursor-height (painter:cursor-height))
	 (document-extent ::Extent (sequence-extent))
	 (initial-cursor (the-cursor)))
    (let probe ((attempt 1))
      (let* ((shift (* attempt cursor-height))
	     (cursor (cursor-under (cursor-column)
				  (+ initial-position:top
				     shift))))
	(cond ((isnt cursor equal? initial-cursor)
	       (set! (the-cursor) cursor)
	       (set! (the-selection-anchor) cursor))
	      ((is 0 < shift < (+ initial-position:top shift)
		   < document-extent:height)
	       (probe (+ attempt 1)))
	      )))))

(define (undo!)
  (let ((document-history ::History (history (the-document))))
    (document-history:undo!)))

(define (redo!)
  (let ((document-history ::History (history (the-document))))
    (document-history:redo!)))

(define-private (perform! operation ::Edit)::boolean
  (let* ((document (the-document))
	 (history ::History (history document)))
    (history:record! operation)
    (and-let* ((new-cursor (operation:apply!)))
      (set! (the-cursor) new-cursor)
      (set! (the-selection-anchor) new-cursor)
      #t)))

(define (delete! position::Index)::void
  (let* ((target (the-expression)))
    (cond
     ((is target Textual?)
      (let ((text ::Textual (as Textual target)))
	(cond ((is 0 <= position < (text:text-length))
	       (text:delete-char! position)
	       (when (= (text:text-length) 0)
		 (extract! at: (cdr (the-cursor)))
		 (set! (the-cursor)
		       (cursor-climb-back
			(recons (- (car (cdr (the-cursor)))
				   1)
				(cdr (cdr (the-cursor))))))
		 (set! (the-selection-anchor) (the-cursor)))))))
     ((is target instance? Space)
      (if (or (is position > (first-index target))
	      (and (is position = (first-index target))
		   (or (and-let* ((`(#\] . ,_) (cursor-advance))))
		       (and-let* ((`(#\[ . ,_) (cursor-retreat)))))))
	  (delete-space! target position))))))

(define (delete-forward!)::void
  (let ((target (the-expression)))
    (cond ((and (pair? target)
		(pair? (the-cursor))
		(eqv? (car (the-cursor)) (first-index target)))
	   (let ((new-cursor (cursor-retreat)))
	     (extract!)
	     (set! (the-cursor) new-cursor)
	     (set! (the-selection-anchor) (the-cursor))))
	  (else
	   (delete! (car (the-cursor)))))))

(define (delete-backward!)::boolean
  (and-let* ((`(,tip ,top . ,root) (the-cursor))
	     (tip ::int (as int tip))
	     (_ (truly (DUMP tip)))
	     (parent ::Indexable (the-expression at: root))
	     (_ (truly (DUMP parent)))
	     (target ::Indexable (parent:part-at top))
	     (_ (truly (DUMP target)))
	     ((eq? target (target:part-at tip)))
	     (first-index ::Index (target:first-index))
	     (_ (truly (DUMP first-index)))
	     (last-index ::Index (target:last-index))
	     (_ (truly (DUMP last-index)))
	     (preceding-cursor (cursor-retreat))
	     (_ (truly (DUMP preceding-cursor)))	     
	     (preceding-element (the-expression at: preceding-cursor))
	     (_ (truly (DUMP preceding-element))))
    (cond
     ((Atom? target)
      (WARN "deleting atom "target)
      (let ((target ::Atom target))
	(cond
	 ((eqv? tip first-index)
	  (set! (the-cursor) (cursor-retreat))
	  (set! (the-selection-anchor) (the-cursor))
	  (delete-backward!))
	 ((is (text-length target) <= 1)
	  (let ((cell (drop (quotient top 2) parent)))
	    ;; the cell will be cut off from the rest
	    ;; of the document after performing Remove
	    (perform! (Remove element: cell
			      at: (recons top root)
			      with-shift: (car preceding-cursor)))))
	 (else
	  (perform!
	   (RemoveCharacter
	    list: (cons (target:char-ref (target:previous-index tip))
			'())))))))
     ((Space? target)
      (let ((target ::Space target))
	(cond
	 ((eqv? tip first-index)
	  (cond
	   ((eq? preceding-element parent)
	    (set! (the-cursor) (cursor-retreat))
	    (set! (the-selection-anchor) (the-cursor))
	    (delete-backward!))
	   ((is (text-length (as Space target)) <= 1)
	    (cond
	     ((Textual? preceding-element)
	      (and-let* ((following-cursor (cursor-advance
					    (recons* last-index
						     top root)))
			 (following-element (the-expression
					     at: following-cursor))
			 ((Textual? following-element))
			 ((eq? (preceding-element:getClass)
			       (following-element:getClass))))
		(perform! (MergeElements removing: target))))
	     ((and (eq? preceding-element parent)
		   (is (text-length (as Space target)) = 1))
	      (perform! (RemoveCharacter
			 list: (cons (target:char-ref tip) '()))))
	     (else #f)))
	   (else
	    (perform! (RemoveCharacter
		       list: (cons (target:char-ref tip)
				   '())))))))))
     ((Text? target)
      (let ((target ::Text target))
	(cond
	 ((eqv? tip first-index)
	  (set! (the-cursor) (cursor-retreat))
	  (set! (the-selection-anchor) (the-cursor))
	  (delete-backward!))
	 ((is (text-length (as Text target)) <= 0)
	  (let ((cell (drop (quotient top 2) parent)))
	    ;; the cell will be cut off from the rest
	    ;; of the document after performing Remove
	    (perform! (Remove element: cell
			      with-shift: (text-length
					   preceding-element)))))
	 (else
	  (perform! (RemoveCharacter list: (cons (target:char-ref tip)
						 '())))))))
     ((gnu.lists.LList? target)
      (let ((cell (drop (quotient top 2) parent)))
	(if (or (eqv? tip last-index)
		(null? target)
		(and-let* ((empty ::EmptyListProxy target)
			   ((is empty:space EmptySpace?)))))
	    (perform! (Remove element: cell
			      with-shift: (text-length
					   preceding-element)))
	    #f
	    )))
     (else
      #f))))
      
#;(define (delete-backward!)::void
  (let ((target (the-expression)))
    (cond ((and (pair? target)
		(eqv? (car (the-cursor)) (last-index target)))
	   (let ((new-cursor (cursor-climb-back
			      (cursor-back (cdr (the-cursor))))))
	     (extract!)
	     (set! (the-cursor) new-cursor)
	     (set! (the-selection-anchor) (the-cursor))))
	  (else
	   (set! (the-cursor)
		 (cursor-climb-back (cursor-back)))
	   (set! (the-selection-anchor) (the-cursor))
	   (delete! (car (the-cursor)))))))

(define/kw (insert-character! c::char)
  ::boolean
  ;; musimy pamietac ze dzialana dokonywane poprzez
  ;;te funkcje powinno sie dac cofac za pomoca "undo!"
  (and-let* (((isnt c eqv? #\null))
	     (`(,tip ,top . ,subcursor) (the-cursor))
	     (parent ::Indexable (the-expression at: subcursor))
	     (item ::Indexable (parent:part-at top))
	     (final ::Indexable (item:part-at tip)))
    (cond
     ((isnt final eq? item)
      (WARN "attempted to insert character "c" to non-final position")
      #f)
     ((Text? item)
      (perform! (InsertCharacter list: (list c))))

     ((is c in '(#\] #\) #\}))
      (unnest-cursor-right!))
      
     ((gnu.lists.LList? item)
      (set! (the-cursor) (cursor-advance))
      (set! (the-selection-anchor) (the-cursor))
      (insert-character! c))
     
     ((Space? item)
      (cond
       ((eqv? c #\")
	(perform! (Insert element: (cons (Text) '()))))
       
       ((is c in '(#\[ #\( #\{))
	(perform! (Insert element: (cons (EmptyListProxy (EmptySpace))
					 '()))))
       ((is c char-whitespace?)
	(perform! (InsertCharacter list: (list c))))
       
       ((and-let* (((is tip eqv? (item:last-index)))
		   (next-cursor (cursor-advance))
		   (next-target (the-expression at: next-cursor))
		   ((Atom? next-target)))
	  (perform! (InsertCharacter list: (list c)
				     after: next-cursor))))

       ((and-let* (((is tip eqv? (item:first-index)))
		   (previous-cursor (cursor-retreat))
		   (previous-target (the-expression
				     at: previous-cursor))
		   ((Atom? previous-target)))
	  (perform! (InsertCharacter list: (list c)
				     after: previous-cursor))))
       (else
	(perform! (Insert element: (cons (Atom (string c)) '()))))))
     ((Atom? item)
      (cond
       ((is c char-whitespace?)
	(cond
	 ((eqv? (final:first-index) tip)
	  (perform! (InsertCharacter list: (list c)
				     after: (cursor-retreat))))
	 ((eqv? (final:last-index) tip)
	  (perform! (InsertCharacter list: (list c)
				     after: (cursor-advance))))
	 (else
	  (perform! (SplitElement with: (SpaceFrom c))))))
       
       ((is c in '(#\[ #\( #\{))
	(cond
	 ((eqv? (final:first-index) tip)
	  (perform! (Insert element: (cons (EmptyListProxy
					    (EmptySpace)) '())
			    at: (cursor-retreat))))
	 ((eqv? (final:last-index) tip)
	  (perform! (Insert element: (cons (EmptyListProxy
					    (EmptySpace)) '())
			    at: (cursor-advance))))
	 (else
	  (perform! (SplitElement with: (EmptySpace)))
	  (perform! (Insert element: (cons (EmptyListProxy
					    (EmptySpace)) '()))))))
       (else
	(perform! (InsertCharacter list: (list c))))))
     ((Text? item)
      (InsertCharacter list: (list c)))
	 
     (else
      (WARN "Don't know how to insert character "c" into "item)
      #f
      ))))
