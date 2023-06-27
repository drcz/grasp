(import (define-type))
(import (define-object))
(import (define-parameter))
(import (define-property))
(import (infix))
(import (match))
(import (srfi :11))
(import (functions))
(import (fundamental))
(import (indexable))
(import (space))
(import (primitive))
(import (define-cache))
(import (conversions))
(import (parse))
(import (print))

(define-object (Document car ::Object source ::java.io.File)::Tile
  ;; TODO: cursor-under* etc.

  (define (draw! context::Cursor)::void
    (cond ((EmptyListProxy? car)
	   (let ((proxy ::EmptyListProxy (as EmptyListProxy car)))
	     (proxy:space:draw! (hash-cons 0 context))))
	  ((pair? car)
	   (let ((s ::Space (pre-head-space car)))
	     (s:draw! (hash-cons 0 context))
	     (draw-sequence! car)))))
  (cons car (empty)))

(define-parameter (open-documents)::(list-of Document)
  '())

(define (open-document source::java.io.File)::Document
  (or (find (lambda (document::Document)
	      ::boolean
	      (eq? document:source source))
	    (open-documents))
      (call-with-input-file (source:getAbsolutePath)
	(lambda (port)
	  (Document (parse port) source)))))

(define (draw-document! document::pair)
  (cond ((EmptyListProxy? (head document))
	 (let ((proxy (as EmptyListProxy (head document))))
	   (draw! proxy:space)))
	((pair? (head document))
	 (draw! (pre-head-space (head document)))
	 (draw-sequence! (head document)))))